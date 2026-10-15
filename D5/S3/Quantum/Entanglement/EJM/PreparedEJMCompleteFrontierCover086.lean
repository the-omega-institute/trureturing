/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover085
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_08259 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91500) = some ⟨13, 1, 0, 3444, 91500, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91500_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91500 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91500 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91500, 1, 16384⟩
    (by decide) selected_cut_08259

theorem selected_cut_08260 : selected 8 ⟨232482, by decide⟩
    (prefixPartial 13 91501) = some ⟨13, 2, 0, 232482, 91501, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_91501_232482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91501 ⟨232482, by decide⟩ :=
  accepted_of_selected 13 91501 ⟨232482, by decide⟩ ⟨13, 2, 0, 232482, 91501, 1733, 16384⟩
    (by decide) selected_cut_08260

theorem selected_cut_08261 : selected 8 ⟨232512, by decide⟩
    (prefixPartial 13 91502) = some ⟨13, 2, 0, 232512, 91502, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_91502_232512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91502 ⟨232512, by decide⟩ :=
  accepted_of_selected 13 91502 ⟨232512, by decide⟩ ⟨13, 2, 0, 232512, 91502, 2537, 16384⟩
    (by decide) selected_cut_08261

theorem selected_cut_08262 : selected 8 ⟨232524, by decide⟩
    (prefixPartial 13 91503) = some ⟨13, 2, 0, 232524, 91503, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_91503_232524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91503 ⟨232524, by decide⟩ :=
  accepted_of_selected 13 91503 ⟨232524, by decide⟩ ⟨13, 2, 0, 232524, 91503, 1041, 16384⟩
    (by decide) selected_cut_08262

theorem unmarked_context_12_22875_232525 : frontier 9 ⟨232525, by decide⟩
    (prefixCache 12 22875) (prefixPartial 12 22875) = false := by
  decide +kernel

theorem node_context_12_22875_232525 : EJMOriginalGlobalDAGData.nodes 9 ⟨232525, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232482, by decide⟩,⟨232512, by decide⟩,⟨232524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22875_232525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22875 ⟨232525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22875
    ⟨232525, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232482, by decide⟩,⟨232512, by decide⟩,⟨232524, by decide⟩]) unmarked_context_12_22875_232525 node_context_12_22875_232525
  intro a
  fin_cases a
  · exact context_13_91500_3444
  · exact context_13_91501_232482
  · exact context_13_91502_232512
  · exact context_13_91503_232524

theorem unmarked_context_11_5718_232526 : frontier 10 ⟨232526, by decide⟩
    (prefixCache 11 5718) (prefixPartial 11 5718) = false := by
  decide +kernel

theorem node_context_11_5718_232526 : EJMOriginalGlobalDAGData.nodes 10 ⟨232526, by decide⟩ =
    .split (coordinate 11) (![⟨232347, by decide⟩,⟨232410, by decide⟩,⟨232465, by decide⟩,⟨232525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5718_232526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5718 ⟨232526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5718
    ⟨232526, by decide⟩ (by decide) (![⟨232347, by decide⟩,⟨232410, by decide⟩,⟨232465, by decide⟩,⟨232525, by decide⟩]) unmarked_context_11_5718_232526 node_context_11_5718_232526
  intro a
  fin_cases a
  · exact context_12_22872_232347
  · exact context_12_22873_232410
  · exact context_12_22874_232465
  · exact context_12_22875_232525

theorem selected_cut_08263 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91504) = some ⟨13, 1, 0, 3444, 91504, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91504_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91504 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91504 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91504, 1, 16384⟩
    (by decide) selected_cut_08263

theorem selected_cut_08264 : selected 8 ⟨232544, by decide⟩
    (prefixPartial 13 91505) = some ⟨13, 2, 0, 232544, 91505, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_91505_232544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91505 ⟨232544, by decide⟩ :=
  accepted_of_selected 13 91505 ⟨232544, by decide⟩ ⟨13, 2, 0, 232544, 91505, 1425, 16384⟩
    (by decide) selected_cut_08264

theorem selected_cut_08265 : selected 8 ⟨232561, by decide⟩
    (prefixPartial 13 91506) = some ⟨13, 2, 0, 232561, 91506, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_91506_232561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91506 ⟨232561, by decide⟩ :=
  accepted_of_selected 13 91506 ⟨232561, by decide⟩ ⟨13, 2, 0, 232561, 91506, 1609, 16384⟩
    (by decide) selected_cut_08265

theorem selected_cut_08266 : selected 8 ⟨232574, by decide⟩
    (prefixPartial 13 91507) = some ⟨13, 2, 0, 232574, 91507, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_91507_232574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91507 ⟨232574, by decide⟩ :=
  accepted_of_selected 13 91507 ⟨232574, by decide⟩ ⟨13, 2, 0, 232574, 91507, 1073, 16384⟩
    (by decide) selected_cut_08266

theorem unmarked_context_12_22876_232575 : frontier 9 ⟨232575, by decide⟩
    (prefixCache 12 22876) (prefixPartial 12 22876) = false := by
  decide +kernel

theorem node_context_12_22876_232575 : EJMOriginalGlobalDAGData.nodes 9 ⟨232575, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232544, by decide⟩,⟨232561, by decide⟩,⟨232574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22876_232575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22876 ⟨232575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22876
    ⟨232575, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232544, by decide⟩,⟨232561, by decide⟩,⟨232574, by decide⟩]) unmarked_context_12_22876_232575 node_context_12_22876_232575
  intro a
  fin_cases a
  · exact context_13_91504_3444
  · exact context_13_91505_232544
  · exact context_13_91506_232561
  · exact context_13_91507_232574

theorem selected_cut_08267 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91508) = some ⟨13, 1, 0, 3444, 91508, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91508_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91508 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91508 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91508, 1, 16384⟩
    (by decide) selected_cut_08267

theorem selected_cut_08268 : selected 8 ⟨232602, by decide⟩
    (prefixPartial 13 91509) = some ⟨13, 2, 0, 232602, 91509, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_91509_232602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91509 ⟨232602, by decide⟩ :=
  accepted_of_selected 13 91509 ⟨232602, by decide⟩ ⟨13, 2, 0, 232602, 91509, 1733, 16384⟩
    (by decide) selected_cut_08268

theorem selected_cut_08269 : selected 8 ⟨232623, by decide⟩
    (prefixPartial 13 91510) = some ⟨13, 2, 0, 232623, 91510, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_91510_232623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91510 ⟨232623, by decide⟩ :=
  accepted_of_selected 13 91510 ⟨232623, by decide⟩ ⟨13, 2, 0, 232623, 91510, 2065, 16384⟩
    (by decide) selected_cut_08269

theorem selected_cut_08270 : selected 8 ⟨232631, by decide⟩
    (prefixPartial 13 91511) = some ⟨13, 2, 0, 232631, 91511, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_91511_232631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91511 ⟨232631, by decide⟩ :=
  accepted_of_selected 13 91511 ⟨232631, by decide⟩ ⟨13, 2, 0, 232631, 91511, 1141, 16384⟩
    (by decide) selected_cut_08270

theorem unmarked_context_12_22877_232632 : frontier 9 ⟨232632, by decide⟩
    (prefixCache 12 22877) (prefixPartial 12 22877) = false := by
  decide +kernel

theorem node_context_12_22877_232632 : EJMOriginalGlobalDAGData.nodes 9 ⟨232632, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232602, by decide⟩,⟨232623, by decide⟩,⟨232631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22877_232632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22877 ⟨232632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22877
    ⟨232632, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232602, by decide⟩,⟨232623, by decide⟩,⟨232631, by decide⟩]) unmarked_context_12_22877_232632 node_context_12_22877_232632
  intro a
  fin_cases a
  · exact context_13_91508_3444
  · exact context_13_91509_232602
  · exact context_13_91510_232623
  · exact context_13_91511_232631

theorem selected_cut_08271 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91512) = some ⟨13, 1, 0, 3444, 91512, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91512_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91512 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91512 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91512, 1, 16384⟩
    (by decide) selected_cut_08271

theorem selected_cut_08272 : selected 8 ⟨232655, by decide⟩
    (prefixPartial 13 91513) = some ⟨13, 2, 0, 232655, 91513, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_91513_232655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91513 ⟨232655, by decide⟩ :=
  accepted_of_selected 13 91513 ⟨232655, by decide⟩ ⟨13, 2, 0, 232655, 91513, 1717, 16384⟩
    (by decide) selected_cut_08272

theorem selected_cut_08273 : selected 8 ⟨232674, by decide⟩
    (prefixPartial 13 91514) = some ⟨13, 2, 0, 232674, 91514, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_91514_232674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91514 ⟨232674, by decide⟩ :=
  accepted_of_selected 13 91514 ⟨232674, by decide⟩ ⟨13, 2, 0, 232674, 91514, 2141, 16384⟩
    (by decide) selected_cut_08273

theorem selected_cut_08274 : selected 8 ⟨232683, by decide⟩
    (prefixPartial 13 91515) = some ⟨13, 2, 0, 232683, 91515, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_91515_232683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91515 ⟨232683, by decide⟩ :=
  accepted_of_selected 13 91515 ⟨232683, by decide⟩ ⟨13, 2, 0, 232683, 91515, 1097, 16384⟩
    (by decide) selected_cut_08274

theorem unmarked_context_12_22878_232684 : frontier 9 ⟨232684, by decide⟩
    (prefixCache 12 22878) (prefixPartial 12 22878) = false := by
  decide +kernel

theorem node_context_12_22878_232684 : EJMOriginalGlobalDAGData.nodes 9 ⟨232684, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232655, by decide⟩,⟨232674, by decide⟩,⟨232683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22878_232684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22878 ⟨232684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22878
    ⟨232684, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232655, by decide⟩,⟨232674, by decide⟩,⟨232683, by decide⟩]) unmarked_context_12_22878_232684 node_context_12_22878_232684
  intro a
  fin_cases a
  · exact context_13_91512_3444
  · exact context_13_91513_232655
  · exact context_13_91514_232674
  · exact context_13_91515_232683

theorem selected_cut_08275 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91516) = some ⟨13, 1, 0, 3444, 91516, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91516_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91516 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91516 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91516, 1, 16384⟩
    (by decide) selected_cut_08275

theorem selected_cut_08276 : selected 8 ⟨232701, by decide⟩
    (prefixPartial 13 91517) = some ⟨13, 2, 0, 232701, 91517, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_91517_232701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91517 ⟨232701, by decide⟩ :=
  accepted_of_selected 13 91517 ⟨232701, by decide⟩ ⟨13, 2, 0, 232701, 91517, 1621, 16384⟩
    (by decide) selected_cut_08276

theorem selected_cut_08277 : selected 8 ⟨232719, by decide⟩
    (prefixPartial 13 91518) = some ⟨13, 2, 0, 232719, 91518, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_91518_232719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91518 ⟨232719, by decide⟩ :=
  accepted_of_selected 13 91518 ⟨232719, by decide⟩ ⟨13, 2, 0, 232719, 91518, 2109, 16384⟩
    (by decide) selected_cut_08277

theorem selected_cut_08278 : selected 8 ⟨232724, by decide⟩
    (prefixPartial 13 91519) = some ⟨13, 2, 0, 232724, 91519, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_91519_232724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91519 ⟨232724, by decide⟩ :=
  accepted_of_selected 13 91519 ⟨232724, by decide⟩ ⟨13, 2, 0, 232724, 91519, 1101, 16384⟩
    (by decide) selected_cut_08278

theorem unmarked_context_12_22879_232725 : frontier 9 ⟨232725, by decide⟩
    (prefixCache 12 22879) (prefixPartial 12 22879) = false := by
  decide +kernel

theorem node_context_12_22879_232725 : EJMOriginalGlobalDAGData.nodes 9 ⟨232725, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232701, by decide⟩,⟨232719, by decide⟩,⟨232724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22879_232725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22879 ⟨232725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22879
    ⟨232725, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232701, by decide⟩,⟨232719, by decide⟩,⟨232724, by decide⟩]) unmarked_context_12_22879_232725 node_context_12_22879_232725
  intro a
  fin_cases a
  · exact context_13_91516_3444
  · exact context_13_91517_232701
  · exact context_13_91518_232719
  · exact context_13_91519_232724

theorem unmarked_context_11_5719_232726 : frontier 10 ⟨232726, by decide⟩
    (prefixCache 11 5719) (prefixPartial 11 5719) = false := by
  decide +kernel

theorem node_context_11_5719_232726 : EJMOriginalGlobalDAGData.nodes 10 ⟨232726, by decide⟩ =
    .split (coordinate 11) (![⟨232575, by decide⟩,⟨232632, by decide⟩,⟨232684, by decide⟩,⟨232725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5719_232726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5719 ⟨232726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5719
    ⟨232726, by decide⟩ (by decide) (![⟨232575, by decide⟩,⟨232632, by decide⟩,⟨232684, by decide⟩,⟨232725, by decide⟩]) unmarked_context_11_5719_232726 node_context_11_5719_232726
  intro a
  fin_cases a
  · exact context_12_22876_232575
  · exact context_12_22877_232632
  · exact context_12_22878_232684
  · exact context_12_22879_232725

theorem unmarked_context_10_1429_232727 : frontier 11 ⟨232727, by decide⟩
    (prefixCache 10 1429) (prefixPartial 10 1429) = false := by
  decide +kernel

theorem node_context_10_1429_232727 : EJMOriginalGlobalDAGData.nodes 11 ⟨232727, by decide⟩ =
    .split (coordinate 10) (![⟨232157, by decide⟩,⟨232298, by decide⟩,⟨232526, by decide⟩,⟨232726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1429_232727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1429 ⟨232727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1429
    ⟨232727, by decide⟩ (by decide) (![⟨232157, by decide⟩,⟨232298, by decide⟩,⟨232526, by decide⟩,⟨232726, by decide⟩]) unmarked_context_10_1429_232727 node_context_10_1429_232727
  intro a
  fin_cases a
  · exact context_11_5716_232157
  · exact context_11_5717_232298
  · exact context_11_5718_232526
  · exact context_11_5719_232726

theorem selected_cut_08279 : selected 9 ⟨232766, by decide⟩
    (prefixPartial 12 22880) = some ⟨12, 2, 0, 232766, 22880, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_22880_232766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22880 ⟨232766, by decide⟩ :=
  accepted_of_selected 12 22880 ⟨232766, by decide⟩ ⟨12, 2, 0, 232766, 22880, 3917, 65536⟩
    (by decide) selected_cut_08279

theorem selected_cut_08280 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91524) = some ⟨13, 1, 0, 3444, 91524, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91524_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91524 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91524 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91524, 1, 16384⟩
    (by decide) selected_cut_08280

theorem selected_cut_08281 : selected 8 ⟨232787, by decide⟩
    (prefixPartial 13 91525) = some ⟨13, 2, 0, 232787, 91525, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_91525_232787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91525 ⟨232787, by decide⟩ :=
  accepted_of_selected 13 91525 ⟨232787, by decide⟩ ⟨13, 2, 0, 232787, 91525, 1725, 16384⟩
    (by decide) selected_cut_08281

theorem selected_cut_08282 : selected 8 ⟨232808, by decide⟩
    (prefixPartial 13 91526) = some ⟨13, 2, 0, 232808, 91526, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_91526_232808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91526 ⟨232808, by decide⟩ :=
  accepted_of_selected 13 91526 ⟨232808, by decide⟩ ⟨13, 2, 0, 232808, 91526, 2001, 16384⟩
    (by decide) selected_cut_08282

theorem selected_cut_08283 : selected 8 ⟨232816, by decide⟩
    (prefixPartial 13 91527) = some ⟨13, 2, 0, 232816, 91527, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_91527_232816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91527 ⟨232816, by decide⟩ :=
  accepted_of_selected 13 91527 ⟨232816, by decide⟩ ⟨13, 2, 0, 232816, 91527, 1173, 16384⟩
    (by decide) selected_cut_08283

theorem unmarked_context_12_22881_232817 : frontier 9 ⟨232817, by decide⟩
    (prefixCache 12 22881) (prefixPartial 12 22881) = false := by
  decide +kernel

theorem node_context_12_22881_232817 : EJMOriginalGlobalDAGData.nodes 9 ⟨232817, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232787, by decide⟩,⟨232808, by decide⟩,⟨232816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22881_232817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22881 ⟨232817, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22881
    ⟨232817, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232787, by decide⟩,⟨232808, by decide⟩,⟨232816, by decide⟩]) unmarked_context_12_22881_232817 node_context_12_22881_232817
  intro a
  fin_cases a
  · exact context_13_91524_3444
  · exact context_13_91525_232787
  · exact context_13_91526_232808
  · exact context_13_91527_232816

theorem selected_cut_08284 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91528) = some ⟨13, 1, 0, 3444, 91528, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91528_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91528 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91528 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91528, 1, 16384⟩
    (by decide) selected_cut_08284

theorem selected_cut_08285 : selected 8 ⟨232840, by decide⟩
    (prefixPartial 13 91529) = some ⟨13, 2, 0, 232840, 91529, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_91529_232840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91529 ⟨232840, by decide⟩ :=
  accepted_of_selected 13 91529 ⟨232840, by decide⟩ ⟨13, 2, 0, 232840, 91529, 1689, 16384⟩
    (by decide) selected_cut_08285

theorem selected_cut_08286 : selected 8 ⟨232860, by decide⟩
    (prefixPartial 13 91530) = some ⟨13, 2, 0, 232860, 91530, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_91530_232860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91530 ⟨232860, by decide⟩ :=
  accepted_of_selected 13 91530 ⟨232860, by decide⟩ ⟨13, 2, 0, 232860, 91530, 1897, 16384⟩
    (by decide) selected_cut_08286

theorem selected_cut_08287 : selected 8 ⟨232870, by decide⟩
    (prefixPartial 13 91531) = some ⟨13, 2, 0, 232870, 91531, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_91531_232870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91531 ⟨232870, by decide⟩ :=
  accepted_of_selected 13 91531 ⟨232870, by decide⟩ ⟨13, 2, 0, 232870, 91531, 1057, 16384⟩
    (by decide) selected_cut_08287

theorem unmarked_context_12_22882_232871 : frontier 9 ⟨232871, by decide⟩
    (prefixCache 12 22882) (prefixPartial 12 22882) = false := by
  decide +kernel

theorem node_context_12_22882_232871 : EJMOriginalGlobalDAGData.nodes 9 ⟨232871, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232840, by decide⟩,⟨232860, by decide⟩,⟨232870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22882_232871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22882 ⟨232871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22882
    ⟨232871, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232840, by decide⟩,⟨232860, by decide⟩,⟨232870, by decide⟩]) unmarked_context_12_22882_232871 node_context_12_22882_232871
  intro a
  fin_cases a
  · exact context_13_91528_3444
  · exact context_13_91529_232840
  · exact context_13_91530_232860
  · exact context_13_91531_232870

theorem selected_cut_08288 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91532) = some ⟨13, 1, 0, 3444, 91532, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91532_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91532 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91532 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91532, 1, 16384⟩
    (by decide) selected_cut_08288

theorem selected_cut_08289 : selected 8 ⟨232887, by decide⟩
    (prefixPartial 13 91533) = some ⟨13, 2, 0, 232887, 91533, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_91533_232887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91533 ⟨232887, by decide⟩ :=
  accepted_of_selected 13 91533 ⟨232887, by decide⟩ ⟨13, 2, 0, 232887, 91533, 1505, 16384⟩
    (by decide) selected_cut_08289

theorem selected_cut_08290 : selected 8 ⟨232910, by decide⟩
    (prefixPartial 13 91534) = some ⟨13, 2, 0, 232910, 91534, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_91534_232910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91534 ⟨232910, by decide⟩ :=
  accepted_of_selected 13 91534 ⟨232910, by decide⟩ ⟨13, 2, 0, 232910, 91534, 2069, 16384⟩
    (by decide) selected_cut_08290

theorem selected_cut_08291 : selected 8 ⟨232918, by decide⟩
    (prefixPartial 13 91535) = some ⟨13, 2, 0, 232918, 91535, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_91535_232918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91535 ⟨232918, by decide⟩ :=
  accepted_of_selected 13 91535 ⟨232918, by decide⟩ ⟨13, 2, 0, 232918, 91535, 1077, 16384⟩
    (by decide) selected_cut_08291

theorem unmarked_context_12_22883_232919 : frontier 9 ⟨232919, by decide⟩
    (prefixCache 12 22883) (prefixPartial 12 22883) = false := by
  decide +kernel

theorem node_context_12_22883_232919 : EJMOriginalGlobalDAGData.nodes 9 ⟨232919, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨232887, by decide⟩,⟨232910, by decide⟩,⟨232918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22883_232919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22883 ⟨232919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22883
    ⟨232919, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨232887, by decide⟩,⟨232910, by decide⟩,⟨232918, by decide⟩]) unmarked_context_12_22883_232919 node_context_12_22883_232919
  intro a
  fin_cases a
  · exact context_13_91532_3444
  · exact context_13_91533_232887
  · exact context_13_91534_232910
  · exact context_13_91535_232918

theorem unmarked_context_11_5720_232920 : frontier 10 ⟨232920, by decide⟩
    (prefixCache 11 5720) (prefixPartial 11 5720) = false := by
  decide +kernel

theorem node_context_11_5720_232920 : EJMOriginalGlobalDAGData.nodes 10 ⟨232920, by decide⟩ =
    .split (coordinate 11) (![⟨232766, by decide⟩,⟨232817, by decide⟩,⟨232871, by decide⟩,⟨232919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5720_232920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5720 ⟨232920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5720
    ⟨232920, by decide⟩ (by decide) (![⟨232766, by decide⟩,⟨232817, by decide⟩,⟨232871, by decide⟩,⟨232919, by decide⟩]) unmarked_context_11_5720_232920 node_context_11_5720_232920
  intro a
  fin_cases a
  · exact context_12_22880_232766
  · exact context_12_22881_232817
  · exact context_12_22882_232871
  · exact context_12_22883_232919

theorem selected_cut_08292 : selected 9 ⟨232955, by decide⟩
    (prefixPartial 12 22884) = some ⟨12, 2, 0, 232955, 22884, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_22884_232955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22884 ⟨232955, by decide⟩ :=
  accepted_of_selected 12 22884 ⟨232955, by decide⟩ ⟨12, 2, 0, 232955, 22884, 3157, 65536⟩
    (by decide) selected_cut_08292

theorem selected_cut_08293 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 22885) = some ⟨12, 1, 0, 126884, 22885, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22885_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22885 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 22885 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 22885, 1, 65536⟩
    (by decide) selected_cut_08293

theorem selected_cut_08294 : selected 9 ⟨232994, by decide⟩
    (prefixPartial 12 22886) = some ⟨12, 2, 0, 232994, 22886, 3645, 65536⟩ := by
  decide +kernel

theorem context_12_22886_232994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22886 ⟨232994, by decide⟩ :=
  accepted_of_selected 12 22886 ⟨232994, by decide⟩ ⟨12, 2, 0, 232994, 22886, 3645, 65536⟩
    (by decide) selected_cut_08294

theorem selected_cut_08295 : selected 9 ⟨233036, by decide⟩
    (prefixPartial 12 22887) = some ⟨12, 2, 0, 233036, 22887, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_22887_233036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22887 ⟨233036, by decide⟩ :=
  accepted_of_selected 12 22887 ⟨233036, by decide⟩ ⟨12, 2, 0, 233036, 22887, 3797, 65536⟩
    (by decide) selected_cut_08295

theorem unmarked_context_11_5721_233037 : frontier 10 ⟨233037, by decide⟩
    (prefixCache 11 5721) (prefixPartial 11 5721) = false := by
  decide +kernel

theorem node_context_11_5721_233037 : EJMOriginalGlobalDAGData.nodes 10 ⟨233037, by decide⟩ =
    .split (coordinate 11) (![⟨232955, by decide⟩,⟨126884, by decide⟩,⟨232994, by decide⟩,⟨233036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5721_233037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5721 ⟨233037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5721
    ⟨233037, by decide⟩ (by decide) (![⟨232955, by decide⟩,⟨126884, by decide⟩,⟨232994, by decide⟩,⟨233036, by decide⟩]) unmarked_context_11_5721_233037 node_context_11_5721_233037
  intro a
  fin_cases a
  · exact context_12_22884_232955
  · exact context_12_22885_126884
  · exact context_12_22886_232994
  · exact context_12_22887_233036

theorem selected_cut_08296 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91552) = some ⟨13, 1, 0, 3444, 91552, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91552_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91552 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91552 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91552, 1, 16384⟩
    (by decide) selected_cut_08296

theorem selected_cut_08297 : selected 8 ⟨233053, by decide⟩
    (prefixPartial 13 91553) = some ⟨13, 2, 0, 233053, 91553, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_91553_233053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91553 ⟨233053, by decide⟩ :=
  accepted_of_selected 13 91553 ⟨233053, by decide⟩ ⟨13, 2, 0, 233053, 91553, 1285, 16384⟩
    (by decide) selected_cut_08297

theorem selected_cut_08298 : selected 8 ⟨233079, by decide⟩
    (prefixPartial 13 91554) = some ⟨13, 2, 0, 233079, 91554, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_91554_233079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91554 ⟨233079, by decide⟩ :=
  accepted_of_selected 13 91554 ⟨233079, by decide⟩ ⟨13, 2, 0, 233079, 91554, 2165, 16384⟩
    (by decide) selected_cut_08298

theorem selected_cut_08299 : selected 8 ⟨233093, by decide⟩
    (prefixPartial 13 91555) = some ⟨13, 2, 0, 233093, 91555, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_91555_233093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91555 ⟨233093, by decide⟩ :=
  accepted_of_selected 13 91555 ⟨233093, by decide⟩ ⟨13, 2, 0, 233093, 91555, 1181, 16384⟩
    (by decide) selected_cut_08299

theorem unmarked_context_12_22888_233094 : frontier 9 ⟨233094, by decide⟩
    (prefixCache 12 22888) (prefixPartial 12 22888) = false := by
  decide +kernel

theorem node_context_12_22888_233094 : EJMOriginalGlobalDAGData.nodes 9 ⟨233094, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233053, by decide⟩,⟨233079, by decide⟩,⟨233093, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22888_233094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22888 ⟨233094, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22888
    ⟨233094, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233053, by decide⟩,⟨233079, by decide⟩,⟨233093, by decide⟩]) unmarked_context_12_22888_233094 node_context_12_22888_233094
  intro a
  fin_cases a
  · exact context_13_91552_3444
  · exact context_13_91553_233053
  · exact context_13_91554_233079
  · exact context_13_91555_233093

theorem selected_cut_08300 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91556) = some ⟨13, 1, 0, 3444, 91556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91556, 1, 16384⟩
    (by decide) selected_cut_08300

theorem selected_cut_08301 : selected 8 ⟨233127, by decide⟩
    (prefixPartial 13 91557) = some ⟨13, 2, 0, 233127, 91557, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_91557_233127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91557 ⟨233127, by decide⟩ :=
  accepted_of_selected 13 91557 ⟨233127, by decide⟩ ⟨13, 2, 0, 233127, 91557, 1853, 16384⟩
    (by decide) selected_cut_08301

theorem selected_cut_08302 : selected 8 ⟨233166, by decide⟩
    (prefixPartial 13 91558) = some ⟨13, 2, 0, 233166, 91558, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_91558_233166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91558 ⟨233166, by decide⟩ :=
  accepted_of_selected 13 91558 ⟨233166, by decide⟩ ⟨13, 2, 0, 233166, 91558, 2761, 16384⟩
    (by decide) selected_cut_08302

theorem selected_cut_08303 : selected 8 ⟨233194, by decide⟩
    (prefixPartial 13 91559) = some ⟨13, 2, 0, 233194, 91559, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_91559_233194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91559 ⟨233194, by decide⟩ :=
  accepted_of_selected 13 91559 ⟨233194, by decide⟩ ⟨13, 2, 0, 233194, 91559, 1609, 16384⟩
    (by decide) selected_cut_08303

theorem unmarked_context_12_22889_233195 : frontier 9 ⟨233195, by decide⟩
    (prefixCache 12 22889) (prefixPartial 12 22889) = false := by
  decide +kernel

theorem node_context_12_22889_233195 : EJMOriginalGlobalDAGData.nodes 9 ⟨233195, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233127, by decide⟩,⟨233166, by decide⟩,⟨233194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22889_233195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22889 ⟨233195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22889
    ⟨233195, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233127, by decide⟩,⟨233166, by decide⟩,⟨233194, by decide⟩]) unmarked_context_12_22889_233195 node_context_12_22889_233195
  intro a
  fin_cases a
  · exact context_13_91556_3444
  · exact context_13_91557_233127
  · exact context_13_91558_233166
  · exact context_13_91559_233194

theorem selected_cut_08304 : selected 9 ⟨233296, by decide⟩
    (prefixPartial 12 22890) = some ⟨12, 2, 0, 233296, 22890, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_22890_233296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22890 ⟨233296, by decide⟩ :=
  accepted_of_selected 12 22890 ⟨233296, by decide⟩ ⟨12, 2, 0, 233296, 22890, 2089, 65536⟩
    (by decide) selected_cut_08304

theorem selected_cut_08305 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91564) = some ⟨13, 1, 0, 3444, 91564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91564, 1, 16384⟩
    (by decide) selected_cut_08305

theorem selected_cut_08306 : selected 8 ⟨233322, by decide⟩
    (prefixPartial 13 91565) = some ⟨13, 2, 0, 233322, 91565, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_91565_233322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91565 ⟨233322, by decide⟩ :=
  accepted_of_selected 13 91565 ⟨233322, by decide⟩ ⟨13, 2, 0, 233322, 91565, 1397, 16384⟩
    (by decide) selected_cut_08306

theorem selected_cut_08307 : selected 8 ⟨233354, by decide⟩
    (prefixPartial 13 91566) = some ⟨13, 2, 0, 233354, 91566, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_91566_233354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91566 ⟨233354, by decide⟩ :=
  accepted_of_selected 13 91566 ⟨233354, by decide⟩ ⟨13, 2, 0, 233354, 91566, 2729, 16384⟩
    (by decide) selected_cut_08307

theorem selected_cut_08308 : selected 8 ⟨233363, by decide⟩
    (prefixPartial 13 91567) = some ⟨13, 2, 0, 233363, 91567, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_91567_233363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91567 ⟨233363, by decide⟩ :=
  accepted_of_selected 13 91567 ⟨233363, by decide⟩ ⟨13, 2, 0, 233363, 91567, 1265, 16384⟩
    (by decide) selected_cut_08308

theorem unmarked_context_12_22891_233364 : frontier 9 ⟨233364, by decide⟩
    (prefixCache 12 22891) (prefixPartial 12 22891) = false := by
  decide +kernel

theorem node_context_12_22891_233364 : EJMOriginalGlobalDAGData.nodes 9 ⟨233364, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233322, by decide⟩,⟨233354, by decide⟩,⟨233363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22891_233364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22891 ⟨233364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22891
    ⟨233364, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233322, by decide⟩,⟨233354, by decide⟩,⟨233363, by decide⟩]) unmarked_context_12_22891_233364 node_context_12_22891_233364
  intro a
  fin_cases a
  · exact context_13_91564_3444
  · exact context_13_91565_233322
  · exact context_13_91566_233354
  · exact context_13_91567_233363

theorem unmarked_context_11_5722_233365 : frontier 10 ⟨233365, by decide⟩
    (prefixCache 11 5722) (prefixPartial 11 5722) = false := by
  decide +kernel

theorem node_context_11_5722_233365 : EJMOriginalGlobalDAGData.nodes 10 ⟨233365, by decide⟩ =
    .split (coordinate 11) (![⟨233094, by decide⟩,⟨233195, by decide⟩,⟨233296, by decide⟩,⟨233364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5722_233365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5722 ⟨233365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5722
    ⟨233365, by decide⟩ (by decide) (![⟨233094, by decide⟩,⟨233195, by decide⟩,⟨233296, by decide⟩,⟨233364, by decide⟩]) unmarked_context_11_5722_233365 node_context_11_5722_233365
  intro a
  fin_cases a
  · exact context_12_22888_233094
  · exact context_12_22889_233195
  · exact context_12_22890_233296
  · exact context_12_22891_233364

theorem selected_cut_08309 : selected 9 ⟨233404, by decide⟩
    (prefixPartial 12 22892) = some ⟨12, 2, 0, 233404, 22892, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_22892_233404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22892 ⟨233404, by decide⟩ :=
  accepted_of_selected 12 22892 ⟨233404, by decide⟩ ⟨12, 2, 0, 233404, 22892, 3665, 65536⟩
    (by decide) selected_cut_08309

theorem selected_cut_08310 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91572) = some ⟨13, 1, 0, 3444, 91572, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91572_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91572 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91572 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91572, 1, 16384⟩
    (by decide) selected_cut_08310

theorem selected_cut_08311 : selected 8 ⟨233419, by decide⟩
    (prefixPartial 13 91573) = some ⟨13, 2, 0, 233419, 91573, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_91573_233419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91573 ⟨233419, by decide⟩ :=
  accepted_of_selected 13 91573 ⟨233419, by decide⟩ ⟨13, 2, 0, 233419, 91573, 1025, 16384⟩
    (by decide) selected_cut_08311

theorem selected_cut_08312 : selected 8 ⟨233441, by decide⟩
    (prefixPartial 13 91574) = some ⟨13, 2, 0, 233441, 91574, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_91574_233441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91574 ⟨233441, by decide⟩ :=
  accepted_of_selected 13 91574 ⟨233441, by decide⟩ ⟨13, 2, 0, 233441, 91574, 2185, 16384⟩
    (by decide) selected_cut_08312

theorem selected_cut_08313 : selected 8 ⟨233455, by decide⟩
    (prefixPartial 13 91575) = some ⟨13, 2, 0, 233455, 91575, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_91575_233455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91575 ⟨233455, by decide⟩ :=
  accepted_of_selected 13 91575 ⟨233455, by decide⟩ ⟨13, 2, 0, 233455, 91575, 1309, 16384⟩
    (by decide) selected_cut_08313

theorem unmarked_context_12_22893_233456 : frontier 9 ⟨233456, by decide⟩
    (prefixCache 12 22893) (prefixPartial 12 22893) = false := by
  decide +kernel

theorem node_context_12_22893_233456 : EJMOriginalGlobalDAGData.nodes 9 ⟨233456, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233419, by decide⟩,⟨233441, by decide⟩,⟨233455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22893_233456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22893 ⟨233456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22893
    ⟨233456, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233419, by decide⟩,⟨233441, by decide⟩,⟨233455, by decide⟩]) unmarked_context_12_22893_233456 node_context_12_22893_233456
  intro a
  fin_cases a
  · exact context_13_91572_3444
  · exact context_13_91573_233419
  · exact context_13_91574_233441
  · exact context_13_91575_233455

theorem selected_cut_08314 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91576) = some ⟨13, 1, 0, 3444, 91576, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91576_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91576 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91576 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91576, 1, 16384⟩
    (by decide) selected_cut_08314

theorem selected_cut_08315 : selected 8 ⟨233466, by decide⟩
    (prefixPartial 13 91577) = some ⟨13, 2, 0, 233466, 91577, 909, 16384⟩ := by
  decide +kernel

theorem context_13_91577_233466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91577 ⟨233466, by decide⟩ :=
  accepted_of_selected 13 91577 ⟨233466, by decide⟩ ⟨13, 2, 0, 233466, 91577, 909, 16384⟩
    (by decide) selected_cut_08315

theorem selected_cut_08316 : selected 8 ⟨233484, by decide⟩
    (prefixPartial 13 91578) = some ⟨13, 2, 0, 233484, 91578, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_91578_233484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91578 ⟨233484, by decide⟩ :=
  accepted_of_selected 13 91578 ⟨233484, by decide⟩ ⟨13, 2, 0, 233484, 91578, 2029, 16384⟩
    (by decide) selected_cut_08316

theorem selected_cut_08317 : selected 8 ⟨233491, by decide⟩
    (prefixPartial 13 91579) = some ⟨13, 2, 0, 233491, 91579, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_91579_233491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91579 ⟨233491, by decide⟩ :=
  accepted_of_selected 13 91579 ⟨233491, by decide⟩ ⟨13, 2, 0, 233491, 91579, 1165, 16384⟩
    (by decide) selected_cut_08317

theorem unmarked_context_12_22894_233492 : frontier 9 ⟨233492, by decide⟩
    (prefixCache 12 22894) (prefixPartial 12 22894) = false := by
  decide +kernel

theorem node_context_12_22894_233492 : EJMOriginalGlobalDAGData.nodes 9 ⟨233492, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233466, by decide⟩,⟨233484, by decide⟩,⟨233491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22894_233492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22894 ⟨233492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22894
    ⟨233492, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233466, by decide⟩,⟨233484, by decide⟩,⟨233491, by decide⟩]) unmarked_context_12_22894_233492 node_context_12_22894_233492
  intro a
  fin_cases a
  · exact context_13_91576_3444
  · exact context_13_91577_233466
  · exact context_13_91578_233484
  · exact context_13_91579_233491

theorem selected_cut_08318 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91580) = some ⟨13, 1, 0, 3444, 91580, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91580_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91580 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91580 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91580, 1, 16384⟩
    (by decide) selected_cut_08318

theorem selected_cut_08319 : selected 8 ⟨233503, by decide⟩
    (prefixPartial 13 91581) = some ⟨13, 2, 0, 233503, 91581, 869, 16384⟩ := by
  decide +kernel

theorem context_13_91581_233503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91581 ⟨233503, by decide⟩ :=
  accepted_of_selected 13 91581 ⟨233503, by decide⟩ ⟨13, 2, 0, 233503, 91581, 869, 16384⟩
    (by decide) selected_cut_08319

theorem selected_cut_08320 : selected 8 ⟨233523, by decide⟩
    (prefixPartial 13 91582) = some ⟨13, 2, 0, 233523, 91582, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_91582_233523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91582 ⟨233523, by decide⟩ :=
  accepted_of_selected 13 91582 ⟨233523, by decide⟩ ⟨13, 2, 0, 233523, 91582, 2201, 16384⟩
    (by decide) selected_cut_08320

theorem selected_cut_08321 : selected 8 ⟨233530, by decide⟩
    (prefixPartial 13 91583) = some ⟨13, 2, 0, 233530, 91583, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_91583_233530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91583 ⟨233530, by decide⟩ :=
  accepted_of_selected 13 91583 ⟨233530, by decide⟩ ⟨13, 2, 0, 233530, 91583, 1185, 16384⟩
    (by decide) selected_cut_08321

theorem unmarked_context_12_22895_233531 : frontier 9 ⟨233531, by decide⟩
    (prefixCache 12 22895) (prefixPartial 12 22895) = false := by
  decide +kernel

theorem node_context_12_22895_233531 : EJMOriginalGlobalDAGData.nodes 9 ⟨233531, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233503, by decide⟩,⟨233523, by decide⟩,⟨233530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22895_233531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22895 ⟨233531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22895
    ⟨233531, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233503, by decide⟩,⟨233523, by decide⟩,⟨233530, by decide⟩]) unmarked_context_12_22895_233531 node_context_12_22895_233531
  intro a
  fin_cases a
  · exact context_13_91580_3444
  · exact context_13_91581_233503
  · exact context_13_91582_233523
  · exact context_13_91583_233530

theorem unmarked_context_11_5723_233532 : frontier 10 ⟨233532, by decide⟩
    (prefixCache 11 5723) (prefixPartial 11 5723) = false := by
  decide +kernel

theorem node_context_11_5723_233532 : EJMOriginalGlobalDAGData.nodes 10 ⟨233532, by decide⟩ =
    .split (coordinate 11) (![⟨233404, by decide⟩,⟨233456, by decide⟩,⟨233492, by decide⟩,⟨233531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5723_233532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5723 ⟨233532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5723
    ⟨233532, by decide⟩ (by decide) (![⟨233404, by decide⟩,⟨233456, by decide⟩,⟨233492, by decide⟩,⟨233531, by decide⟩]) unmarked_context_11_5723_233532 node_context_11_5723_233532
  intro a
  fin_cases a
  · exact context_12_22892_233404
  · exact context_12_22893_233456
  · exact context_12_22894_233492
  · exact context_12_22895_233531

theorem unmarked_context_10_1430_233533 : frontier 11 ⟨233533, by decide⟩
    (prefixCache 10 1430) (prefixPartial 10 1430) = false := by
  decide +kernel

theorem node_context_10_1430_233533 : EJMOriginalGlobalDAGData.nodes 11 ⟨233533, by decide⟩ =
    .split (coordinate 10) (![⟨232920, by decide⟩,⟨233037, by decide⟩,⟨233365, by decide⟩,⟨233532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1430_233533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1430 ⟨233533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1430
    ⟨233533, by decide⟩ (by decide) (![⟨232920, by decide⟩,⟨233037, by decide⟩,⟨233365, by decide⟩,⟨233532, by decide⟩]) unmarked_context_10_1430_233533 node_context_10_1430_233533
  intro a
  fin_cases a
  · exact context_11_5720_232920
  · exact context_11_5721_233037
  · exact context_11_5722_233365
  · exact context_11_5723_233532

theorem selected_cut_08322 : selected 9 ⟨233563, by decide⟩
    (prefixPartial 12 22896) = some ⟨12, 2, 0, 233563, 22896, 3297, 65536⟩ := by
  decide +kernel

theorem context_12_22896_233563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22896 ⟨233563, by decide⟩ :=
  accepted_of_selected 12 22896 ⟨233563, by decide⟩ ⟨12, 2, 0, 233563, 22896, 3297, 65536⟩
    (by decide) selected_cut_08322

theorem selected_cut_08323 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91588) = some ⟨13, 1, 0, 3444, 91588, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91588_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91588 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91588 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91588, 1, 16384⟩
    (by decide) selected_cut_08323

theorem selected_cut_08324 : selected 8 ⟨233571, by decide⟩
    (prefixPartial 13 91589) = some ⟨13, 2, 0, 233571, 91589, 749, 16384⟩ := by
  decide +kernel

theorem context_13_91589_233571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91589 ⟨233571, by decide⟩ :=
  accepted_of_selected 13 91589 ⟨233571, by decide⟩ ⟨13, 2, 0, 233571, 91589, 749, 16384⟩
    (by decide) selected_cut_08324

theorem selected_cut_08325 : selected 8 ⟨233592, by decide⟩
    (prefixPartial 13 91590) = some ⟨13, 2, 0, 233592, 91590, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_91590_233592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91590 ⟨233592, by decide⟩ :=
  accepted_of_selected 13 91590 ⟨233592, by decide⟩ ⟨13, 2, 0, 233592, 91590, 2381, 16384⟩
    (by decide) selected_cut_08325

theorem selected_cut_08326 : selected 8 ⟨233603, by decide⟩
    (prefixPartial 13 91591) = some ⟨13, 2, 0, 233603, 91591, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_91591_233603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91591 ⟨233603, by decide⟩ :=
  accepted_of_selected 13 91591 ⟨233603, by decide⟩ ⟨13, 2, 0, 233603, 91591, 1061, 16384⟩
    (by decide) selected_cut_08326

theorem unmarked_context_12_22897_233604 : frontier 9 ⟨233604, by decide⟩
    (prefixCache 12 22897) (prefixPartial 12 22897) = false := by
  decide +kernel

theorem node_context_12_22897_233604 : EJMOriginalGlobalDAGData.nodes 9 ⟨233604, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233571, by decide⟩,⟨233592, by decide⟩,⟨233603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22897_233604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22897 ⟨233604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22897
    ⟨233604, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233571, by decide⟩,⟨233592, by decide⟩,⟨233603, by decide⟩]) unmarked_context_12_22897_233604 node_context_12_22897_233604
  intro a
  fin_cases a
  · exact context_13_91588_3444
  · exact context_13_91589_233571
  · exact context_13_91590_233592
  · exact context_13_91591_233603

theorem selected_cut_08327 : selected 9 ⟨233648, by decide⟩
    (prefixPartial 12 22898) = some ⟨12, 2, 0, 233648, 22898, 4081, 65536⟩ := by
  decide +kernel

theorem context_12_22898_233648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22898 ⟨233648, by decide⟩ :=
  accepted_of_selected 12 22898 ⟨233648, by decide⟩ ⟨12, 2, 0, 233648, 22898, 4081, 65536⟩
    (by decide) selected_cut_08327

theorem selected_cut_08328 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91596) = some ⟨13, 1, 0, 3444, 91596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91596, 1, 16384⟩
    (by decide) selected_cut_08328

theorem selected_cut_08329 : selected 8 ⟨233661, by decide⟩
    (prefixPartial 13 91597) = some ⟨13, 2, 0, 233661, 91597, 681, 16384⟩ := by
  decide +kernel

theorem context_13_91597_233661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91597 ⟨233661, by decide⟩ :=
  accepted_of_selected 13 91597 ⟨233661, by decide⟩ ⟨13, 2, 0, 233661, 91597, 681, 16384⟩
    (by decide) selected_cut_08329

theorem selected_cut_08330 : selected 8 ⟨233687, by decide⟩
    (prefixPartial 13 91598) = some ⟨13, 2, 0, 233687, 91598, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_91598_233687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91598 ⟨233687, by decide⟩ :=
  accepted_of_selected 13 91598 ⟨233687, by decide⟩ ⟨13, 2, 0, 233687, 91598, 2529, 16384⟩
    (by decide) selected_cut_08330

theorem selected_cut_08331 : selected 8 ⟨233697, by decide⟩
    (prefixPartial 13 91599) = some ⟨13, 2, 0, 233697, 91599, 969, 16384⟩ := by
  decide +kernel

theorem context_13_91599_233697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91599 ⟨233697, by decide⟩ :=
  accepted_of_selected 13 91599 ⟨233697, by decide⟩ ⟨13, 2, 0, 233697, 91599, 969, 16384⟩
    (by decide) selected_cut_08331

theorem unmarked_context_12_22899_233698 : frontier 9 ⟨233698, by decide⟩
    (prefixCache 12 22899) (prefixPartial 12 22899) = false := by
  decide +kernel

theorem node_context_12_22899_233698 : EJMOriginalGlobalDAGData.nodes 9 ⟨233698, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233661, by decide⟩,⟨233687, by decide⟩,⟨233697, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22899_233698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22899 ⟨233698, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22899
    ⟨233698, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233661, by decide⟩,⟨233687, by decide⟩,⟨233697, by decide⟩]) unmarked_context_12_22899_233698 node_context_12_22899_233698
  intro a
  fin_cases a
  · exact context_13_91596_3444
  · exact context_13_91597_233661
  · exact context_13_91598_233687
  · exact context_13_91599_233697

theorem unmarked_context_11_5724_233699 : frontier 10 ⟨233699, by decide⟩
    (prefixCache 11 5724) (prefixPartial 11 5724) = false := by
  decide +kernel

theorem node_context_11_5724_233699 : EJMOriginalGlobalDAGData.nodes 10 ⟨233699, by decide⟩ =
    .split (coordinate 11) (![⟨233563, by decide⟩,⟨233604, by decide⟩,⟨233648, by decide⟩,⟨233698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5724_233699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5724 ⟨233699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5724
    ⟨233699, by decide⟩ (by decide) (![⟨233563, by decide⟩,⟨233604, by decide⟩,⟨233648, by decide⟩,⟨233698, by decide⟩]) unmarked_context_11_5724_233699 node_context_11_5724_233699
  intro a
  fin_cases a
  · exact context_12_22896_233563
  · exact context_12_22897_233604
  · exact context_12_22898_233648
  · exact context_12_22899_233698

theorem selected_cut_08332 : selected 9 ⟨233728, by decide⟩
    (prefixPartial 12 22900) = some ⟨12, 2, 0, 233728, 22900, 2685, 65536⟩ := by
  decide +kernel

theorem context_12_22900_233728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22900 ⟨233728, by decide⟩ :=
  accepted_of_selected 12 22900 ⟨233728, by decide⟩ ⟨12, 2, 0, 233728, 22900, 2685, 65536⟩
    (by decide) selected_cut_08332

theorem selected_cut_08333 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 22901) = some ⟨12, 1, 0, 126884, 22901, 1, 65536⟩ := by
  decide +kernel

theorem context_12_22901_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22901 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 22901 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 22901, 1, 65536⟩
    (by decide) selected_cut_08333

theorem selected_cut_08334 : selected 9 ⟨233765, by decide⟩
    (prefixPartial 12 22902) = some ⟨12, 2, 0, 233765, 22902, 3153, 65536⟩ := by
  decide +kernel

theorem context_12_22902_233765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22902 ⟨233765, by decide⟩ :=
  accepted_of_selected 12 22902 ⟨233765, by decide⟩ ⟨12, 2, 0, 233765, 22902, 3153, 65536⟩
    (by decide) selected_cut_08334

theorem selected_cut_08335 : selected 9 ⟨233799, by decide⟩
    (prefixPartial 12 22903) = some ⟨12, 2, 0, 233799, 22903, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_22903_233799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22903 ⟨233799, by decide⟩ :=
  accepted_of_selected 12 22903 ⟨233799, by decide⟩ ⟨12, 2, 0, 233799, 22903, 3293, 65536⟩
    (by decide) selected_cut_08335

theorem unmarked_context_11_5725_233800 : frontier 10 ⟨233800, by decide⟩
    (prefixCache 11 5725) (prefixPartial 11 5725) = false := by
  decide +kernel

theorem node_context_11_5725_233800 : EJMOriginalGlobalDAGData.nodes 10 ⟨233800, by decide⟩ =
    .split (coordinate 11) (![⟨233728, by decide⟩,⟨126884, by decide⟩,⟨233765, by decide⟩,⟨233799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5725_233800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5725 ⟨233800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5725
    ⟨233800, by decide⟩ (by decide) (![⟨233728, by decide⟩,⟨126884, by decide⟩,⟨233765, by decide⟩,⟨233799, by decide⟩]) unmarked_context_11_5725_233800 node_context_11_5725_233800
  intro a
  fin_cases a
  · exact context_12_22900_233728
  · exact context_12_22901_126884
  · exact context_12_22902_233765
  · exact context_12_22903_233799

theorem selected_cut_08336 : selected 9 ⟨233834, by decide⟩
    (prefixPartial 12 22904) = some ⟨12, 2, 0, 233834, 22904, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_22904_233834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22904 ⟨233834, by decide⟩ :=
  accepted_of_selected 12 22904 ⟨233834, by decide⟩ ⟨12, 2, 0, 233834, 22904, 3357, 65536⟩
    (by decide) selected_cut_08336

theorem selected_cut_08337 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 91620) = some ⟨13, 1, 0, 3444, 91620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_91620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 91620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 91620, 1, 16384⟩
    (by decide) selected_cut_08337

theorem selected_cut_08338 : selected 8 ⟨233840, by decide⟩
    (prefixPartial 13 91621) = some ⟨13, 2, 0, 233840, 91621, 437, 16384⟩ := by
  decide +kernel

theorem context_13_91621_233840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91621 ⟨233840, by decide⟩ :=
  accepted_of_selected 13 91621 ⟨233840, by decide⟩ ⟨13, 2, 0, 233840, 91621, 437, 16384⟩
    (by decide) selected_cut_08338

theorem selected_cut_08339 : selected 8 ⟨233876, by decide⟩
    (prefixPartial 13 91622) = some ⟨13, 2, 0, 233876, 91622, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_91622_233876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91622 ⟨233876, by decide⟩ :=
  accepted_of_selected 13 91622 ⟨233876, by decide⟩ ⟨13, 2, 0, 233876, 91622, 2681, 16384⟩
    (by decide) selected_cut_08339

theorem selected_cut_08340 : selected 8 ⟨233881, by decide⟩
    (prefixPartial 13 91623) = some ⟨13, 2, 0, 233881, 91623, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_91623_233881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91623 ⟨233881, by decide⟩ :=
  accepted_of_selected 13 91623 ⟨233881, by decide⟩ ⟨13, 2, 0, 233881, 91623, 1149, 16384⟩
    (by decide) selected_cut_08340

theorem unmarked_context_12_22905_233882 : frontier 9 ⟨233882, by decide⟩
    (prefixCache 12 22905) (prefixPartial 12 22905) = false := by
  decide +kernel

theorem node_context_12_22905_233882 : EJMOriginalGlobalDAGData.nodes 9 ⟨233882, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨233840, by decide⟩,⟨233876, by decide⟩,⟨233881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22905_233882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22905 ⟨233882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22905
    ⟨233882, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨233840, by decide⟩,⟨233876, by decide⟩,⟨233881, by decide⟩]) unmarked_context_12_22905_233882 node_context_12_22905_233882
  intro a
  fin_cases a
  · exact context_13_91620_3444
  · exact context_13_91621_233840
  · exact context_13_91622_233876
  · exact context_13_91623_233881

theorem selected_cut_08341 : selected 9 ⟨233928, by decide⟩
    (prefixPartial 12 22906) = some ⟨12, 2, 0, 233928, 22906, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_22906_233928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22906 ⟨233928, by decide⟩ :=
  accepted_of_selected 12 22906 ⟨233928, by decide⟩ ⟨12, 2, 0, 233928, 22906, 3825, 65536⟩
    (by decide) selected_cut_08341

theorem selected_cut_08342 : selected 9 ⟨233970, by decide⟩
    (prefixPartial 12 22907) = some ⟨12, 2, 0, 233970, 22907, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_22907_233970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22907 ⟨233970, by decide⟩ :=
  accepted_of_selected 12 22907 ⟨233970, by decide⟩ ⟨12, 2, 0, 233970, 22907, 3965, 65536⟩
    (by decide) selected_cut_08342

theorem unmarked_context_11_5726_233971 : frontier 10 ⟨233971, by decide⟩
    (prefixCache 11 5726) (prefixPartial 11 5726) = false := by
  decide +kernel

theorem node_context_11_5726_233971 : EJMOriginalGlobalDAGData.nodes 10 ⟨233971, by decide⟩ =
    .split (coordinate 11) (![⟨233834, by decide⟩,⟨233882, by decide⟩,⟨233928, by decide⟩,⟨233970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5726_233971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5726 ⟨233971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5726
    ⟨233971, by decide⟩ (by decide) (![⟨233834, by decide⟩,⟨233882, by decide⟩,⟨233928, by decide⟩,⟨233970, by decide⟩]) unmarked_context_11_5726_233971 node_context_11_5726_233971
  intro a
  fin_cases a
  · exact context_12_22904_233834
  · exact context_12_22905_233882
  · exact context_12_22906_233928
  · exact context_12_22907_233970

theorem selected_cut_08343 : selected 9 ⟨234003, by decide⟩
    (prefixPartial 12 22908) = some ⟨12, 2, 0, 234003, 22908, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_22908_234003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22908 ⟨234003, by decide⟩ :=
  accepted_of_selected 12 22908 ⟨234003, by decide⟩ ⟨12, 2, 0, 234003, 22908, 2861, 65536⟩
    (by decide) selected_cut_08343

theorem selected_cut_08344 : selected 9 ⟨234037, by decide⟩
    (prefixPartial 12 22909) = some ⟨12, 2, 0, 234037, 22909, 3569, 65536⟩ := by
  decide +kernel

theorem context_12_22909_234037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22909 ⟨234037, by decide⟩ :=
  accepted_of_selected 12 22909 ⟨234037, by decide⟩ ⟨12, 2, 0, 234037, 22909, 3569, 65536⟩
    (by decide) selected_cut_08344

theorem selected_cut_08345 : selected 9 ⟨234070, by decide⟩
    (prefixPartial 12 22910) = some ⟨12, 2, 0, 234070, 22910, 3297, 65536⟩ := by
  decide +kernel

theorem context_12_22910_234070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22910 ⟨234070, by decide⟩ :=
  accepted_of_selected 12 22910 ⟨234070, by decide⟩ ⟨12, 2, 0, 234070, 22910, 3297, 65536⟩
    (by decide) selected_cut_08345

theorem selected_cut_08346 : selected 9 ⟨234096, by decide⟩
    (prefixPartial 12 22911) = some ⟨12, 2, 0, 234096, 22911, 3353, 65536⟩ := by
  decide +kernel

theorem context_12_22911_234096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22911 ⟨234096, by decide⟩ :=
  accepted_of_selected 12 22911 ⟨234096, by decide⟩ ⟨12, 2, 0, 234096, 22911, 3353, 65536⟩
    (by decide) selected_cut_08346

theorem unmarked_context_11_5727_234097 : frontier 10 ⟨234097, by decide⟩
    (prefixCache 11 5727) (prefixPartial 11 5727) = false := by
  decide +kernel

theorem node_context_11_5727_234097 : EJMOriginalGlobalDAGData.nodes 10 ⟨234097, by decide⟩ =
    .split (coordinate 11) (![⟨234003, by decide⟩,⟨234037, by decide⟩,⟨234070, by decide⟩,⟨234096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5727_234097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5727 ⟨234097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5727
    ⟨234097, by decide⟩ (by decide) (![⟨234003, by decide⟩,⟨234037, by decide⟩,⟨234070, by decide⟩,⟨234096, by decide⟩]) unmarked_context_11_5727_234097 node_context_11_5727_234097
  intro a
  fin_cases a
  · exact context_12_22908_234003
  · exact context_12_22909_234037
  · exact context_12_22910_234070
  · exact context_12_22911_234096

theorem unmarked_context_10_1431_234098 : frontier 11 ⟨234098, by decide⟩
    (prefixCache 10 1431) (prefixPartial 10 1431) = false := by
  decide +kernel

theorem node_context_10_1431_234098 : EJMOriginalGlobalDAGData.nodes 11 ⟨234098, by decide⟩ =
    .split (coordinate 10) (![⟨233699, by decide⟩,⟨233800, by decide⟩,⟨233971, by decide⟩,⟨234097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1431_234098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1431 ⟨234098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1431
    ⟨234098, by decide⟩ (by decide) (![⟨233699, by decide⟩,⟨233800, by decide⟩,⟨233971, by decide⟩,⟨234097, by decide⟩]) unmarked_context_10_1431_234098 node_context_10_1431_234098
  intro a
  fin_cases a
  · exact context_11_5724_233699
  · exact context_11_5725_233800
  · exact context_11_5726_233971
  · exact context_11_5727_234097

theorem unmarked_context_9_357_234099 : frontier 12 ⟨234099, by decide⟩
    (prefixCache 9 357) (prefixPartial 9 357) = false := by
  decide +kernel

theorem node_context_9_357_234099 : EJMOriginalGlobalDAGData.nodes 12 ⟨234099, by decide⟩ =
    .split (coordinate 9) (![⟨231985, by decide⟩,⟨232727, by decide⟩,⟨233533, by decide⟩,⟨234098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_357_234099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 357 ⟨234099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 357
    ⟨234099, by decide⟩ (by decide) (![⟨231985, by decide⟩,⟨232727, by decide⟩,⟨233533, by decide⟩,⟨234098, by decide⟩]) unmarked_context_9_357_234099 node_context_9_357_234099
  intro a
  fin_cases a
  · exact context_10_1428_231985
  · exact context_10_1429_232727
  · exact context_10_1430_233533
  · exact context_10_1431_234098

theorem selected_cut_08347 : selected 9 ⟨234127, by decide⟩
    (prefixPartial 12 22912) = some ⟨12, 2, 0, 234127, 22912, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_22912_234127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22912 ⟨234127, by decide⟩ :=
  accepted_of_selected 12 22912 ⟨234127, by decide⟩ ⟨12, 2, 0, 234127, 22912, 2737, 65536⟩
    (by decide) selected_cut_08347

theorem selected_cut_08348 : selected 9 ⟨234153, by decide⟩
    (prefixPartial 12 22913) = some ⟨12, 2, 0, 234153, 22913, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_22913_234153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22913 ⟨234153, by decide⟩ :=
  accepted_of_selected 12 22913 ⟨234153, by decide⟩ ⟨12, 2, 0, 234153, 22913, 2661, 65536⟩
    (by decide) selected_cut_08348

theorem selected_cut_08349 : selected 9 ⟨234182, by decide⟩
    (prefixPartial 12 22914) = some ⟨12, 2, 0, 234182, 22914, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_22914_234182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22914 ⟨234182, by decide⟩ :=
  accepted_of_selected 12 22914 ⟨234182, by decide⟩ ⟨12, 2, 0, 234182, 22914, 2953, 65536⟩
    (by decide) selected_cut_08349

theorem selected_cut_08350 : selected 9 ⟨234206, by decide⟩
    (prefixPartial 12 22915) = some ⟨12, 2, 0, 234206, 22915, 2885, 65536⟩ := by
  decide +kernel

theorem context_12_22915_234206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22915 ⟨234206, by decide⟩ :=
  accepted_of_selected 12 22915 ⟨234206, by decide⟩ ⟨12, 2, 0, 234206, 22915, 2885, 65536⟩
    (by decide) selected_cut_08350

theorem unmarked_context_11_5728_234207 : frontier 10 ⟨234207, by decide⟩
    (prefixCache 11 5728) (prefixPartial 11 5728) = false := by
  decide +kernel

theorem node_context_11_5728_234207 : EJMOriginalGlobalDAGData.nodes 10 ⟨234207, by decide⟩ =
    .split (coordinate 11) (![⟨234127, by decide⟩,⟨234153, by decide⟩,⟨234182, by decide⟩,⟨234206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5728_234207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5728 ⟨234207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5728
    ⟨234207, by decide⟩ (by decide) (![⟨234127, by decide⟩,⟨234153, by decide⟩,⟨234182, by decide⟩,⟨234206, by decide⟩]) unmarked_context_11_5728_234207 node_context_11_5728_234207
  intro a
  fin_cases a
  · exact context_12_22912_234127
  · exact context_12_22913_234153
  · exact context_12_22914_234182
  · exact context_12_22915_234206

theorem selected_cut_08351 : selected 9 ⟨234234, by decide⟩
    (prefixPartial 12 22916) = some ⟨12, 2, 0, 234234, 22916, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_22916_234234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22916 ⟨234234, by decide⟩ :=
  accepted_of_selected 12 22916 ⟨234234, by decide⟩ ⟨12, 2, 0, 234234, 22916, 2117, 65536⟩
    (by decide) selected_cut_08351

theorem selected_cut_08352 : selected 9 ⟨234263, by decide⟩
    (prefixPartial 12 22917) = some ⟨12, 2, 0, 234263, 22917, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_22917_234263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22917 ⟨234263, by decide⟩ :=
  accepted_of_selected 12 22917 ⟨234263, by decide⟩ ⟨12, 2, 0, 234263, 22917, 3141, 65536⟩
    (by decide) selected_cut_08352

theorem selected_cut_08353 : selected 9 ⟨234288, by decide⟩
    (prefixPartial 12 22918) = some ⟨12, 2, 0, 234288, 22918, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_22918_234288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22918 ⟨234288, by decide⟩ :=
  accepted_of_selected 12 22918 ⟨234288, by decide⟩ ⟨12, 2, 0, 234288, 22918, 2257, 65536⟩
    (by decide) selected_cut_08353

theorem selected_cut_08354 : selected 9 ⟨234315, by decide⟩
    (prefixPartial 12 22919) = some ⟨12, 2, 0, 234315, 22919, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_22919_234315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22919 ⟨234315, by decide⟩ :=
  accepted_of_selected 12 22919 ⟨234315, by decide⟩ ⟨12, 2, 0, 234315, 22919, 2233, 65536⟩
    (by decide) selected_cut_08354

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
