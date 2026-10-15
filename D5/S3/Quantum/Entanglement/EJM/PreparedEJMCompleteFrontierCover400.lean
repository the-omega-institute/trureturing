/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover399
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38403 : selected 9 ⟨1035120, by decide⟩
    (prefixPartial 12 301383) = some ⟨12, 2, 0, 1035120, 301383, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_301383_1035120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301383 ⟨1035120, by decide⟩ :=
  accepted_of_selected 12 301383 ⟨1035120, by decide⟩ ⟨12, 2, 0, 1035120, 301383, 2285, 65536⟩
    (by decide) selected_cut_38403

theorem unmarked_context_11_75345_1035121 : frontier 10 ⟨1035121, by decide⟩
    (prefixCache 11 75345) (prefixPartial 11 75345) = false := by
  decide +kernel

theorem node_context_11_75345_1035121 : EJMOriginalGlobalDAGData.nodes 10 ⟨1035121, by decide⟩ =
    .split (coordinate 11) (![⟨1035030, by decide⟩,⟨891951, by decide⟩,⟨1035077, by decide⟩,⟨1035120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75345_1035121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75345 ⟨1035121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75345
    ⟨1035121, by decide⟩ (by decide) (![⟨1035030, by decide⟩,⟨891951, by decide⟩,⟨1035077, by decide⟩,⟨1035120, by decide⟩]) unmarked_context_11_75345_1035121 node_context_11_75345_1035121
  intro a
  fin_cases a
  · exact context_12_301380_1035030
  · exact context_12_301381_891951
  · exact context_12_301382_1035077
  · exact context_12_301383_1035120

theorem selected_cut_38404 : selected 9 ⟨1035162, by decide⟩
    (prefixPartial 12 301384) = some ⟨12, 2, 0, 1035162, 301384, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_301384_1035162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301384 ⟨1035162, by decide⟩ :=
  accepted_of_selected 12 301384 ⟨1035162, by decide⟩ ⟨12, 2, 0, 1035162, 301384, 2401, 65536⟩
    (by decide) selected_cut_38404

theorem selected_cut_38405 : selected 9 ⟨1035189, by decide⟩
    (prefixPartial 12 301385) = some ⟨12, 2, 0, 1035189, 301385, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_301385_1035189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301385 ⟨1035189, by decide⟩ :=
  accepted_of_selected 12 301385 ⟨1035189, by decide⟩ ⟨12, 2, 0, 1035189, 301385, 1993, 65536⟩
    (by decide) selected_cut_38405

theorem selected_cut_38406 : selected 9 ⟨1035222, by decide⟩
    (prefixPartial 12 301386) = some ⟨12, 2, 0, 1035222, 301386, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_301386_1035222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301386 ⟨1035222, by decide⟩ :=
  accepted_of_selected 12 301386 ⟨1035222, by decide⟩ ⟨12, 2, 0, 1035222, 301386, 2101, 65536⟩
    (by decide) selected_cut_38406

theorem selected_cut_38407 : selected 9 ⟨1035251, by decide⟩
    (prefixPartial 12 301387) = some ⟨12, 2, 0, 1035251, 301387, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_301387_1035251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301387 ⟨1035251, by decide⟩ :=
  accepted_of_selected 12 301387 ⟨1035251, by decide⟩ ⟨12, 2, 0, 1035251, 301387, 1957, 65536⟩
    (by decide) selected_cut_38407

theorem unmarked_context_11_75346_1035252 : frontier 10 ⟨1035252, by decide⟩
    (prefixCache 11 75346) (prefixPartial 11 75346) = false := by
  decide +kernel

theorem node_context_11_75346_1035252 : EJMOriginalGlobalDAGData.nodes 10 ⟨1035252, by decide⟩ =
    .split (coordinate 11) (![⟨1035162, by decide⟩,⟨1035189, by decide⟩,⟨1035222, by decide⟩,⟨1035251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75346_1035252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75346 ⟨1035252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75346
    ⟨1035252, by decide⟩ (by decide) (![⟨1035162, by decide⟩,⟨1035189, by decide⟩,⟨1035222, by decide⟩,⟨1035251, by decide⟩]) unmarked_context_11_75346_1035252 node_context_11_75346_1035252
  intro a
  fin_cases a
  · exact context_12_301384_1035162
  · exact context_12_301385_1035189
  · exact context_12_301386_1035222
  · exact context_12_301387_1035251

theorem selected_cut_38408 : selected 9 ⟨1035296, by decide⟩
    (prefixPartial 12 301388) = some ⟨12, 2, 0, 1035296, 301388, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_301388_1035296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301388 ⟨1035296, by decide⟩ :=
  accepted_of_selected 12 301388 ⟨1035296, by decide⟩ ⟨12, 2, 0, 1035296, 301388, 2457, 65536⟩
    (by decide) selected_cut_38408

theorem selected_cut_38409 : selected 9 ⟨1035335, by decide⟩
    (prefixPartial 12 301389) = some ⟨12, 2, 0, 1035335, 301389, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_301389_1035335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301389 ⟨1035335, by decide⟩ :=
  accepted_of_selected 12 301389 ⟨1035335, by decide⟩ ⟨12, 2, 0, 1035335, 301389, 2149, 65536⟩
    (by decide) selected_cut_38409

theorem selected_cut_38410 : selected 9 ⟨1035376, by decide⟩
    (prefixPartial 12 301390) = some ⟨12, 2, 0, 1035376, 301390, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_301390_1035376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301390 ⟨1035376, by decide⟩ :=
  accepted_of_selected 12 301390 ⟨1035376, by decide⟩ ⟨12, 2, 0, 1035376, 301390, 2073, 65536⟩
    (by decide) selected_cut_38410

theorem selected_cut_38411 : selected 9 ⟨1035413, by decide⟩
    (prefixPartial 12 301391) = some ⟨12, 2, 0, 1035413, 301391, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_301391_1035413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301391 ⟨1035413, by decide⟩ :=
  accepted_of_selected 12 301391 ⟨1035413, by decide⟩ ⟨12, 2, 0, 1035413, 301391, 2081, 65536⟩
    (by decide) selected_cut_38411

theorem unmarked_context_11_75347_1035414 : frontier 10 ⟨1035414, by decide⟩
    (prefixCache 11 75347) (prefixPartial 11 75347) = false := by
  decide +kernel

theorem node_context_11_75347_1035414 : EJMOriginalGlobalDAGData.nodes 10 ⟨1035414, by decide⟩ =
    .split (coordinate 11) (![⟨1035296, by decide⟩,⟨1035335, by decide⟩,⟨1035376, by decide⟩,⟨1035413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75347_1035414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75347 ⟨1035414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75347
    ⟨1035414, by decide⟩ (by decide) (![⟨1035296, by decide⟩,⟨1035335, by decide⟩,⟨1035376, by decide⟩,⟨1035413, by decide⟩]) unmarked_context_11_75347_1035414 node_context_11_75347_1035414
  intro a
  fin_cases a
  · exact context_12_301388_1035296
  · exact context_12_301389_1035335
  · exact context_12_301390_1035376
  · exact context_12_301391_1035413

theorem unmarked_context_10_18836_1035415 : frontier 11 ⟨1035415, by decide⟩
    (prefixCache 10 18836) (prefixPartial 10 18836) = false := by
  decide +kernel

theorem node_context_10_18836_1035415 : EJMOriginalGlobalDAGData.nodes 11 ⟨1035415, by decide⟩ =
    .split (coordinate 10) (![⟨1034969, by decide⟩,⟨1035121, by decide⟩,⟨1035252, by decide⟩,⟨1035414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18836_1035415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18836 ⟨1035415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18836
    ⟨1035415, by decide⟩ (by decide) (![⟨1034969, by decide⟩,⟨1035121, by decide⟩,⟨1035252, by decide⟩,⟨1035414, by decide⟩]) unmarked_context_10_18836_1035415 node_context_10_18836_1035415
  intro a
  fin_cases a
  · exact context_11_75344_1034969
  · exact context_11_75345_1035121
  · exact context_11_75346_1035252
  · exact context_11_75347_1035414

theorem selected_cut_38412 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18837) = some ⟨10, 1, 0, 893098, 18837, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18837_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18837 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18837 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18837, 1, 1048576⟩
    (by decide) selected_cut_38412

theorem selected_cut_38413 : selected 9 ⟨1035441, by decide⟩
    (prefixPartial 12 301408) = some ⟨12, 2, 0, 1035441, 301408, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_301408_1035441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301408 ⟨1035441, by decide⟩ :=
  accepted_of_selected 12 301408 ⟨1035441, by decide⟩ ⟨12, 2, 0, 1035441, 301408, 1669, 65536⟩
    (by decide) selected_cut_38413

theorem selected_cut_38414 : selected 9 ⟨1035461, by decide⟩
    (prefixPartial 12 301409) = some ⟨12, 2, 0, 1035461, 301409, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_301409_1035461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301409 ⟨1035461, by decide⟩ :=
  accepted_of_selected 12 301409 ⟨1035461, by decide⟩ ⟨12, 2, 0, 1035461, 301409, 1581, 65536⟩
    (by decide) selected_cut_38414

theorem selected_cut_38415 : selected 9 ⟨1035488, by decide⟩
    (prefixPartial 12 301410) = some ⟨12, 2, 0, 1035488, 301410, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_301410_1035488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301410 ⟨1035488, by decide⟩ :=
  accepted_of_selected 12 301410 ⟨1035488, by decide⟩ ⟨12, 2, 0, 1035488, 301410, 1333, 65536⟩
    (by decide) selected_cut_38415

theorem selected_cut_38416 : selected 9 ⟨1035505, by decide⟩
    (prefixPartial 12 301411) = some ⟨12, 2, 0, 1035505, 301411, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_301411_1035505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301411 ⟨1035505, by decide⟩ :=
  accepted_of_selected 12 301411 ⟨1035505, by decide⟩ ⟨12, 2, 0, 1035505, 301411, 1433, 65536⟩
    (by decide) selected_cut_38416

theorem unmarked_context_11_75352_1035506 : frontier 10 ⟨1035506, by decide⟩
    (prefixCache 11 75352) (prefixPartial 11 75352) = false := by
  decide +kernel

theorem node_context_11_75352_1035506 : EJMOriginalGlobalDAGData.nodes 10 ⟨1035506, by decide⟩ =
    .split (coordinate 11) (![⟨1035441, by decide⟩,⟨1035461, by decide⟩,⟨1035488, by decide⟩,⟨1035505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75352_1035506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75352 ⟨1035506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75352
    ⟨1035506, by decide⟩ (by decide) (![⟨1035441, by decide⟩,⟨1035461, by decide⟩,⟨1035488, by decide⟩,⟨1035505, by decide⟩]) unmarked_context_11_75352_1035506 node_context_11_75352_1035506
  intro a
  fin_cases a
  · exact context_12_301408_1035441
  · exact context_12_301409_1035461
  · exact context_12_301410_1035488
  · exact context_12_301411_1035505

theorem selected_cut_38417 : selected 9 ⟨1035537, by decide⟩
    (prefixPartial 12 301412) = some ⟨12, 2, 0, 1035537, 301412, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_301412_1035537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301412 ⟨1035537, by decide⟩ :=
  accepted_of_selected 12 301412 ⟨1035537, by decide⟩ ⟨12, 2, 0, 1035537, 301412, 2069, 65536⟩
    (by decide) selected_cut_38417

theorem selected_cut_38418 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 301413) = some ⟨12, 1, 0, 891951, 301413, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301413_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301413 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 301413 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 301413, 1, 65536⟩
    (by decide) selected_cut_38418

theorem selected_cut_38419 : selected 9 ⟨1035566, by decide⟩
    (prefixPartial 12 301414) = some ⟨12, 2, 0, 1035566, 301414, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_301414_1035566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301414 ⟨1035566, by decide⟩ :=
  accepted_of_selected 12 301414 ⟨1035566, by decide⟩ ⟨12, 2, 0, 1035566, 301414, 1493, 65536⟩
    (by decide) selected_cut_38419

theorem selected_cut_38420 : selected 9 ⟨1035594, by decide⟩
    (prefixPartial 12 301415) = some ⟨12, 2, 0, 1035594, 301415, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_301415_1035594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301415 ⟨1035594, by decide⟩ :=
  accepted_of_selected 12 301415 ⟨1035594, by decide⟩ ⟨12, 2, 0, 1035594, 301415, 1681, 65536⟩
    (by decide) selected_cut_38420

theorem unmarked_context_11_75353_1035595 : frontier 10 ⟨1035595, by decide⟩
    (prefixCache 11 75353) (prefixPartial 11 75353) = false := by
  decide +kernel

theorem node_context_11_75353_1035595 : EJMOriginalGlobalDAGData.nodes 10 ⟨1035595, by decide⟩ =
    .split (coordinate 11) (![⟨1035537, by decide⟩,⟨891951, by decide⟩,⟨1035566, by decide⟩,⟨1035594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75353_1035595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75353 ⟨1035595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75353
    ⟨1035595, by decide⟩ (by decide) (![⟨1035537, by decide⟩,⟨891951, by decide⟩,⟨1035566, by decide⟩,⟨1035594, by decide⟩]) unmarked_context_11_75353_1035595 node_context_11_75353_1035595
  intro a
  fin_cases a
  · exact context_12_301412_1035537
  · exact context_12_301413_891951
  · exact context_12_301414_1035566
  · exact context_12_301415_1035594

theorem selected_cut_38421 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 75354) = some ⟨11, 1, 0, 900587, 75354, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75354_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75354 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 75354 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 75354, 1, 262144⟩
    (by decide) selected_cut_38421

theorem selected_cut_38422 : selected 9 ⟨1035620, by decide⟩
    (prefixPartial 12 301420) = some ⟨12, 2, 0, 1035620, 301420, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_301420_1035620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301420 ⟨1035620, by decide⟩ :=
  accepted_of_selected 12 301420 ⟨1035620, by decide⟩ ⟨12, 2, 0, 1035620, 301420, 1817, 65536⟩
    (by decide) selected_cut_38422

theorem selected_cut_38423 : selected 9 ⟨1035651, by decide⟩
    (prefixPartial 12 301421) = some ⟨12, 2, 0, 1035651, 301421, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_301421_1035651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301421 ⟨1035651, by decide⟩ :=
  accepted_of_selected 12 301421 ⟨1035651, by decide⟩ ⟨12, 2, 0, 1035651, 301421, 1689, 65536⟩
    (by decide) selected_cut_38423

theorem selected_cut_38424 : selected 9 ⟨1035675, by decide⟩
    (prefixPartial 12 301422) = some ⟨12, 2, 0, 1035675, 301422, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_301422_1035675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301422 ⟨1035675, by decide⟩ :=
  accepted_of_selected 12 301422 ⟨1035675, by decide⟩ ⟨12, 2, 0, 1035675, 301422, 1521, 65536⟩
    (by decide) selected_cut_38424

theorem selected_cut_38425 : selected 9 ⟨1035705, by decide⟩
    (prefixPartial 12 301423) = some ⟨12, 2, 0, 1035705, 301423, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_301423_1035705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301423 ⟨1035705, by decide⟩ :=
  accepted_of_selected 12 301423 ⟨1035705, by decide⟩ ⟨12, 2, 0, 1035705, 301423, 1685, 65536⟩
    (by decide) selected_cut_38425

theorem unmarked_context_11_75355_1035706 : frontier 10 ⟨1035706, by decide⟩
    (prefixCache 11 75355) (prefixPartial 11 75355) = false := by
  decide +kernel

theorem node_context_11_75355_1035706 : EJMOriginalGlobalDAGData.nodes 10 ⟨1035706, by decide⟩ =
    .split (coordinate 11) (![⟨1035620, by decide⟩,⟨1035651, by decide⟩,⟨1035675, by decide⟩,⟨1035705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75355_1035706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75355 ⟨1035706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75355
    ⟨1035706, by decide⟩ (by decide) (![⟨1035620, by decide⟩,⟨1035651, by decide⟩,⟨1035675, by decide⟩,⟨1035705, by decide⟩]) unmarked_context_11_75355_1035706 node_context_11_75355_1035706
  intro a
  fin_cases a
  · exact context_12_301420_1035620
  · exact context_12_301421_1035651
  · exact context_12_301422_1035675
  · exact context_12_301423_1035705

theorem unmarked_context_10_18838_1035707 : frontier 11 ⟨1035707, by decide⟩
    (prefixCache 10 18838) (prefixPartial 10 18838) = false := by
  decide +kernel

theorem node_context_10_18838_1035707 : EJMOriginalGlobalDAGData.nodes 11 ⟨1035707, by decide⟩ =
    .split (coordinate 10) (![⟨1035506, by decide⟩,⟨1035595, by decide⟩,⟨900587, by decide⟩,⟨1035706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18838_1035707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18838 ⟨1035707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18838
    ⟨1035707, by decide⟩ (by decide) (![⟨1035506, by decide⟩,⟨1035595, by decide⟩,⟨900587, by decide⟩,⟨1035706, by decide⟩]) unmarked_context_10_18838_1035707 node_context_10_18838_1035707
  intro a
  fin_cases a
  · exact context_11_75352_1035506
  · exact context_11_75353_1035595
  · exact context_11_75354_900587
  · exact context_11_75355_1035706

theorem selected_cut_38426 : selected 9 ⟨1035732, by decide⟩
    (prefixPartial 12 301424) = some ⟨12, 2, 0, 1035732, 301424, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_301424_1035732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301424 ⟨1035732, by decide⟩ :=
  accepted_of_selected 12 301424 ⟨1035732, by decide⟩ ⟨12, 2, 0, 1035732, 301424, 1589, 65536⟩
    (by decide) selected_cut_38426

theorem selected_cut_38427 : selected 9 ⟨1035763, by decide⟩
    (prefixPartial 12 301425) = some ⟨12, 2, 0, 1035763, 301425, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_301425_1035763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301425 ⟨1035763, by decide⟩ :=
  accepted_of_selected 12 301425 ⟨1035763, by decide⟩ ⟨12, 2, 0, 1035763, 301425, 1633, 65536⟩
    (by decide) selected_cut_38427

theorem selected_cut_38428 : selected 9 ⟨1035786, by decide⟩
    (prefixPartial 12 301426) = some ⟨12, 2, 0, 1035786, 301426, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_301426_1035786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301426 ⟨1035786, by decide⟩ :=
  accepted_of_selected 12 301426 ⟨1035786, by decide⟩ ⟨12, 2, 0, 1035786, 301426, 1437, 65536⟩
    (by decide) selected_cut_38428

theorem selected_cut_38429 : selected 9 ⟨1035811, by decide⟩
    (prefixPartial 12 301427) = some ⟨12, 2, 0, 1035811, 301427, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_301427_1035811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301427 ⟨1035811, by decide⟩ :=
  accepted_of_selected 12 301427 ⟨1035811, by decide⟩ ⟨12, 2, 0, 1035811, 301427, 1429, 65536⟩
    (by decide) selected_cut_38429

theorem unmarked_context_11_75356_1035812 : frontier 10 ⟨1035812, by decide⟩
    (prefixCache 11 75356) (prefixPartial 11 75356) = false := by
  decide +kernel

theorem node_context_11_75356_1035812 : EJMOriginalGlobalDAGData.nodes 10 ⟨1035812, by decide⟩ =
    .split (coordinate 11) (![⟨1035732, by decide⟩,⟨1035763, by decide⟩,⟨1035786, by decide⟩,⟨1035811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75356_1035812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75356 ⟨1035812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75356
    ⟨1035812, by decide⟩ (by decide) (![⟨1035732, by decide⟩,⟨1035763, by decide⟩,⟨1035786, by decide⟩,⟨1035811, by decide⟩]) unmarked_context_11_75356_1035812 node_context_11_75356_1035812
  intro a
  fin_cases a
  · exact context_12_301424_1035732
  · exact context_12_301425_1035763
  · exact context_12_301426_1035786
  · exact context_12_301427_1035811

theorem selected_cut_38430 : selected 9 ⟨1035853, by decide⟩
    (prefixPartial 12 301428) = some ⟨12, 2, 0, 1035853, 301428, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_301428_1035853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301428 ⟨1035853, by decide⟩ :=
  accepted_of_selected 12 301428 ⟨1035853, by decide⟩ ⟨12, 2, 0, 1035853, 301428, 1953, 65536⟩
    (by decide) selected_cut_38430

theorem selected_cut_38431 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 301429) = some ⟨12, 1, 0, 891951, 301429, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301429_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301429 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 301429 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 301429, 1, 65536⟩
    (by decide) selected_cut_38431

theorem selected_cut_38432 : selected 9 ⟨1035879, by decide⟩
    (prefixPartial 12 301430) = some ⟨12, 2, 0, 1035879, 301430, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_301430_1035879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301430 ⟨1035879, by decide⟩ :=
  accepted_of_selected 12 301430 ⟨1035879, by decide⟩ ⟨12, 2, 0, 1035879, 301430, 1609, 65536⟩
    (by decide) selected_cut_38432

theorem selected_cut_38433 : selected 9 ⟨1035907, by decide⟩
    (prefixPartial 12 301431) = some ⟨12, 2, 0, 1035907, 301431, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_301431_1035907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301431 ⟨1035907, by decide⟩ :=
  accepted_of_selected 12 301431 ⟨1035907, by decide⟩ ⟨12, 2, 0, 1035907, 301431, 1565, 65536⟩
    (by decide) selected_cut_38433

theorem unmarked_context_11_75357_1035908 : frontier 10 ⟨1035908, by decide⟩
    (prefixCache 11 75357) (prefixPartial 11 75357) = false := by
  decide +kernel

theorem node_context_11_75357_1035908 : EJMOriginalGlobalDAGData.nodes 10 ⟨1035908, by decide⟩ =
    .split (coordinate 11) (![⟨1035853, by decide⟩,⟨891951, by decide⟩,⟨1035879, by decide⟩,⟨1035907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75357_1035908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75357 ⟨1035908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75357
    ⟨1035908, by decide⟩ (by decide) (![⟨1035853, by decide⟩,⟨891951, by decide⟩,⟨1035879, by decide⟩,⟨1035907, by decide⟩]) unmarked_context_11_75357_1035908 node_context_11_75357_1035908
  intro a
  fin_cases a
  · exact context_12_301428_1035853
  · exact context_12_301429_891951
  · exact context_12_301430_1035879
  · exact context_12_301431_1035907

theorem selected_cut_38434 : selected 9 ⟨1035930, by decide⟩
    (prefixPartial 12 301432) = some ⟨12, 2, 0, 1035930, 301432, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_301432_1035930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301432 ⟨1035930, by decide⟩ :=
  accepted_of_selected 12 301432 ⟨1035930, by decide⟩ ⟨12, 2, 0, 1035930, 301432, 1525, 65536⟩
    (by decide) selected_cut_38434

theorem selected_cut_38435 : selected 9 ⟨1035959, by decide⟩
    (prefixPartial 12 301433) = some ⟨12, 2, 0, 1035959, 301433, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_301433_1035959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301433 ⟨1035959, by decide⟩ :=
  accepted_of_selected 12 301433 ⟨1035959, by decide⟩ ⟨12, 2, 0, 1035959, 301433, 1469, 65536⟩
    (by decide) selected_cut_38435

theorem selected_cut_38436 : selected 9 ⟨1035984, by decide⟩
    (prefixPartial 12 301434) = some ⟨12, 2, 0, 1035984, 301434, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_301434_1035984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301434 ⟨1035984, by decide⟩ :=
  accepted_of_selected 12 301434 ⟨1035984, by decide⟩ ⟨12, 2, 0, 1035984, 301434, 1465, 65536⟩
    (by decide) selected_cut_38436

theorem selected_cut_38437 : selected 9 ⟨1036005, by decide⟩
    (prefixPartial 12 301435) = some ⟨12, 2, 0, 1036005, 301435, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_301435_1036005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301435 ⟨1036005, by decide⟩ :=
  accepted_of_selected 12 301435 ⟨1036005, by decide⟩ ⟨12, 2, 0, 1036005, 301435, 1373, 65536⟩
    (by decide) selected_cut_38437

theorem unmarked_context_11_75358_1036006 : frontier 10 ⟨1036006, by decide⟩
    (prefixCache 11 75358) (prefixPartial 11 75358) = false := by
  decide +kernel

theorem node_context_11_75358_1036006 : EJMOriginalGlobalDAGData.nodes 10 ⟨1036006, by decide⟩ =
    .split (coordinate 11) (![⟨1035930, by decide⟩,⟨1035959, by decide⟩,⟨1035984, by decide⟩,⟨1036005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75358_1036006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75358 ⟨1036006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75358
    ⟨1036006, by decide⟩ (by decide) (![⟨1035930, by decide⟩,⟨1035959, by decide⟩,⟨1035984, by decide⟩,⟨1036005, by decide⟩]) unmarked_context_11_75358_1036006 node_context_11_75358_1036006
  intro a
  fin_cases a
  · exact context_12_301432_1035930
  · exact context_12_301433_1035959
  · exact context_12_301434_1035984
  · exact context_12_301435_1036005

theorem selected_cut_38438 : selected 9 ⟨1036028, by decide⟩
    (prefixPartial 12 301436) = some ⟨12, 2, 0, 1036028, 301436, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_301436_1036028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301436 ⟨1036028, by decide⟩ :=
  accepted_of_selected 12 301436 ⟨1036028, by decide⟩ ⟨12, 2, 0, 1036028, 301436, 1573, 65536⟩
    (by decide) selected_cut_38438

theorem selected_cut_38439 : selected 9 ⟨1036054, by decide⟩
    (prefixPartial 12 301437) = some ⟨12, 2, 0, 1036054, 301437, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_301437_1036054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301437 ⟨1036054, by decide⟩ :=
  accepted_of_selected 12 301437 ⟨1036054, by decide⟩ ⟨12, 2, 0, 1036054, 301437, 1541, 65536⟩
    (by decide) selected_cut_38439

theorem selected_cut_38440 : selected 9 ⟨1036076, by decide⟩
    (prefixPartial 12 301438) = some ⟨12, 2, 0, 1036076, 301438, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_301438_1036076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301438 ⟨1036076, by decide⟩ :=
  accepted_of_selected 12 301438 ⟨1036076, by decide⟩ ⟨12, 2, 0, 1036076, 301438, 1409, 65536⟩
    (by decide) selected_cut_38440

theorem selected_cut_38441 : selected 9 ⟨1036133, by decide⟩
    (prefixPartial 12 301439) = some ⟨12, 2, 0, 1036133, 301439, 597, 65536⟩ := by
  decide +kernel

theorem context_12_301439_1036133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301439 ⟨1036133, by decide⟩ :=
  accepted_of_selected 12 301439 ⟨1036133, by decide⟩ ⟨12, 2, 0, 1036133, 301439, 597, 65536⟩
    (by decide) selected_cut_38441

theorem unmarked_context_11_75359_1036134 : frontier 10 ⟨1036134, by decide⟩
    (prefixCache 11 75359) (prefixPartial 11 75359) = false := by
  decide +kernel

theorem node_context_11_75359_1036134 : EJMOriginalGlobalDAGData.nodes 10 ⟨1036134, by decide⟩ =
    .split (coordinate 11) (![⟨1036028, by decide⟩,⟨1036054, by decide⟩,⟨1036076, by decide⟩,⟨1036133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75359_1036134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75359 ⟨1036134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75359
    ⟨1036134, by decide⟩ (by decide) (![⟨1036028, by decide⟩,⟨1036054, by decide⟩,⟨1036076, by decide⟩,⟨1036133, by decide⟩]) unmarked_context_11_75359_1036134 node_context_11_75359_1036134
  intro a
  fin_cases a
  · exact context_12_301436_1036028
  · exact context_12_301437_1036054
  · exact context_12_301438_1036076
  · exact context_12_301439_1036133

theorem unmarked_context_10_18839_1036135 : frontier 11 ⟨1036135, by decide⟩
    (prefixCache 10 18839) (prefixPartial 10 18839) = false := by
  decide +kernel

theorem node_context_10_18839_1036135 : EJMOriginalGlobalDAGData.nodes 11 ⟨1036135, by decide⟩ =
    .split (coordinate 10) (![⟨1035812, by decide⟩,⟨1035908, by decide⟩,⟨1036006, by decide⟩,⟨1036134, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18839_1036135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18839 ⟨1036135, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18839
    ⟨1036135, by decide⟩ (by decide) (![⟨1035812, by decide⟩,⟨1035908, by decide⟩,⟨1036006, by decide⟩,⟨1036134, by decide⟩]) unmarked_context_10_18839_1036135 node_context_10_18839_1036135
  intro a
  fin_cases a
  · exact context_11_75356_1035812
  · exact context_11_75357_1035908
  · exact context_11_75358_1036006
  · exact context_11_75359_1036134

theorem unmarked_context_9_4709_1036136 : frontier 12 ⟨1036136, by decide⟩
    (prefixCache 9 4709) (prefixPartial 9 4709) = false := by
  decide +kernel

theorem node_context_9_4709_1036136 : EJMOriginalGlobalDAGData.nodes 12 ⟨1036136, by decide⟩ =
    .split (coordinate 9) (![⟨1035415, by decide⟩,⟨893098, by decide⟩,⟨1035707, by decide⟩,⟨1036135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4709_1036136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4709 ⟨1036136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4709
    ⟨1036136, by decide⟩ (by decide) (![⟨1035415, by decide⟩,⟨893098, by decide⟩,⟨1035707, by decide⟩,⟨1036135, by decide⟩]) unmarked_context_9_4709_1036136 node_context_9_4709_1036136
  intro a
  fin_cases a
  · exact context_10_18836_1035415
  · exact context_10_18837_893098
  · exact context_10_18838_1035707
  · exact context_10_18839_1036135

theorem selected_cut_38442 : selected 10 ⟨1036212, by decide⟩
    (prefixPartial 11 75360) = some ⟨11, 2, 0, 1036212, 75360, 3109, 262144⟩ := by
  decide +kernel

theorem context_11_75360_1036212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75360 ⟨1036212, by decide⟩ :=
  accepted_of_selected 11 75360 ⟨1036212, by decide⟩ ⟨11, 2, 0, 1036212, 75360, 3109, 262144⟩
    (by decide) selected_cut_38442

theorem selected_cut_38443 : selected 10 ⟨1036295, by decide⟩
    (prefixPartial 11 75361) = some ⟨11, 2, 0, 1036295, 75361, 3217, 262144⟩ := by
  decide +kernel

theorem context_11_75361_1036295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75361 ⟨1036295, by decide⟩ :=
  accepted_of_selected 11 75361 ⟨1036295, by decide⟩ ⟨11, 2, 0, 1036295, 75361, 3217, 262144⟩
    (by decide) selected_cut_38443

theorem selected_cut_38444 : selected 10 ⟨1036363, by decide⟩
    (prefixPartial 11 75362) = some ⟨11, 2, 0, 1036363, 75362, 3937, 262144⟩ := by
  decide +kernel

theorem context_11_75362_1036363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75362 ⟨1036363, by decide⟩ :=
  accepted_of_selected 11 75362 ⟨1036363, by decide⟩ ⟨11, 2, 0, 1036363, 75362, 3937, 262144⟩
    (by decide) selected_cut_38444

theorem selected_cut_38445 : selected 10 ⟨1036433, by decide⟩
    (prefixPartial 11 75363) = some ⟨11, 2, 0, 1036433, 75363, 3689, 262144⟩ := by
  decide +kernel

theorem context_11_75363_1036433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75363 ⟨1036433, by decide⟩ :=
  accepted_of_selected 11 75363 ⟨1036433, by decide⟩ ⟨11, 2, 0, 1036433, 75363, 3689, 262144⟩
    (by decide) selected_cut_38445

theorem unmarked_context_10_18840_1036434 : frontier 11 ⟨1036434, by decide⟩
    (prefixCache 10 18840) (prefixPartial 10 18840) = false := by
  decide +kernel

theorem node_context_10_18840_1036434 : EJMOriginalGlobalDAGData.nodes 11 ⟨1036434, by decide⟩ =
    .split (coordinate 10) (![⟨1036212, by decide⟩,⟨1036295, by decide⟩,⟨1036363, by decide⟩,⟨1036433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18840_1036434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18840 ⟨1036434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18840
    ⟨1036434, by decide⟩ (by decide) (![⟨1036212, by decide⟩,⟨1036295, by decide⟩,⟨1036363, by decide⟩,⟨1036433, by decide⟩]) unmarked_context_10_18840_1036434 node_context_10_18840_1036434
  intro a
  fin_cases a
  · exact context_11_75360_1036212
  · exact context_11_75361_1036295
  · exact context_11_75362_1036363
  · exact context_11_75363_1036433

theorem selected_cut_38446 : selected 10 ⟨1036481, by decide⟩
    (prefixPartial 11 75364) = some ⟨11, 2, 0, 1036481, 75364, 2653, 262144⟩ := by
  decide +kernel

theorem context_11_75364_1036481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75364 ⟨1036481, by decide⟩ :=
  accepted_of_selected 11 75364 ⟨1036481, by decide⟩ ⟨11, 2, 0, 1036481, 75364, 2653, 262144⟩
    (by decide) selected_cut_38446

theorem selected_cut_38447 : selected 10 ⟨1036516, by decide⟩
    (prefixPartial 11 75365) = some ⟨11, 2, 0, 1036516, 75365, 1845, 262144⟩ := by
  decide +kernel

theorem context_11_75365_1036516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75365 ⟨1036516, by decide⟩ :=
  accepted_of_selected 11 75365 ⟨1036516, by decide⟩ ⟨11, 2, 0, 1036516, 75365, 1845, 262144⟩
    (by decide) selected_cut_38447

theorem selected_cut_38448 : selected 10 ⟨1036554, by decide⟩
    (prefixPartial 11 75366) = some ⟨11, 2, 0, 1036554, 75366, 2469, 262144⟩ := by
  decide +kernel

theorem context_11_75366_1036554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75366 ⟨1036554, by decide⟩ :=
  accepted_of_selected 11 75366 ⟨1036554, by decide⟩ ⟨11, 2, 0, 1036554, 75366, 2469, 262144⟩
    (by decide) selected_cut_38448

theorem selected_cut_38449 : selected 10 ⟨1036595, by decide⟩
    (prefixPartial 11 75367) = some ⟨11, 2, 0, 1036595, 75367, 2393, 262144⟩ := by
  decide +kernel

theorem context_11_75367_1036595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75367 ⟨1036595, by decide⟩ :=
  accepted_of_selected 11 75367 ⟨1036595, by decide⟩ ⟨11, 2, 0, 1036595, 75367, 2393, 262144⟩
    (by decide) selected_cut_38449

theorem unmarked_context_10_18841_1036596 : frontier 11 ⟨1036596, by decide⟩
    (prefixCache 10 18841) (prefixPartial 10 18841) = false := by
  decide +kernel

theorem node_context_10_18841_1036596 : EJMOriginalGlobalDAGData.nodes 11 ⟨1036596, by decide⟩ =
    .split (coordinate 10) (![⟨1036481, by decide⟩,⟨1036516, by decide⟩,⟨1036554, by decide⟩,⟨1036595, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18841_1036596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18841 ⟨1036596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18841
    ⟨1036596, by decide⟩ (by decide) (![⟨1036481, by decide⟩,⟨1036516, by decide⟩,⟨1036554, by decide⟩,⟨1036595, by decide⟩]) unmarked_context_10_18841_1036596 node_context_10_18841_1036596
  intro a
  fin_cases a
  · exact context_11_75364_1036481
  · exact context_11_75365_1036516
  · exact context_11_75366_1036554
  · exact context_11_75367_1036595

theorem selected_cut_38450 : selected 10 ⟨1036632, by decide⟩
    (prefixPartial 11 75368) = some ⟨11, 2, 0, 1036632, 75368, 2229, 262144⟩ := by
  decide +kernel

theorem context_11_75368_1036632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75368 ⟨1036632, by decide⟩ :=
  accepted_of_selected 11 75368 ⟨1036632, by decide⟩ ⟨11, 2, 0, 1036632, 75368, 2229, 262144⟩
    (by decide) selected_cut_38450

theorem selected_cut_38451 : selected 10 ⟨1036661, by decide⟩
    (prefixPartial 11 75369) = some ⟨11, 2, 0, 1036661, 75369, 1641, 262144⟩ := by
  decide +kernel

theorem context_11_75369_1036661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75369 ⟨1036661, by decide⟩ :=
  accepted_of_selected 11 75369 ⟨1036661, by decide⟩ ⟨11, 2, 0, 1036661, 75369, 1641, 262144⟩
    (by decide) selected_cut_38451

theorem selected_cut_38452 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 75370) = some ⟨11, 1, 0, 906566, 75370, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75370_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75370 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 75370 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 75370, 1, 262144⟩
    (by decide) selected_cut_38452

theorem selected_cut_38453 : selected 10 ⟨1036689, by decide⟩
    (prefixPartial 11 75371) = some ⟨11, 2, 0, 1036689, 75371, 2137, 262144⟩ := by
  decide +kernel

theorem context_11_75371_1036689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75371 ⟨1036689, by decide⟩ :=
  accepted_of_selected 11 75371 ⟨1036689, by decide⟩ ⟨11, 2, 0, 1036689, 75371, 2137, 262144⟩
    (by decide) selected_cut_38453

theorem unmarked_context_10_18842_1036690 : frontier 11 ⟨1036690, by decide⟩
    (prefixCache 10 18842) (prefixPartial 10 18842) = false := by
  decide +kernel

theorem node_context_10_18842_1036690 : EJMOriginalGlobalDAGData.nodes 11 ⟨1036690, by decide⟩ =
    .split (coordinate 10) (![⟨1036632, by decide⟩,⟨1036661, by decide⟩,⟨906566, by decide⟩,⟨1036689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18842_1036690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18842 ⟨1036690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18842
    ⟨1036690, by decide⟩ (by decide) (![⟨1036632, by decide⟩,⟨1036661, by decide⟩,⟨906566, by decide⟩,⟨1036689, by decide⟩]) unmarked_context_10_18842_1036690 node_context_10_18842_1036690
  intro a
  fin_cases a
  · exact context_11_75368_1036632
  · exact context_11_75369_1036661
  · exact context_11_75370_906566
  · exact context_11_75371_1036689

theorem selected_cut_38454 : selected 10 ⟨1036734, by decide⟩
    (prefixPartial 11 75372) = some ⟨11, 2, 0, 1036734, 75372, 2037, 262144⟩ := by
  decide +kernel

theorem context_11_75372_1036734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75372 ⟨1036734, by decide⟩ :=
  accepted_of_selected 11 75372 ⟨1036734, by decide⟩ ⟨11, 2, 0, 1036734, 75372, 2037, 262144⟩
    (by decide) selected_cut_38454

theorem selected_cut_38455 : selected 10 ⟨1036768, by decide⟩
    (prefixPartial 11 75373) = some ⟨11, 2, 0, 1036768, 75373, 1321, 262144⟩ := by
  decide +kernel

theorem context_11_75373_1036768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75373 ⟨1036768, by decide⟩ :=
  accepted_of_selected 11 75373 ⟨1036768, by decide⟩ ⟨11, 2, 0, 1036768, 75373, 1321, 262144⟩
    (by decide) selected_cut_38455

theorem selected_cut_38456 : selected 10 ⟨1036796, by decide⟩
    (prefixPartial 11 75374) = some ⟨11, 2, 0, 1036796, 75374, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_75374_1036796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75374 ⟨1036796, by decide⟩ :=
  accepted_of_selected 11 75374 ⟨1036796, by decide⟩ ⟨11, 2, 0, 1036796, 75374, 1685, 262144⟩
    (by decide) selected_cut_38456

theorem selected_cut_38457 : selected 10 ⟨1036821, by decide⟩
    (prefixPartial 11 75375) = some ⟨11, 2, 0, 1036821, 75375, 1205, 262144⟩ := by
  decide +kernel

theorem context_11_75375_1036821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75375 ⟨1036821, by decide⟩ :=
  accepted_of_selected 11 75375 ⟨1036821, by decide⟩ ⟨11, 2, 0, 1036821, 75375, 1205, 262144⟩
    (by decide) selected_cut_38457

theorem unmarked_context_10_18843_1036822 : frontier 11 ⟨1036822, by decide⟩
    (prefixCache 10 18843) (prefixPartial 10 18843) = false := by
  decide +kernel

theorem node_context_10_18843_1036822 : EJMOriginalGlobalDAGData.nodes 11 ⟨1036822, by decide⟩ =
    .split (coordinate 10) (![⟨1036734, by decide⟩,⟨1036768, by decide⟩,⟨1036796, by decide⟩,⟨1036821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18843_1036822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18843 ⟨1036822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18843
    ⟨1036822, by decide⟩ (by decide) (![⟨1036734, by decide⟩,⟨1036768, by decide⟩,⟨1036796, by decide⟩,⟨1036821, by decide⟩]) unmarked_context_10_18843_1036822 node_context_10_18843_1036822
  intro a
  fin_cases a
  · exact context_11_75372_1036734
  · exact context_11_75373_1036768
  · exact context_11_75374_1036796
  · exact context_11_75375_1036821

theorem unmarked_context_9_4710_1036823 : frontier 12 ⟨1036823, by decide⟩
    (prefixCache 9 4710) (prefixPartial 9 4710) = false := by
  decide +kernel

theorem node_context_9_4710_1036823 : EJMOriginalGlobalDAGData.nodes 12 ⟨1036823, by decide⟩ =
    .split (coordinate 9) (![⟨1036434, by decide⟩,⟨1036596, by decide⟩,⟨1036690, by decide⟩,⟨1036822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4710_1036823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4710 ⟨1036823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4710
    ⟨1036823, by decide⟩ (by decide) (![⟨1036434, by decide⟩,⟨1036596, by decide⟩,⟨1036690, by decide⟩,⟨1036822, by decide⟩]) unmarked_context_9_4710_1036823 node_context_9_4710_1036823
  intro a
  fin_cases a
  · exact context_10_18840_1036434
  · exact context_10_18841_1036596
  · exact context_10_18842_1036690
  · exact context_10_18843_1036822

theorem selected_cut_38458 : selected 10 ⟨1036866, by decide⟩
    (prefixPartial 11 75376) = some ⟨11, 2, 0, 1036866, 75376, 2557, 262144⟩ := by
  decide +kernel

theorem context_11_75376_1036866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75376 ⟨1036866, by decide⟩ :=
  accepted_of_selected 11 75376 ⟨1036866, by decide⟩ ⟨11, 2, 0, 1036866, 75376, 2557, 262144⟩
    (by decide) selected_cut_38458

theorem selected_cut_38459 : selected 10 ⟨1036906, by decide⟩
    (prefixPartial 11 75377) = some ⟨11, 2, 0, 1036906, 75377, 1841, 262144⟩ := by
  decide +kernel

theorem context_11_75377_1036906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75377 ⟨1036906, by decide⟩ :=
  accepted_of_selected 11 75377 ⟨1036906, by decide⟩ ⟨11, 2, 0, 1036906, 75377, 1841, 262144⟩
    (by decide) selected_cut_38459

theorem selected_cut_38460 : selected 10 ⟨1036942, by decide⟩
    (prefixPartial 11 75378) = some ⟨11, 2, 0, 1036942, 75378, 2181, 262144⟩ := by
  decide +kernel

theorem context_11_75378_1036942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75378 ⟨1036942, by decide⟩ :=
  accepted_of_selected 11 75378 ⟨1036942, by decide⟩ ⟨11, 2, 0, 1036942, 75378, 2181, 262144⟩
    (by decide) selected_cut_38460

theorem selected_cut_38461 : selected 10 ⟨1036994, by decide⟩
    (prefixPartial 11 75379) = some ⟨11, 2, 0, 1036994, 75379, 2021, 262144⟩ := by
  decide +kernel

theorem context_11_75379_1036994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75379 ⟨1036994, by decide⟩ :=
  accepted_of_selected 11 75379 ⟨1036994, by decide⟩ ⟨11, 2, 0, 1036994, 75379, 2021, 262144⟩
    (by decide) selected_cut_38461

theorem unmarked_context_10_18844_1036995 : frontier 11 ⟨1036995, by decide⟩
    (prefixCache 10 18844) (prefixPartial 10 18844) = false := by
  decide +kernel

theorem node_context_10_18844_1036995 : EJMOriginalGlobalDAGData.nodes 11 ⟨1036995, by decide⟩ =
    .split (coordinate 10) (![⟨1036866, by decide⟩,⟨1036906, by decide⟩,⟨1036942, by decide⟩,⟨1036994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18844_1036995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18844 ⟨1036995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18844
    ⟨1036995, by decide⟩ (by decide) (![⟨1036866, by decide⟩,⟨1036906, by decide⟩,⟨1036942, by decide⟩,⟨1036994, by decide⟩]) unmarked_context_10_18844_1036995 node_context_10_18844_1036995
  intro a
  fin_cases a
  · exact context_11_75376_1036866
  · exact context_11_75377_1036906
  · exact context_11_75378_1036942
  · exact context_11_75379_1036994

theorem selected_cut_38462 : selected 10 ⟨1037019, by decide⟩
    (prefixPartial 11 75380) = some ⟨11, 2, 0, 1037019, 75380, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_75380_1037019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75380 ⟨1037019, by decide⟩ :=
  accepted_of_selected 11 75380 ⟨1037019, by decide⟩ ⟨11, 2, 0, 1037019, 75380, 1449, 262144⟩
    (by decide) selected_cut_38462

theorem selected_cut_38463 : selected 10 ⟨1037040, by decide⟩
    (prefixPartial 11 75381) = some ⟨11, 2, 0, 1037040, 75381, 993, 262144⟩ := by
  decide +kernel

theorem context_11_75381_1037040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75381 ⟨1037040, by decide⟩ :=
  accepted_of_selected 11 75381 ⟨1037040, by decide⟩ ⟨11, 2, 0, 1037040, 75381, 993, 262144⟩
    (by decide) selected_cut_38463

theorem selected_cut_38464 : selected 10 ⟨1037062, by decide⟩
    (prefixPartial 11 75382) = some ⟨11, 2, 0, 1037062, 75382, 1213, 262144⟩ := by
  decide +kernel

theorem context_11_75382_1037062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75382 ⟨1037062, by decide⟩ :=
  accepted_of_selected 11 75382 ⟨1037062, by decide⟩ ⟨11, 2, 0, 1037062, 75382, 1213, 262144⟩
    (by decide) selected_cut_38464

theorem selected_cut_38465 : selected 10 ⟨1037086, by decide⟩
    (prefixPartial 11 75383) = some ⟨11, 2, 0, 1037086, 75383, 917, 262144⟩ := by
  decide +kernel

theorem context_11_75383_1037086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75383 ⟨1037086, by decide⟩ :=
  accepted_of_selected 11 75383 ⟨1037086, by decide⟩ ⟨11, 2, 0, 1037086, 75383, 917, 262144⟩
    (by decide) selected_cut_38465

theorem unmarked_context_10_18845_1037087 : frontier 11 ⟨1037087, by decide⟩
    (prefixCache 10 18845) (prefixPartial 10 18845) = false := by
  decide +kernel

theorem node_context_10_18845_1037087 : EJMOriginalGlobalDAGData.nodes 11 ⟨1037087, by decide⟩ =
    .split (coordinate 10) (![⟨1037019, by decide⟩,⟨1037040, by decide⟩,⟨1037062, by decide⟩,⟨1037086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18845_1037087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18845 ⟨1037087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18845
    ⟨1037087, by decide⟩ (by decide) (![⟨1037019, by decide⟩,⟨1037040, by decide⟩,⟨1037062, by decide⟩,⟨1037086, by decide⟩]) unmarked_context_10_18845_1037087 node_context_10_18845_1037087
  intro a
  fin_cases a
  · exact context_11_75380_1037019
  · exact context_11_75381_1037040
  · exact context_11_75382_1037062
  · exact context_11_75383_1037086

theorem selected_cut_38466 : selected 11 ⟨1037152, by decide⟩
    (prefixPartial 10 18846) = some ⟨10, 2, 0, 1037152, 18846, 1921, 1048576⟩ := by
  decide +kernel

theorem context_10_18846_1037152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18846 ⟨1037152, by decide⟩ :=
  accepted_of_selected 10 18846 ⟨1037152, by decide⟩ ⟨10, 2, 0, 1037152, 18846, 1921, 1048576⟩
    (by decide) selected_cut_38466

theorem selected_cut_38467 : selected 11 ⟨1037193, by decide⟩
    (prefixPartial 10 18847) = some ⟨10, 2, 0, 1037193, 18847, 713, 1048576⟩ := by
  decide +kernel

theorem context_10_18847_1037193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18847 ⟨1037193, by decide⟩ :=
  accepted_of_selected 10 18847 ⟨1037193, by decide⟩ ⟨10, 2, 0, 1037193, 18847, 713, 1048576⟩
    (by decide) selected_cut_38467

theorem unmarked_context_9_4711_1037194 : frontier 12 ⟨1037194, by decide⟩
    (prefixCache 9 4711) (prefixPartial 9 4711) = false := by
  decide +kernel

theorem node_context_9_4711_1037194 : EJMOriginalGlobalDAGData.nodes 12 ⟨1037194, by decide⟩ =
    .split (coordinate 9) (![⟨1036995, by decide⟩,⟨1037087, by decide⟩,⟨1037152, by decide⟩,⟨1037193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4711_1037194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4711 ⟨1037194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4711
    ⟨1037194, by decide⟩ (by decide) (![⟨1036995, by decide⟩,⟨1037087, by decide⟩,⟨1037152, by decide⟩,⟨1037193, by decide⟩]) unmarked_context_9_4711_1037194 node_context_9_4711_1037194
  intro a
  fin_cases a
  · exact context_10_18844_1036995
  · exact context_10_18845_1037087
  · exact context_10_18846_1037152
  · exact context_10_18847_1037193

theorem unmarked_context_8_1177_1037195 : frontier 13 ⟨1037195, by decide⟩
    (prefixCache 8 1177) (prefixPartial 8 1177) = false := by
  decide +kernel

theorem node_context_8_1177_1037195 : EJMOriginalGlobalDAGData.nodes 13 ⟨1037195, by decide⟩ =
    .split (coordinate 8) (![⟨1034761, by decide⟩,⟨1036136, by decide⟩,⟨1036823, by decide⟩,⟨1037194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1177_1037195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1177 ⟨1037195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1177
    ⟨1037195, by decide⟩ (by decide) (![⟨1034761, by decide⟩,⟨1036136, by decide⟩,⟨1036823, by decide⟩,⟨1037194, by decide⟩]) unmarked_context_8_1177_1037195 node_context_8_1177_1037195
  intro a
  fin_cases a
  · exact context_9_4708_1034761
  · exact context_9_4709_1036136
  · exact context_9_4710_1036823
  · exact context_9_4711_1037194

theorem selected_cut_38468 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 301568) = some ⟨12, 1, 0, 34034, 301568, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301568_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301568 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 301568 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 301568, 1, 65536⟩
    (by decide) selected_cut_38468

theorem selected_cut_38469 : selected 9 ⟨1037280, by decide⟩
    (prefixPartial 12 301569) = some ⟨12, 2, 0, 1037280, 301569, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_301569_1037280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301569 ⟨1037280, by decide⟩ :=
  accepted_of_selected 12 301569 ⟨1037280, by decide⟩ ⟨12, 2, 0, 1037280, 301569, 2421, 65536⟩
    (by decide) selected_cut_38469

theorem selected_cut_38470 : selected 9 ⟨1027489, by decide⟩
    (prefixPartial 12 301570) = some ⟨12, 1, 0, 1027489, 301570, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301570_1027489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301570 ⟨1027489, by decide⟩ :=
  accepted_of_selected 12 301570 ⟨1027489, by decide⟩ ⟨12, 1, 0, 1027489, 301570, 1, 65536⟩
    (by decide) selected_cut_38470

theorem selected_cut_38471 : selected 9 ⟨1037356, by decide⟩
    (prefixPartial 12 301571) = some ⟨12, 2, 0, 1037356, 301571, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_301571_1037356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301571 ⟨1037356, by decide⟩ :=
  accepted_of_selected 12 301571 ⟨1037356, by decide⟩ ⟨12, 2, 0, 1037356, 301571, 3909, 65536⟩
    (by decide) selected_cut_38471

theorem unmarked_context_11_75392_1037357 : frontier 10 ⟨1037357, by decide⟩
    (prefixCache 11 75392) (prefixPartial 11 75392) = false := by
  decide +kernel

theorem node_context_11_75392_1037357 : EJMOriginalGlobalDAGData.nodes 10 ⟨1037357, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1037280, by decide⟩,⟨1027489, by decide⟩,⟨1037356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75392_1037357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75392 ⟨1037357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75392
    ⟨1037357, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1037280, by decide⟩,⟨1027489, by decide⟩,⟨1037356, by decide⟩]) unmarked_context_11_75392_1037357 node_context_11_75392_1037357
  intro a
  fin_cases a
  · exact context_12_301568_34034
  · exact context_12_301569_1037280
  · exact context_12_301570_1027489
  · exact context_12_301571_1037356

theorem selected_cut_38472 : selected 8 ⟨1037387, by decide⟩
    (prefixPartial 13 1206288) = some ⟨13, 2, 0, 1037387, 1206288, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_1206288_1037387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206288 ⟨1037387, by decide⟩ :=
  accepted_of_selected 13 1206288 ⟨1037387, by decide⟩ ⟨13, 2, 0, 1037387, 1206288, 1353, 16384⟩
    (by decide) selected_cut_38472

theorem selected_cut_38473 : selected 8 ⟨1037411, by decide⟩
    (prefixPartial 13 1206289) = some ⟨13, 2, 0, 1037411, 1206289, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_1206289_1037411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206289 ⟨1037411, by decide⟩ :=
  accepted_of_selected 13 1206289 ⟨1037411, by decide⟩ ⟨13, 2, 0, 1037411, 1206289, 1233, 16384⟩
    (by decide) selected_cut_38473

theorem selected_cut_38474 : selected 8 ⟨1037433, by decide⟩
    (prefixPartial 13 1206290) = some ⟨13, 2, 0, 1037433, 1206290, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_1206290_1037433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206290 ⟨1037433, by decide⟩ :=
  accepted_of_selected 13 1206290 ⟨1037433, by decide⟩ ⟨13, 2, 0, 1037433, 1206290, 1037, 16384⟩
    (by decide) selected_cut_38474

theorem selected_cut_38475 : selected 8 ⟨1037450, by decide⟩
    (prefixPartial 13 1206291) = some ⟨13, 2, 0, 1037450, 1206291, 789, 16384⟩ := by
  decide +kernel

theorem context_13_1206291_1037450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206291 ⟨1037450, by decide⟩ :=
  accepted_of_selected 13 1206291 ⟨1037450, by decide⟩ ⟨13, 2, 0, 1037450, 1206291, 789, 16384⟩
    (by decide) selected_cut_38475

theorem unmarked_context_12_301572_1037451 : frontier 9 ⟨1037451, by decide⟩
    (prefixCache 12 301572) (prefixPartial 12 301572) = false := by
  decide +kernel

theorem node_context_12_301572_1037451 : EJMOriginalGlobalDAGData.nodes 9 ⟨1037451, by decide⟩ =
    .split (coordinate 12) (![⟨1037387, by decide⟩,⟨1037411, by decide⟩,⟨1037433, by decide⟩,⟨1037450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301572_1037451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301572 ⟨1037451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301572
    ⟨1037451, by decide⟩ (by decide) (![⟨1037387, by decide⟩,⟨1037411, by decide⟩,⟨1037433, by decide⟩,⟨1037450, by decide⟩]) unmarked_context_12_301572_1037451 node_context_12_301572_1037451
  intro a
  fin_cases a
  · exact context_13_1206288_1037387
  · exact context_13_1206289_1037411
  · exact context_13_1206290_1037433
  · exact context_13_1206291_1037450

theorem selected_cut_38476 : selected 8 ⟨1037494, by decide⟩
    (prefixPartial 13 1206292) = some ⟨13, 2, 0, 1037494, 1206292, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_1206292_1037494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206292 ⟨1037494, by decide⟩ :=
  accepted_of_selected 13 1206292 ⟨1037494, by decide⟩ ⟨13, 2, 0, 1037494, 1206292, 1885, 16384⟩
    (by decide) selected_cut_38476

theorem selected_cut_38477 : selected 8 ⟨1037520, by decide⟩
    (prefixPartial 13 1206293) = some ⟨13, 2, 0, 1037520, 1206293, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_1206293_1037520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206293 ⟨1037520, by decide⟩ :=
  accepted_of_selected 13 1206293 ⟨1037520, by decide⟩ ⟨13, 2, 0, 1037520, 1206293, 1161, 16384⟩
    (by decide) selected_cut_38477

theorem selected_cut_38478 : selected 8 ⟨1037543, by decide⟩
    (prefixPartial 13 1206294) = some ⟨13, 2, 0, 1037543, 1206294, 893, 16384⟩ := by
  decide +kernel

theorem context_13_1206294_1037543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206294 ⟨1037543, by decide⟩ :=
  accepted_of_selected 13 1206294 ⟨1037543, by decide⟩ ⟨13, 2, 0, 1037543, 1206294, 893, 16384⟩
    (by decide) selected_cut_38478

theorem selected_cut_38479 : selected 8 ⟨1037559, by decide⟩
    (prefixPartial 13 1206295) = some ⟨13, 2, 0, 1037559, 1206295, 813, 16384⟩ := by
  decide +kernel

theorem context_13_1206295_1037559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206295 ⟨1037559, by decide⟩ :=
  accepted_of_selected 13 1206295 ⟨1037559, by decide⟩ ⟨13, 2, 0, 1037559, 1206295, 813, 16384⟩
    (by decide) selected_cut_38479

theorem unmarked_context_12_301573_1037560 : frontier 9 ⟨1037560, by decide⟩
    (prefixCache 12 301573) (prefixPartial 12 301573) = false := by
  decide +kernel

theorem node_context_12_301573_1037560 : EJMOriginalGlobalDAGData.nodes 9 ⟨1037560, by decide⟩ =
    .split (coordinate 12) (![⟨1037494, by decide⟩,⟨1037520, by decide⟩,⟨1037543, by decide⟩,⟨1037559, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301573_1037560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301573 ⟨1037560, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301573
    ⟨1037560, by decide⟩ (by decide) (![⟨1037494, by decide⟩,⟨1037520, by decide⟩,⟨1037543, by decide⟩,⟨1037559, by decide⟩]) unmarked_context_12_301573_1037560 node_context_12_301573_1037560
  intro a
  fin_cases a
  · exact context_13_1206292_1037494
  · exact context_13_1206293_1037520
  · exact context_13_1206294_1037543
  · exact context_13_1206295_1037559

theorem selected_cut_38480 : selected 9 ⟨1037635, by decide⟩
    (prefixPartial 12 301574) = some ⟨12, 2, 0, 1037635, 301574, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_301574_1037635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301574 ⟨1037635, by decide⟩ :=
  accepted_of_selected 12 301574 ⟨1037635, by decide⟩ ⟨12, 2, 0, 1037635, 301574, 3961, 65536⟩
    (by decide) selected_cut_38480

theorem selected_cut_38481 : selected 8 ⟨1037675, by decide⟩
    (prefixPartial 13 1206300) = some ⟨13, 2, 0, 1037675, 1206300, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_1206300_1037675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206300 ⟨1037675, by decide⟩ :=
  accepted_of_selected 13 1206300 ⟨1037675, by decide⟩ ⟨13, 2, 0, 1037675, 1206300, 1693, 16384⟩
    (by decide) selected_cut_38481

theorem selected_cut_38482 : selected 8 ⟨1037692, by decide⟩
    (prefixPartial 13 1206301) = some ⟨13, 2, 0, 1037692, 1206301, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_1206301_1037692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206301 ⟨1037692, by decide⟩ :=
  accepted_of_selected 13 1206301 ⟨1037692, by decide⟩ ⟨13, 2, 0, 1037692, 1206301, 1037, 16384⟩
    (by decide) selected_cut_38482

theorem selected_cut_38483 : selected 8 ⟨1037712, by decide⟩
    (prefixPartial 13 1206302) = some ⟨13, 2, 0, 1037712, 1206302, 973, 16384⟩ := by
  decide +kernel

theorem context_13_1206302_1037712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206302 ⟨1037712, by decide⟩ :=
  accepted_of_selected 13 1206302 ⟨1037712, by decide⟩ ⟨13, 2, 0, 1037712, 1206302, 973, 16384⟩
    (by decide) selected_cut_38483

theorem selected_cut_38484 : selected 8 ⟨1037721, by decide⟩
    (prefixPartial 13 1206303) = some ⟨13, 2, 0, 1037721, 1206303, 701, 16384⟩ := by
  decide +kernel

theorem context_13_1206303_1037721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206303 ⟨1037721, by decide⟩ :=
  accepted_of_selected 13 1206303 ⟨1037721, by decide⟩ ⟨13, 2, 0, 1037721, 1206303, 701, 16384⟩
    (by decide) selected_cut_38484

theorem unmarked_context_12_301575_1037722 : frontier 9 ⟨1037722, by decide⟩
    (prefixCache 12 301575) (prefixPartial 12 301575) = false := by
  decide +kernel

theorem node_context_12_301575_1037722 : EJMOriginalGlobalDAGData.nodes 9 ⟨1037722, by decide⟩ =
    .split (coordinate 12) (![⟨1037675, by decide⟩,⟨1037692, by decide⟩,⟨1037712, by decide⟩,⟨1037721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301575_1037722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301575 ⟨1037722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301575
    ⟨1037722, by decide⟩ (by decide) (![⟨1037675, by decide⟩,⟨1037692, by decide⟩,⟨1037712, by decide⟩,⟨1037721, by decide⟩]) unmarked_context_12_301575_1037722 node_context_12_301575_1037722
  intro a
  fin_cases a
  · exact context_13_1206300_1037675
  · exact context_13_1206301_1037692
  · exact context_13_1206302_1037712
  · exact context_13_1206303_1037721

theorem unmarked_context_11_75393_1037723 : frontier 10 ⟨1037723, by decide⟩
    (prefixCache 11 75393) (prefixPartial 11 75393) = false := by
  decide +kernel

theorem node_context_11_75393_1037723 : EJMOriginalGlobalDAGData.nodes 10 ⟨1037723, by decide⟩ =
    .split (coordinate 11) (![⟨1037451, by decide⟩,⟨1037560, by decide⟩,⟨1037635, by decide⟩,⟨1037722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75393_1037723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75393 ⟨1037723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75393
    ⟨1037723, by decide⟩ (by decide) (![⟨1037451, by decide⟩,⟨1037560, by decide⟩,⟨1037635, by decide⟩,⟨1037722, by decide⟩]) unmarked_context_11_75393_1037723 node_context_11_75393_1037723
  intro a
  fin_cases a
  · exact context_12_301572_1037451
  · exact context_12_301573_1037560
  · exact context_12_301574_1037635
  · exact context_12_301575_1037722

theorem selected_cut_38485 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 301576) = some ⟨12, 1, 0, 450498, 301576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301576_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301576 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 301576 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 301576, 1, 65536⟩
    (by decide) selected_cut_38485

theorem selected_cut_38486 : selected 8 ⟨1037754, by decide⟩
    (prefixPartial 13 1206308) = some ⟨13, 2, 0, 1037754, 1206308, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_1206308_1037754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206308 ⟨1037754, by decide⟩ :=
  accepted_of_selected 13 1206308 ⟨1037754, by decide⟩ ⟨13, 2, 0, 1037754, 1206308, 1501, 16384⟩
    (by decide) selected_cut_38486

theorem selected_cut_38487 : selected 8 ⟨1037782, by decide⟩
    (prefixPartial 13 1206309) = some ⟨13, 2, 0, 1037782, 1206309, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_1206309_1037782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206309 ⟨1037782, by decide⟩ :=
  accepted_of_selected 13 1206309 ⟨1037782, by decide⟩ ⟨13, 2, 0, 1037782, 1206309, 1201, 16384⟩
    (by decide) selected_cut_38487

theorem selected_cut_38488 : selected 8 ⟨1037803, by decide⟩
    (prefixPartial 13 1206310) = some ⟨13, 2, 0, 1037803, 1206310, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_1206310_1037803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206310 ⟨1037803, by decide⟩ :=
  accepted_of_selected 13 1206310 ⟨1037803, by decide⟩ ⟨13, 2, 0, 1037803, 1206310, 1081, 16384⟩
    (by decide) selected_cut_38488

theorem selected_cut_38489 : selected 8 ⟨1037814, by decide⟩
    (prefixPartial 13 1206311) = some ⟨13, 2, 0, 1037814, 1206311, 673, 16384⟩ := by
  decide +kernel

theorem context_13_1206311_1037814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206311 ⟨1037814, by decide⟩ :=
  accepted_of_selected 13 1206311 ⟨1037814, by decide⟩ ⟨13, 2, 0, 1037814, 1206311, 673, 16384⟩
    (by decide) selected_cut_38489

theorem unmarked_context_12_301577_1037815 : frontier 9 ⟨1037815, by decide⟩
    (prefixCache 12 301577) (prefixPartial 12 301577) = false := by
  decide +kernel

theorem node_context_12_301577_1037815 : EJMOriginalGlobalDAGData.nodes 9 ⟨1037815, by decide⟩ =
    .split (coordinate 12) (![⟨1037754, by decide⟩,⟨1037782, by decide⟩,⟨1037803, by decide⟩,⟨1037814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301577_1037815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301577 ⟨1037815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301577
    ⟨1037815, by decide⟩ (by decide) (![⟨1037754, by decide⟩,⟨1037782, by decide⟩,⟨1037803, by decide⟩,⟨1037814, by decide⟩]) unmarked_context_12_301577_1037815 node_context_12_301577_1037815
  intro a
  fin_cases a
  · exact context_13_1206308_1037754
  · exact context_13_1206309_1037782
  · exact context_13_1206310_1037803
  · exact context_13_1206311_1037814

theorem selected_cut_38490 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 301578) = some ⟨12, 1, 0, 893903, 301578, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301578_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301578 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 301578 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 301578, 1, 65536⟩
    (by decide) selected_cut_38490

theorem selected_cut_38491 : selected 8 ⟨1037842, by decide⟩
    (prefixPartial 13 1206316) = some ⟨13, 2, 0, 1037842, 1206316, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_1206316_1037842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206316 ⟨1037842, by decide⟩ :=
  accepted_of_selected 13 1206316 ⟨1037842, by decide⟩ ⟨13, 2, 0, 1037842, 1206316, 1361, 16384⟩
    (by decide) selected_cut_38491

theorem selected_cut_38492 : selected 8 ⟨1037862, by decide⟩
    (prefixPartial 13 1206317) = some ⟨13, 2, 0, 1037862, 1206317, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_1206317_1037862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206317 ⟨1037862, by decide⟩ :=
  accepted_of_selected 13 1206317 ⟨1037862, by decide⟩ ⟨13, 2, 0, 1037862, 1206317, 1189, 16384⟩
    (by decide) selected_cut_38492

theorem selected_cut_38493 : selected 8 ⟨1037882, by decide⟩
    (prefixPartial 13 1206318) = some ⟨13, 2, 0, 1037882, 1206318, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_1206318_1037882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206318 ⟨1037882, by decide⟩ :=
  accepted_of_selected 13 1206318 ⟨1037882, by decide⟩ ⟨13, 2, 0, 1037882, 1206318, 1113, 16384⟩
    (by decide) selected_cut_38493

theorem selected_cut_38494 : selected 8 ⟨1037894, by decide⟩
    (prefixPartial 13 1206319) = some ⟨13, 2, 0, 1037894, 1206319, 697, 16384⟩ := by
  decide +kernel

theorem context_13_1206319_1037894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206319 ⟨1037894, by decide⟩ :=
  accepted_of_selected 13 1206319 ⟨1037894, by decide⟩ ⟨13, 2, 0, 1037894, 1206319, 697, 16384⟩
    (by decide) selected_cut_38494

theorem unmarked_context_12_301579_1037895 : frontier 9 ⟨1037895, by decide⟩
    (prefixCache 12 301579) (prefixPartial 12 301579) = false := by
  decide +kernel

theorem node_context_12_301579_1037895 : EJMOriginalGlobalDAGData.nodes 9 ⟨1037895, by decide⟩ =
    .split (coordinate 12) (![⟨1037842, by decide⟩,⟨1037862, by decide⟩,⟨1037882, by decide⟩,⟨1037894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301579_1037895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301579 ⟨1037895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301579
    ⟨1037895, by decide⟩ (by decide) (![⟨1037842, by decide⟩,⟨1037862, by decide⟩,⟨1037882, by decide⟩,⟨1037894, by decide⟩]) unmarked_context_12_301579_1037895 node_context_12_301579_1037895
  intro a
  fin_cases a
  · exact context_13_1206316_1037842
  · exact context_13_1206317_1037862
  · exact context_13_1206318_1037882
  · exact context_13_1206319_1037894

theorem unmarked_context_11_75394_1037896 : frontier 10 ⟨1037896, by decide⟩
    (prefixCache 11 75394) (prefixPartial 11 75394) = false := by
  decide +kernel

theorem node_context_11_75394_1037896 : EJMOriginalGlobalDAGData.nodes 10 ⟨1037896, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1037815, by decide⟩,⟨893903, by decide⟩,⟨1037895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75394_1037896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75394 ⟨1037896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75394
    ⟨1037896, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1037815, by decide⟩,⟨893903, by decide⟩,⟨1037895, by decide⟩]) unmarked_context_11_75394_1037896 node_context_11_75394_1037896
  intro a
  fin_cases a
  · exact context_12_301576_450498
  · exact context_12_301577_1037815
  · exact context_12_301578_893903
  · exact context_12_301579_1037895

theorem selected_cut_38495 : selected 8 ⟨1037924, by decide⟩
    (prefixPartial 13 1206320) = some ⟨13, 2, 0, 1037924, 1206320, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_1206320_1037924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206320 ⟨1037924, by decide⟩ :=
  accepted_of_selected 13 1206320 ⟨1037924, by decide⟩ ⟨13, 2, 0, 1037924, 1206320, 1257, 16384⟩
    (by decide) selected_cut_38495

theorem selected_cut_38496 : selected 8 ⟨1037953, by decide⟩
    (prefixPartial 13 1206321) = some ⟨13, 2, 0, 1037953, 1206321, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_1206321_1037953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206321 ⟨1037953, by decide⟩ :=
  accepted_of_selected 13 1206321 ⟨1037953, by decide⟩ ⟨13, 2, 0, 1037953, 1206321, 1249, 16384⟩
    (by decide) selected_cut_38496

theorem selected_cut_38497 : selected 8 ⟨1037973, by decide⟩
    (prefixPartial 13 1206322) = some ⟨13, 2, 0, 1037973, 1206322, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_1206322_1037973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206322 ⟨1037973, by decide⟩ :=
  accepted_of_selected 13 1206322 ⟨1037973, by decide⟩ ⟨13, 2, 0, 1037973, 1206322, 1225, 16384⟩
    (by decide) selected_cut_38497

theorem selected_cut_38498 : selected 8 ⟨1037993, by decide⟩
    (prefixPartial 13 1206323) = some ⟨13, 2, 0, 1037993, 1206323, 793, 16384⟩ := by
  decide +kernel

theorem context_13_1206323_1037993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1206323 ⟨1037993, by decide⟩ :=
  accepted_of_selected 13 1206323 ⟨1037993, by decide⟩ ⟨13, 2, 0, 1037993, 1206323, 793, 16384⟩
    (by decide) selected_cut_38498

theorem unmarked_context_12_301580_1037994 : frontier 9 ⟨1037994, by decide⟩
    (prefixCache 12 301580) (prefixPartial 12 301580) = false := by
  decide +kernel

theorem node_context_12_301580_1037994 : EJMOriginalGlobalDAGData.nodes 9 ⟨1037994, by decide⟩ =
    .split (coordinate 12) (![⟨1037924, by decide⟩,⟨1037953, by decide⟩,⟨1037973, by decide⟩,⟨1037993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_301580_1037994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301580 ⟨1037994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 301580
    ⟨1037994, by decide⟩ (by decide) (![⟨1037924, by decide⟩,⟨1037953, by decide⟩,⟨1037973, by decide⟩,⟨1037993, by decide⟩]) unmarked_context_12_301580_1037994 node_context_12_301580_1037994
  intro a
  fin_cases a
  · exact context_13_1206320_1037924
  · exact context_13_1206321_1037953
  · exact context_13_1206322_1037973
  · exact context_13_1206323_1037993

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
