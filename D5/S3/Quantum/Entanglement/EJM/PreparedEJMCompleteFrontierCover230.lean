/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover229
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_22083 : selected 9 ⟨563023, by decide⟩
    (prefixPartial 12 75426) = some ⟨12, 2, 0, 563023, 75426, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_75426_563023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75426 ⟨563023, by decide⟩ :=
  accepted_of_selected 12 75426 ⟨563023, by decide⟩ ⟨12, 2, 0, 563023, 75426, 1381, 65536⟩
    (by decide) selected_cut_22083

theorem selected_cut_22084 : selected 9 ⟨563037, by decide⟩
    (prefixPartial 12 75427) = some ⟨12, 2, 0, 563037, 75427, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_75427_563037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75427 ⟨563037, by decide⟩ :=
  accepted_of_selected 12 75427 ⟨563037, by decide⟩ ⟨12, 2, 0, 563037, 75427, 1493, 65536⟩
    (by decide) selected_cut_22084

theorem unmarked_context_11_18856_563038 : frontier 10 ⟨563038, by decide⟩
    (prefixCache 11 18856) (prefixPartial 11 18856) = false := by
  decide +kernel

theorem node_context_11_18856_563038 : EJMOriginalGlobalDAGData.nodes 10 ⟨563038, by decide⟩ =
    .split (coordinate 11) (![⟨562998, by decide⟩,⟨563011, by decide⟩,⟨563023, by decide⟩,⟨563037, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18856_563038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18856 ⟨563038, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18856
    ⟨563038, by decide⟩ (by decide) (![⟨562998, by decide⟩,⟨563011, by decide⟩,⟨563023, by decide⟩,⟨563037, by decide⟩]) unmarked_context_11_18856_563038 node_context_11_18856_563038
  intro a
  fin_cases a
  · exact context_12_75424_562998
  · exact context_12_75425_563011
  · exact context_12_75426_563023
  · exact context_12_75427_563037

theorem selected_cut_22085 : selected 9 ⟨563056, by decide⟩
    (prefixPartial 12 75428) = some ⟨12, 2, 0, 563056, 75428, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_75428_563056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75428 ⟨563056, by decide⟩ :=
  accepted_of_selected 12 75428 ⟨563056, by decide⟩ ⟨12, 2, 0, 563056, 75428, 1585, 65536⟩
    (by decide) selected_cut_22085

theorem selected_cut_22086 : selected 9 ⟨563069, by decide⟩
    (prefixPartial 12 75429) = some ⟨12, 2, 0, 563069, 75429, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_75429_563069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75429 ⟨563069, by decide⟩ :=
  accepted_of_selected 12 75429 ⟨563069, by decide⟩ ⟨12, 2, 0, 563069, 75429, 1477, 65536⟩
    (by decide) selected_cut_22086

theorem selected_cut_22087 : selected 9 ⟨563087, by decide⟩
    (prefixPartial 12 75430) = some ⟨12, 2, 0, 563087, 75430, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_75430_563087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75430 ⟨563087, by decide⟩ :=
  accepted_of_selected 12 75430 ⟨563087, by decide⟩ ⟨12, 2, 0, 563087, 75430, 1573, 65536⟩
    (by decide) selected_cut_22087

theorem selected_cut_22088 : selected 9 ⟨563106, by decide⟩
    (prefixPartial 12 75431) = some ⟨12, 2, 0, 563106, 75431, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_75431_563106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75431 ⟨563106, by decide⟩ :=
  accepted_of_selected 12 75431 ⟨563106, by decide⟩ ⟨12, 2, 0, 563106, 75431, 1717, 65536⟩
    (by decide) selected_cut_22088

theorem unmarked_context_11_18857_563107 : frontier 10 ⟨563107, by decide⟩
    (prefixCache 11 18857) (prefixPartial 11 18857) = false := by
  decide +kernel

theorem node_context_11_18857_563107 : EJMOriginalGlobalDAGData.nodes 10 ⟨563107, by decide⟩ =
    .split (coordinate 11) (![⟨563056, by decide⟩,⟨563069, by decide⟩,⟨563087, by decide⟩,⟨563106, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18857_563107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18857 ⟨563107, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18857
    ⟨563107, by decide⟩ (by decide) (![⟨563056, by decide⟩,⟨563069, by decide⟩,⟨563087, by decide⟩,⟨563106, by decide⟩]) unmarked_context_11_18857_563107 node_context_11_18857_563107
  intro a
  fin_cases a
  · exact context_12_75428_563056
  · exact context_12_75429_563069
  · exact context_12_75430_563087
  · exact context_12_75431_563106

theorem selected_cut_22089 : selected 9 ⟨563122, by decide⟩
    (prefixPartial 12 75432) = some ⟨12, 2, 0, 563122, 75432, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_75432_563122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75432 ⟨563122, by decide⟩ :=
  accepted_of_selected 12 75432 ⟨563122, by decide⟩ ⟨12, 2, 0, 563122, 75432, 1429, 65536⟩
    (by decide) selected_cut_22089

theorem selected_cut_22090 : selected 9 ⟨563137, by decide⟩
    (prefixPartial 12 75433) = some ⟨12, 2, 0, 563137, 75433, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_75433_563137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75433 ⟨563137, by decide⟩ :=
  accepted_of_selected 12 75433 ⟨563137, by decide⟩ ⟨12, 2, 0, 563137, 75433, 1453, 65536⟩
    (by decide) selected_cut_22090

theorem selected_cut_22091 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 75434) = some ⟨12, 1, 0, 445248, 75434, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75434_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75434 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 75434 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 75434, 1, 65536⟩
    (by decide) selected_cut_22091

theorem selected_cut_22092 : selected 9 ⟨563154, by decide⟩
    (prefixPartial 12 75435) = some ⟨12, 2, 0, 563154, 75435, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_75435_563154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75435 ⟨563154, by decide⟩ :=
  accepted_of_selected 12 75435 ⟨563154, by decide⟩ ⟨12, 2, 0, 563154, 75435, 1433, 65536⟩
    (by decide) selected_cut_22092

theorem unmarked_context_11_18858_563155 : frontier 10 ⟨563155, by decide⟩
    (prefixCache 11 18858) (prefixPartial 11 18858) = false := by
  decide +kernel

theorem node_context_11_18858_563155 : EJMOriginalGlobalDAGData.nodes 10 ⟨563155, by decide⟩ =
    .split (coordinate 11) (![⟨563122, by decide⟩,⟨563137, by decide⟩,⟨445248, by decide⟩,⟨563154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18858_563155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18858 ⟨563155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18858
    ⟨563155, by decide⟩ (by decide) (![⟨563122, by decide⟩,⟨563137, by decide⟩,⟨445248, by decide⟩,⟨563154, by decide⟩]) unmarked_context_11_18858_563155 node_context_11_18858_563155
  intro a
  fin_cases a
  · exact context_12_75432_563122
  · exact context_12_75433_563137
  · exact context_12_75434_445248
  · exact context_12_75435_563154

theorem selected_cut_22093 : selected 9 ⟨563171, by decide⟩
    (prefixPartial 12 75436) = some ⟨12, 2, 0, 563171, 75436, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_75436_563171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75436 ⟨563171, by decide⟩ :=
  accepted_of_selected 12 75436 ⟨563171, by decide⟩ ⟨12, 2, 0, 563171, 75436, 1505, 65536⟩
    (by decide) selected_cut_22093

theorem selected_cut_22094 : selected 9 ⟨563181, by decide⟩
    (prefixPartial 12 75437) = some ⟨12, 2, 0, 563181, 75437, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_75437_563181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75437 ⟨563181, by decide⟩ :=
  accepted_of_selected 12 75437 ⟨563181, by decide⟩ ⟨12, 2, 0, 563181, 75437, 1337, 65536⟩
    (by decide) selected_cut_22094

theorem selected_cut_22095 : selected 9 ⟨563193, by decide⟩
    (prefixPartial 12 75438) = some ⟨12, 2, 0, 563193, 75438, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_75438_563193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75438 ⟨563193, by decide⟩ :=
  accepted_of_selected 12 75438 ⟨563193, by decide⟩ ⟨12, 2, 0, 563193, 75438, 1357, 65536⟩
    (by decide) selected_cut_22095

theorem selected_cut_22096 : selected 9 ⟨563210, by decide⟩
    (prefixPartial 12 75439) = some ⟨12, 2, 0, 563210, 75439, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_75439_563210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75439 ⟨563210, by decide⟩ :=
  accepted_of_selected 12 75439 ⟨563210, by decide⟩ ⟨12, 2, 0, 563210, 75439, 1513, 65536⟩
    (by decide) selected_cut_22096

theorem unmarked_context_11_18859_563211 : frontier 10 ⟨563211, by decide⟩
    (prefixCache 11 18859) (prefixPartial 11 18859) = false := by
  decide +kernel

theorem node_context_11_18859_563211 : EJMOriginalGlobalDAGData.nodes 10 ⟨563211, by decide⟩ =
    .split (coordinate 11) (![⟨563171, by decide⟩,⟨563181, by decide⟩,⟨563193, by decide⟩,⟨563210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18859_563211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18859 ⟨563211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18859
    ⟨563211, by decide⟩ (by decide) (![⟨563171, by decide⟩,⟨563181, by decide⟩,⟨563193, by decide⟩,⟨563210, by decide⟩]) unmarked_context_11_18859_563211 node_context_11_18859_563211
  intro a
  fin_cases a
  · exact context_12_75436_563171
  · exact context_12_75437_563181
  · exact context_12_75438_563193
  · exact context_12_75439_563210

theorem unmarked_context_10_4714_563212 : frontier 11 ⟨563212, by decide⟩
    (prefixCache 10 4714) (prefixPartial 10 4714) = false := by
  decide +kernel

theorem node_context_10_4714_563212 : EJMOriginalGlobalDAGData.nodes 11 ⟨563212, by decide⟩ =
    .split (coordinate 10) (![⟨563038, by decide⟩,⟨563107, by decide⟩,⟨563155, by decide⟩,⟨563211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4714_563212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4714 ⟨563212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4714
    ⟨563212, by decide⟩ (by decide) (![⟨563038, by decide⟩,⟨563107, by decide⟩,⟨563155, by decide⟩,⟨563211, by decide⟩]) unmarked_context_10_4714_563212 node_context_10_4714_563212
  intro a
  fin_cases a
  · exact context_11_18856_563038
  · exact context_11_18857_563107
  · exact context_11_18858_563155
  · exact context_11_18859_563211

theorem selected_cut_22097 : selected 9 ⟨563225, by decide⟩
    (prefixPartial 12 75440) = some ⟨12, 2, 0, 563225, 75440, 1041, 65536⟩ := by
  decide +kernel

theorem context_12_75440_563225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75440 ⟨563225, by decide⟩ :=
  accepted_of_selected 12 75440 ⟨563225, by decide⟩ ⟨12, 2, 0, 563225, 75440, 1041, 65536⟩
    (by decide) selected_cut_22097

theorem selected_cut_22098 : selected 9 ⟨563236, by decide⟩
    (prefixPartial 12 75441) = some ⟨12, 2, 0, 563236, 75441, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_75441_563236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75441 ⟨563236, by decide⟩ :=
  accepted_of_selected 12 75441 ⟨563236, by decide⟩ ⟨12, 2, 0, 563236, 75441, 1133, 65536⟩
    (by decide) selected_cut_22098

theorem selected_cut_22099 : selected 9 ⟨563246, by decide⟩
    (prefixPartial 12 75442) = some ⟨12, 2, 0, 563246, 75442, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_75442_563246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75442 ⟨563246, by decide⟩ :=
  accepted_of_selected 12 75442 ⟨563246, by decide⟩ ⟨12, 2, 0, 563246, 75442, 1097, 65536⟩
    (by decide) selected_cut_22099

theorem selected_cut_22100 : selected 9 ⟨563255, by decide⟩
    (prefixPartial 12 75443) = some ⟨12, 2, 0, 563255, 75443, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_75443_563255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75443 ⟨563255, by decide⟩ :=
  accepted_of_selected 12 75443 ⟨563255, by decide⟩ ⟨12, 2, 0, 563255, 75443, 1141, 65536⟩
    (by decide) selected_cut_22100

theorem unmarked_context_11_18860_563256 : frontier 10 ⟨563256, by decide⟩
    (prefixCache 11 18860) (prefixPartial 11 18860) = false := by
  decide +kernel

theorem node_context_11_18860_563256 : EJMOriginalGlobalDAGData.nodes 10 ⟨563256, by decide⟩ =
    .split (coordinate 11) (![⟨563225, by decide⟩,⟨563236, by decide⟩,⟨563246, by decide⟩,⟨563255, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18860_563256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18860 ⟨563256, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18860
    ⟨563256, by decide⟩ (by decide) (![⟨563225, by decide⟩,⟨563236, by decide⟩,⟨563246, by decide⟩,⟨563255, by decide⟩]) unmarked_context_11_18860_563256 node_context_11_18860_563256
  intro a
  fin_cases a
  · exact context_12_75440_563225
  · exact context_12_75441_563236
  · exact context_12_75442_563246
  · exact context_12_75443_563255

theorem selected_cut_22101 : selected 9 ⟨563269, by decide⟩
    (prefixPartial 12 75444) = some ⟨12, 2, 0, 563269, 75444, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_75444_563269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75444 ⟨563269, by decide⟩ :=
  accepted_of_selected 12 75444 ⟨563269, by decide⟩ ⟨12, 2, 0, 563269, 75444, 1141, 65536⟩
    (by decide) selected_cut_22101

theorem selected_cut_22102 : selected 9 ⟨563282, by decide⟩
    (prefixPartial 12 75445) = some ⟨12, 2, 0, 563282, 75445, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_75445_563282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75445 ⟨563282, by decide⟩ :=
  accepted_of_selected 12 75445 ⟨563282, by decide⟩ ⟨12, 2, 0, 563282, 75445, 1145, 65536⟩
    (by decide) selected_cut_22102

theorem selected_cut_22103 : selected 9 ⟨563300, by decide⟩
    (prefixPartial 12 75446) = some ⟨12, 2, 0, 563300, 75446, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_75446_563300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75446 ⟨563300, by decide⟩ :=
  accepted_of_selected 12 75446 ⟨563300, by decide⟩ ⟨12, 2, 0, 563300, 75446, 1237, 65536⟩
    (by decide) selected_cut_22103

theorem selected_cut_22104 : selected 9 ⟨563317, by decide⟩
    (prefixPartial 12 75447) = some ⟨12, 2, 0, 563317, 75447, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_75447_563317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75447 ⟨563317, by decide⟩ :=
  accepted_of_selected 12 75447 ⟨563317, by decide⟩ ⟨12, 2, 0, 563317, 75447, 1237, 65536⟩
    (by decide) selected_cut_22104

theorem unmarked_context_11_18861_563318 : frontier 10 ⟨563318, by decide⟩
    (prefixCache 11 18861) (prefixPartial 11 18861) = false := by
  decide +kernel

theorem node_context_11_18861_563318 : EJMOriginalGlobalDAGData.nodes 10 ⟨563318, by decide⟩ =
    .split (coordinate 11) (![⟨563269, by decide⟩,⟨563282, by decide⟩,⟨563300, by decide⟩,⟨563317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18861_563318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18861 ⟨563318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18861
    ⟨563318, by decide⟩ (by decide) (![⟨563269, by decide⟩,⟨563282, by decide⟩,⟨563300, by decide⟩,⟨563317, by decide⟩]) unmarked_context_11_18861_563318 node_context_11_18861_563318
  intro a
  fin_cases a
  · exact context_12_75444_563269
  · exact context_12_75445_563282
  · exact context_12_75446_563300
  · exact context_12_75447_563317

theorem selected_cut_22105 : selected 10 ⟨563359, by decide⟩
    (prefixPartial 11 18862) = some ⟨11, 2, 0, 563359, 18862, 3389, 262144⟩ := by
  decide +kernel

theorem context_11_18862_563359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18862 ⟨563359, by decide⟩ :=
  accepted_of_selected 11 18862 ⟨563359, by decide⟩ ⟨11, 2, 0, 563359, 18862, 3389, 262144⟩
    (by decide) selected_cut_22105

theorem selected_cut_22106 : selected 9 ⟨563371, by decide⟩
    (prefixPartial 12 75452) = some ⟨12, 2, 0, 563371, 75452, 997, 65536⟩ := by
  decide +kernel

theorem context_12_75452_563371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75452 ⟨563371, by decide⟩ :=
  accepted_of_selected 12 75452 ⟨563371, by decide⟩ ⟨12, 2, 0, 563371, 75452, 997, 65536⟩
    (by decide) selected_cut_22106

theorem selected_cut_22107 : selected 9 ⟨563380, by decide⟩
    (prefixPartial 12 75453) = some ⟨12, 2, 0, 563380, 75453, 981, 65536⟩ := by
  decide +kernel

theorem context_12_75453_563380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75453 ⟨563380, by decide⟩ :=
  accepted_of_selected 12 75453 ⟨563380, by decide⟩ ⟨12, 2, 0, 563380, 75453, 981, 65536⟩
    (by decide) selected_cut_22107

theorem selected_cut_22108 : selected 9 ⟨563396, by decide⟩
    (prefixPartial 12 75454) = some ⟨12, 2, 0, 563396, 75454, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_75454_563396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75454 ⟨563396, by decide⟩ :=
  accepted_of_selected 12 75454 ⟨563396, by decide⟩ ⟨12, 2, 0, 563396, 75454, 1125, 65536⟩
    (by decide) selected_cut_22108

theorem selected_cut_22109 : selected 9 ⟨563406, by decide⟩
    (prefixPartial 12 75455) = some ⟨12, 2, 0, 563406, 75455, 1029, 65536⟩ := by
  decide +kernel

theorem context_12_75455_563406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75455 ⟨563406, by decide⟩ :=
  accepted_of_selected 12 75455 ⟨563406, by decide⟩ ⟨12, 2, 0, 563406, 75455, 1029, 65536⟩
    (by decide) selected_cut_22109

theorem unmarked_context_11_18863_563407 : frontier 10 ⟨563407, by decide⟩
    (prefixCache 11 18863) (prefixPartial 11 18863) = false := by
  decide +kernel

theorem node_context_11_18863_563407 : EJMOriginalGlobalDAGData.nodes 10 ⟨563407, by decide⟩ =
    .split (coordinate 11) (![⟨563371, by decide⟩,⟨563380, by decide⟩,⟨563396, by decide⟩,⟨563406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18863_563407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18863 ⟨563407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18863
    ⟨563407, by decide⟩ (by decide) (![⟨563371, by decide⟩,⟨563380, by decide⟩,⟨563396, by decide⟩,⟨563406, by decide⟩]) unmarked_context_11_18863_563407 node_context_11_18863_563407
  intro a
  fin_cases a
  · exact context_12_75452_563371
  · exact context_12_75453_563380
  · exact context_12_75454_563396
  · exact context_12_75455_563406

theorem unmarked_context_10_4715_563408 : frontier 11 ⟨563408, by decide⟩
    (prefixCache 10 4715) (prefixPartial 10 4715) = false := by
  decide +kernel

theorem node_context_10_4715_563408 : EJMOriginalGlobalDAGData.nodes 11 ⟨563408, by decide⟩ =
    .split (coordinate 10) (![⟨563256, by decide⟩,⟨563318, by decide⟩,⟨563359, by decide⟩,⟨563407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4715_563408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4715 ⟨563408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4715
    ⟨563408, by decide⟩ (by decide) (![⟨563256, by decide⟩,⟨563318, by decide⟩,⟨563359, by decide⟩,⟨563407, by decide⟩]) unmarked_context_10_4715_563408 node_context_10_4715_563408
  intro a
  fin_cases a
  · exact context_11_18860_563256
  · exact context_11_18861_563318
  · exact context_11_18862_563359
  · exact context_11_18863_563407

theorem unmarked_context_9_1178_563409 : frontier 12 ⟨563409, by decide⟩
    (prefixCache 9 1178) (prefixPartial 9 1178) = false := by
  decide +kernel

theorem node_context_9_1178_563409 : EJMOriginalGlobalDAGData.nodes 12 ⟨563409, by decide⟩ =
    .split (coordinate 9) (![⟨562636, by decide⟩,⟨562984, by decide⟩,⟨563212, by decide⟩,⟨563408, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1178_563409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1178 ⟨563409, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1178
    ⟨563409, by decide⟩ (by decide) (![⟨562636, by decide⟩,⟨562984, by decide⟩,⟨563212, by decide⟩,⟨563408, by decide⟩]) unmarked_context_9_1178_563409 node_context_9_1178_563409
  intro a
  fin_cases a
  · exact context_10_4712_562636
  · exact context_10_4713_562984
  · exact context_10_4714_563212
  · exact context_10_4715_563408

theorem selected_cut_22110 : selected 10 ⟨563443, by decide⟩
    (prefixPartial 11 18864) = some ⟨11, 2, 0, 563443, 18864, 3457, 262144⟩ := by
  decide +kernel

theorem context_11_18864_563443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18864 ⟨563443, by decide⟩ :=
  accepted_of_selected 11 18864 ⟨563443, by decide⟩ ⟨11, 2, 0, 563443, 18864, 3457, 262144⟩
    (by decide) selected_cut_22110

theorem selected_cut_22111 : selected 10 ⟨563475, by decide⟩
    (prefixPartial 11 18865) = some ⟨11, 2, 0, 563475, 18865, 3097, 262144⟩ := by
  decide +kernel

theorem context_11_18865_563475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18865 ⟨563475, by decide⟩ :=
  accepted_of_selected 11 18865 ⟨563475, by decide⟩ ⟨11, 2, 0, 563475, 18865, 3097, 262144⟩
    (by decide) selected_cut_22111

theorem selected_cut_22112 : selected 10 ⟨563517, by decide⟩
    (prefixPartial 11 18866) = some ⟨11, 2, 0, 563517, 18866, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_18866_563517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18866 ⟨563517, by decide⟩ :=
  accepted_of_selected 11 18866 ⟨563517, by decide⟩ ⟨11, 2, 0, 563517, 18866, 3337, 262144⟩
    (by decide) selected_cut_22112

theorem selected_cut_22113 : selected 10 ⟨563556, by decide⟩
    (prefixPartial 11 18867) = some ⟨11, 2, 0, 563556, 18867, 2957, 262144⟩ := by
  decide +kernel

theorem context_11_18867_563556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18867 ⟨563556, by decide⟩ :=
  accepted_of_selected 11 18867 ⟨563556, by decide⟩ ⟨11, 2, 0, 563556, 18867, 2957, 262144⟩
    (by decide) selected_cut_22113

theorem unmarked_context_10_4716_563557 : frontier 11 ⟨563557, by decide⟩
    (prefixCache 10 4716) (prefixPartial 10 4716) = false := by
  decide +kernel

theorem node_context_10_4716_563557 : EJMOriginalGlobalDAGData.nodes 11 ⟨563557, by decide⟩ =
    .split (coordinate 10) (![⟨563443, by decide⟩,⟨563475, by decide⟩,⟨563517, by decide⟩,⟨563556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4716_563557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4716 ⟨563557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4716
    ⟨563557, by decide⟩ (by decide) (![⟨563443, by decide⟩,⟨563475, by decide⟩,⟨563517, by decide⟩,⟨563556, by decide⟩]) unmarked_context_10_4716_563557 node_context_10_4716_563557
  intro a
  fin_cases a
  · exact context_11_18864_563443
  · exact context_11_18865_563475
  · exact context_11_18866_563517
  · exact context_11_18867_563556

theorem selected_cut_22114 : selected 10 ⟨563578, by decide⟩
    (prefixPartial 11 18868) = some ⟨11, 2, 0, 563578, 18868, 2341, 262144⟩ := by
  decide +kernel

theorem context_11_18868_563578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18868 ⟨563578, by decide⟩ :=
  accepted_of_selected 11 18868 ⟨563578, by decide⟩ ⟨11, 2, 0, 563578, 18868, 2341, 262144⟩
    (by decide) selected_cut_22114

theorem selected_cut_22115 : selected 10 ⟨563600, by decide⟩
    (prefixPartial 11 18869) = some ⟨11, 2, 0, 563600, 18869, 2117, 262144⟩ := by
  decide +kernel

theorem context_11_18869_563600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18869 ⟨563600, by decide⟩ :=
  accepted_of_selected 11 18869 ⟨563600, by decide⟩ ⟨11, 2, 0, 563600, 18869, 2117, 262144⟩
    (by decide) selected_cut_22115

theorem selected_cut_22116 : selected 10 ⟨563627, by decide⟩
    (prefixPartial 11 18870) = some ⟨11, 2, 0, 563627, 18870, 2121, 262144⟩ := by
  decide +kernel

theorem context_11_18870_563627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18870 ⟨563627, by decide⟩ :=
  accepted_of_selected 11 18870 ⟨563627, by decide⟩ ⟨11, 2, 0, 563627, 18870, 2121, 262144⟩
    (by decide) selected_cut_22116

theorem selected_cut_22117 : selected 10 ⟨563643, by decide⟩
    (prefixPartial 11 18871) = some ⟨11, 2, 0, 563643, 18871, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_18871_563643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18871 ⟨563643, by decide⟩ :=
  accepted_of_selected 11 18871 ⟨563643, by decide⟩ ⟨11, 2, 0, 563643, 18871, 1733, 262144⟩
    (by decide) selected_cut_22117

theorem unmarked_context_10_4717_563644 : frontier 11 ⟨563644, by decide⟩
    (prefixCache 10 4717) (prefixPartial 10 4717) = false := by
  decide +kernel

theorem node_context_10_4717_563644 : EJMOriginalGlobalDAGData.nodes 11 ⟨563644, by decide⟩ =
    .split (coordinate 10) (![⟨563578, by decide⟩,⟨563600, by decide⟩,⟨563627, by decide⟩,⟨563643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4717_563644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4717 ⟨563644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4717
    ⟨563644, by decide⟩ (by decide) (![⟨563578, by decide⟩,⟨563600, by decide⟩,⟨563627, by decide⟩,⟨563643, by decide⟩]) unmarked_context_10_4717_563644 node_context_10_4717_563644
  intro a
  fin_cases a
  · exact context_11_18868_563578
  · exact context_11_18869_563600
  · exact context_11_18870_563627
  · exact context_11_18871_563643

theorem selected_cut_22118 : selected 10 ⟨563660, by decide⟩
    (prefixPartial 11 18872) = some ⟨11, 2, 0, 563660, 18872, 1453, 262144⟩ := by
  decide +kernel

theorem context_11_18872_563660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18872 ⟨563660, by decide⟩ :=
  accepted_of_selected 11 18872 ⟨563660, by decide⟩ ⟨11, 2, 0, 563660, 18872, 1453, 262144⟩
    (by decide) selected_cut_22118

theorem selected_cut_22119 : selected 10 ⟨563673, by decide⟩
    (prefixPartial 11 18873) = some ⟨11, 2, 0, 563673, 18873, 1417, 262144⟩ := by
  decide +kernel

theorem context_11_18873_563673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18873 ⟨563673, by decide⟩ :=
  accepted_of_selected 11 18873 ⟨563673, by decide⟩ ⟨11, 2, 0, 563673, 18873, 1417, 262144⟩
    (by decide) selected_cut_22119

theorem selected_cut_22120 : selected 10 ⟨563684, by decide⟩
    (prefixPartial 11 18874) = some ⟨11, 2, 0, 563684, 18874, 869, 262144⟩ := by
  decide +kernel

theorem context_11_18874_563684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18874 ⟨563684, by decide⟩ :=
  accepted_of_selected 11 18874 ⟨563684, by decide⟩ ⟨11, 2, 0, 563684, 18874, 869, 262144⟩
    (by decide) selected_cut_22120

theorem selected_cut_22121 : selected 10 ⟨563698, by decide⟩
    (prefixPartial 11 18875) = some ⟨11, 2, 0, 563698, 18875, 973, 262144⟩ := by
  decide +kernel

theorem context_11_18875_563698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18875 ⟨563698, by decide⟩ :=
  accepted_of_selected 11 18875 ⟨563698, by decide⟩ ⟨11, 2, 0, 563698, 18875, 973, 262144⟩
    (by decide) selected_cut_22121

theorem unmarked_context_10_4718_563699 : frontier 11 ⟨563699, by decide⟩
    (prefixCache 10 4718) (prefixPartial 10 4718) = false := by
  decide +kernel

theorem node_context_10_4718_563699 : EJMOriginalGlobalDAGData.nodes 11 ⟨563699, by decide⟩ =
    .split (coordinate 10) (![⟨563660, by decide⟩,⟨563673, by decide⟩,⟨563684, by decide⟩,⟨563698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4718_563699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4718 ⟨563699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4718
    ⟨563699, by decide⟩ (by decide) (![⟨563660, by decide⟩,⟨563673, by decide⟩,⟨563684, by decide⟩,⟨563698, by decide⟩]) unmarked_context_10_4718_563699 node_context_10_4718_563699
  intro a
  fin_cases a
  · exact context_11_18872_563660
  · exact context_11_18873_563673
  · exact context_11_18874_563684
  · exact context_11_18875_563698

theorem selected_cut_22122 : selected 11 ⟨563734, by decide⟩
    (prefixPartial 10 4719) = some ⟨10, 2, 0, 563734, 4719, 1705, 1048576⟩ := by
  decide +kernel

theorem context_10_4719_563734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4719 ⟨563734, by decide⟩ :=
  accepted_of_selected 10 4719 ⟨563734, by decide⟩ ⟨10, 2, 0, 563734, 4719, 1705, 1048576⟩
    (by decide) selected_cut_22122

theorem unmarked_context_9_1179_563735 : frontier 12 ⟨563735, by decide⟩
    (prefixCache 9 1179) (prefixPartial 9 1179) = false := by
  decide +kernel

theorem node_context_9_1179_563735 : EJMOriginalGlobalDAGData.nodes 12 ⟨563735, by decide⟩ =
    .split (coordinate 9) (![⟨563557, by decide⟩,⟨563644, by decide⟩,⟨563699, by decide⟩,⟨563734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1179_563735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1179 ⟨563735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1179
    ⟨563735, by decide⟩ (by decide) (![⟨563557, by decide⟩,⟨563644, by decide⟩,⟨563699, by decide⟩,⟨563734, by decide⟩]) unmarked_context_9_1179_563735 node_context_9_1179_563735
  intro a
  fin_cases a
  · exact context_10_4716_563557
  · exact context_10_4717_563644
  · exact context_10_4718_563699
  · exact context_10_4719_563734

theorem unmarked_context_8_294_563736 : frontier 13 ⟨563736, by decide⟩
    (prefixCache 8 294) (prefixPartial 8 294) = false := by
  decide +kernel

theorem node_context_8_294_563736 : EJMOriginalGlobalDAGData.nodes 13 ⟨563736, by decide⟩ =
    .split (coordinate 8) (![⟨559379, by decide⟩,⟨562308, by decide⟩,⟨563409, by decide⟩,⟨563735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_294_563736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 294 ⟨563736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 294
    ⟨563736, by decide⟩ (by decide) (![⟨559379, by decide⟩,⟨562308, by decide⟩,⟨563409, by decide⟩,⟨563735, by decide⟩]) unmarked_context_8_294_563736 node_context_8_294_563736
  intro a
  fin_cases a
  · exact context_9_1176_559379
  · exact context_9_1177_562308
  · exact context_9_1178_563409
  · exact context_9_1179_563735

theorem selected_cut_22123 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 18880) = some ⟨11, 1, 0, 434745, 18880, 1, 262144⟩ := by
  decide +kernel

theorem context_11_18880_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18880 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 18880 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 18880, 1, 262144⟩
    (by decide) selected_cut_22123

theorem selected_cut_22124 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75524) = some ⟨12, 1, 0, 448748, 75524, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75524_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75524 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75524 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75524, 1, 65536⟩
    (by decide) selected_cut_22124

theorem selected_cut_22125 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 75525) = some ⟨12, 1, 0, 34034, 75525, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75525_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75525 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 75525 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 75525, 1, 65536⟩
    (by decide) selected_cut_22125

theorem selected_cut_22126 : selected 8 ⟨563835, by decide⟩
    (prefixPartial 13 302104) = some ⟨13, 2, 0, 563835, 302104, 3449, 16384⟩ := by
  decide +kernel

theorem context_13_302104_563835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302104 ⟨563835, by decide⟩ :=
  accepted_of_selected 13 302104 ⟨563835, by decide⟩ ⟨13, 2, 0, 563835, 302104, 3449, 16384⟩
    (by decide) selected_cut_22126

theorem selected_cut_22127 : selected 8 ⟨563890, by decide⟩
    (prefixPartial 13 302105) = some ⟨13, 2, 0, 563890, 302105, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_302105_563890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302105 ⟨563890, by decide⟩ :=
  accepted_of_selected 13 302105 ⟨563890, by decide⟩ ⟨13, 2, 0, 563890, 302105, 3029, 16384⟩
    (by decide) selected_cut_22127

theorem selected_cut_22128 : selected 8 ⟨563918, by decide⟩
    (prefixPartial 13 302106) = some ⟨13, 2, 0, 563918, 302106, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_302106_563918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302106 ⟨563918, by decide⟩ :=
  accepted_of_selected 13 302106 ⟨563918, by decide⟩ ⟨13, 2, 0, 563918, 302106, 1977, 16384⟩
    (by decide) selected_cut_22128

theorem selected_cut_22129 : selected 8 ⟨563926, by decide⟩
    (prefixPartial 13 302107) = some ⟨13, 2, 0, 563926, 302107, 885, 16384⟩ := by
  decide +kernel

theorem context_13_302107_563926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302107 ⟨563926, by decide⟩ :=
  accepted_of_selected 13 302107 ⟨563926, by decide⟩ ⟨13, 2, 0, 563926, 302107, 885, 16384⟩
    (by decide) selected_cut_22129

theorem unmarked_context_12_75526_563927 : frontier 9 ⟨563927, by decide⟩
    (prefixCache 12 75526) (prefixPartial 12 75526) = false := by
  decide +kernel

theorem node_context_12_75526_563927 : EJMOriginalGlobalDAGData.nodes 9 ⟨563927, by decide⟩ =
    .split (coordinate 12) (![⟨563835, by decide⟩,⟨563890, by decide⟩,⟨563918, by decide⟩,⟨563926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75526_563927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75526 ⟨563927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75526
    ⟨563927, by decide⟩ (by decide) (![⟨563835, by decide⟩,⟨563890, by decide⟩,⟨563918, by decide⟩,⟨563926, by decide⟩]) unmarked_context_12_75526_563927 node_context_12_75526_563927
  intro a
  fin_cases a
  · exact context_13_302104_563835
  · exact context_13_302105_563890
  · exact context_13_302106_563918
  · exact context_13_302107_563926

theorem selected_cut_22130 : selected 8 ⟨563986, by decide⟩
    (prefixPartial 13 302108) = some ⟨13, 2, 0, 563986, 302108, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_302108_563986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302108 ⟨563986, by decide⟩ :=
  accepted_of_selected 13 302108 ⟨563986, by decide⟩ ⟨13, 2, 0, 563986, 302108, 2745, 16384⟩
    (by decide) selected_cut_22130

theorem selected_cut_22131 : selected 8 ⟨564033, by decide⟩
    (prefixPartial 13 302109) = some ⟨13, 2, 0, 564033, 302109, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_302109_564033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302109 ⟨564033, by decide⟩ :=
  accepted_of_selected 13 302109 ⟨564033, by decide⟩ ⟨13, 2, 0, 564033, 302109, 3021, 16384⟩
    (by decide) selected_cut_22131

theorem selected_cut_22132 : selected 8 ⟨564070, by decide⟩
    (prefixPartial 13 302110) = some ⟨13, 2, 0, 564070, 302110, 2245, 16384⟩ := by
  decide +kernel

theorem context_13_302110_564070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302110 ⟨564070, by decide⟩ :=
  accepted_of_selected 13 302110 ⟨564070, by decide⟩ ⟨13, 2, 0, 564070, 302110, 2245, 16384⟩
    (by decide) selected_cut_22132

theorem selected_cut_22133 : selected 8 ⟨564075, by decide⟩
    (prefixPartial 13 302111) = some ⟨13, 2, 0, 564075, 302111, 853, 16384⟩ := by
  decide +kernel

theorem context_13_302111_564075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302111 ⟨564075, by decide⟩ :=
  accepted_of_selected 13 302111 ⟨564075, by decide⟩ ⟨13, 2, 0, 564075, 302111, 853, 16384⟩
    (by decide) selected_cut_22133

theorem unmarked_context_12_75527_564076 : frontier 9 ⟨564076, by decide⟩
    (prefixCache 12 75527) (prefixPartial 12 75527) = false := by
  decide +kernel

theorem node_context_12_75527_564076 : EJMOriginalGlobalDAGData.nodes 9 ⟨564076, by decide⟩ =
    .split (coordinate 12) (![⟨563986, by decide⟩,⟨564033, by decide⟩,⟨564070, by decide⟩,⟨564075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75527_564076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75527 ⟨564076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75527
    ⟨564076, by decide⟩ (by decide) (![⟨563986, by decide⟩,⟨564033, by decide⟩,⟨564070, by decide⟩,⟨564075, by decide⟩]) unmarked_context_12_75527_564076 node_context_12_75527_564076
  intro a
  fin_cases a
  · exact context_13_302108_563986
  · exact context_13_302109_564033
  · exact context_13_302110_564070
  · exact context_13_302111_564075

theorem unmarked_context_11_18881_564077 : frontier 10 ⟨564077, by decide⟩
    (prefixCache 11 18881) (prefixPartial 11 18881) = false := by
  decide +kernel

theorem node_context_11_18881_564077 : EJMOriginalGlobalDAGData.nodes 10 ⟨564077, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨563927, by decide⟩,⟨564076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18881_564077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18881 ⟨564077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18881
    ⟨564077, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨563927, by decide⟩,⟨564076, by decide⟩]) unmarked_context_11_18881_564077 node_context_11_18881_564077
  intro a
  fin_cases a
  · exact context_12_75524_448748
  · exact context_12_75525_34034
  · exact context_12_75526_563927
  · exact context_12_75527_564076

theorem selected_cut_22134 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75528) = some ⟨12, 1, 0, 448748, 75528, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75528_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75528 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75528 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75528, 1, 65536⟩
    (by decide) selected_cut_22134

theorem selected_cut_22135 : selected 8 ⟨564150, by decide⟩
    (prefixPartial 13 302116) = some ⟨13, 2, 0, 564150, 302116, 3145, 16384⟩ := by
  decide +kernel

theorem context_13_302116_564150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302116 ⟨564150, by decide⟩ :=
  accepted_of_selected 13 302116 ⟨564150, by decide⟩ ⟨13, 2, 0, 564150, 302116, 3145, 16384⟩
    (by decide) selected_cut_22135

theorem selected_cut_22136 : selected 8 ⟨564244, by decide⟩
    (prefixPartial 13 302117) = some ⟨13, 2, 0, 564244, 302117, 3665, 16384⟩ := by
  decide +kernel

theorem context_13_302117_564244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302117 ⟨564244, by decide⟩ :=
  accepted_of_selected 13 302117 ⟨564244, by decide⟩ ⟨13, 2, 0, 564244, 302117, 3665, 16384⟩
    (by decide) selected_cut_22136

theorem selected_cut_22137 : selected 8 ⟨564291, by decide⟩
    (prefixPartial 13 302118) = some ⟨13, 2, 0, 564291, 302118, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_302118_564291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302118 ⟨564291, by decide⟩ :=
  accepted_of_selected 13 302118 ⟨564291, by decide⟩ ⟨13, 2, 0, 564291, 302118, 2209, 16384⟩
    (by decide) selected_cut_22137

theorem selected_cut_22138 : selected 8 ⟨564305, by decide⟩
    (prefixPartial 13 302119) = some ⟨13, 2, 0, 564305, 302119, 881, 16384⟩ := by
  decide +kernel

theorem context_13_302119_564305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302119 ⟨564305, by decide⟩ :=
  accepted_of_selected 13 302119 ⟨564305, by decide⟩ ⟨13, 2, 0, 564305, 302119, 881, 16384⟩
    (by decide) selected_cut_22138

theorem unmarked_context_12_75529_564306 : frontier 9 ⟨564306, by decide⟩
    (prefixCache 12 75529) (prefixPartial 12 75529) = false := by
  decide +kernel

theorem node_context_12_75529_564306 : EJMOriginalGlobalDAGData.nodes 9 ⟨564306, by decide⟩ =
    .split (coordinate 12) (![⟨564150, by decide⟩,⟨564244, by decide⟩,⟨564291, by decide⟩,⟨564305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75529_564306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75529 ⟨564306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75529
    ⟨564306, by decide⟩ (by decide) (![⟨564150, by decide⟩,⟨564244, by decide⟩,⟨564291, by decide⟩,⟨564305, by decide⟩]) unmarked_context_12_75529_564306 node_context_12_75529_564306
  intro a
  fin_cases a
  · exact context_13_302116_564150
  · exact context_13_302117_564244
  · exact context_13_302118_564291
  · exact context_13_302119_564305

theorem selected_cut_22139 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 75530) = some ⟨12, 1, 0, 524302, 75530, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75530_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75530 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 75530 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 75530, 1, 65536⟩
    (by decide) selected_cut_22139

theorem selected_cut_22140 : selected 8 ⟨564369, by decide⟩
    (prefixPartial 13 302124) = some ⟨13, 2, 0, 564369, 302124, 3041, 16384⟩ := by
  decide +kernel

theorem context_13_302124_564369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302124 ⟨564369, by decide⟩ :=
  accepted_of_selected 13 302124 ⟨564369, by decide⟩ ⟨13, 2, 0, 564369, 302124, 3041, 16384⟩
    (by decide) selected_cut_22140

theorem selected_cut_22141 : selected 8 ⟨564440, by decide⟩
    (prefixPartial 13 302125) = some ⟨13, 2, 0, 564440, 302125, 3665, 16384⟩ := by
  decide +kernel

theorem context_13_302125_564440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302125 ⟨564440, by decide⟩ :=
  accepted_of_selected 13 302125 ⟨564440, by decide⟩ ⟨13, 2, 0, 564440, 302125, 3665, 16384⟩
    (by decide) selected_cut_22141

theorem selected_cut_22142 : selected 8 ⟨564476, by decide⟩
    (prefixPartial 13 302126) = some ⟨13, 2, 0, 564476, 302126, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_302126_564476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302126 ⟨564476, by decide⟩ :=
  accepted_of_selected 13 302126 ⟨564476, by decide⟩ ⟨13, 2, 0, 564476, 302126, 2345, 16384⟩
    (by decide) selected_cut_22142

theorem selected_cut_22143 : selected 8 ⟨564485, by decide⟩
    (prefixPartial 13 302127) = some ⟨13, 2, 0, 564485, 302127, 853, 16384⟩ := by
  decide +kernel

theorem context_13_302127_564485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302127 ⟨564485, by decide⟩ :=
  accepted_of_selected 13 302127 ⟨564485, by decide⟩ ⟨13, 2, 0, 564485, 302127, 853, 16384⟩
    (by decide) selected_cut_22143

theorem unmarked_context_12_75531_564486 : frontier 9 ⟨564486, by decide⟩
    (prefixCache 12 75531) (prefixPartial 12 75531) = false := by
  decide +kernel

theorem node_context_12_75531_564486 : EJMOriginalGlobalDAGData.nodes 9 ⟨564486, by decide⟩ =
    .split (coordinate 12) (![⟨564369, by decide⟩,⟨564440, by decide⟩,⟨564476, by decide⟩,⟨564485, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75531_564486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75531 ⟨564486, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75531
    ⟨564486, by decide⟩ (by decide) (![⟨564369, by decide⟩,⟨564440, by decide⟩,⟨564476, by decide⟩,⟨564485, by decide⟩]) unmarked_context_12_75531_564486 node_context_12_75531_564486
  intro a
  fin_cases a
  · exact context_13_302124_564369
  · exact context_13_302125_564440
  · exact context_13_302126_564476
  · exact context_13_302127_564485

theorem unmarked_context_11_18882_564487 : frontier 10 ⟨564487, by decide⟩
    (prefixCache 11 18882) (prefixPartial 11 18882) = false := by
  decide +kernel

theorem node_context_11_18882_564487 : EJMOriginalGlobalDAGData.nodes 10 ⟨564487, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨564306, by decide⟩,⟨524302, by decide⟩,⟨564486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18882_564487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18882 ⟨564487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18882
    ⟨564487, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨564306, by decide⟩,⟨524302, by decide⟩,⟨564486, by decide⟩]) unmarked_context_11_18882_564487 node_context_11_18882_564487
  intro a
  fin_cases a
  · exact context_12_75528_448748
  · exact context_12_75529_564306
  · exact context_12_75530_524302
  · exact context_12_75531_564486

theorem selected_cut_22144 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 75532) = some ⟨12, 1, 0, 448748, 75532, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75532_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75532 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 75532 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 75532, 1, 65536⟩
    (by decide) selected_cut_22144

theorem selected_cut_22145 : selected 9 ⟨292651, by decide⟩
    (prefixPartial 12 75533) = some ⟨12, 1, 0, 292651, 75533, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75533_292651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75533 ⟨292651, by decide⟩ :=
  accepted_of_selected 12 75533 ⟨292651, by decide⟩ ⟨12, 1, 0, 292651, 75533, 1, 65536⟩
    (by decide) selected_cut_22145

theorem selected_cut_22146 : selected 8 ⟨564555, by decide⟩
    (prefixPartial 13 302136) = some ⟨13, 2, 0, 564555, 302136, 2961, 16384⟩ := by
  decide +kernel

theorem context_13_302136_564555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302136 ⟨564555, by decide⟩ :=
  accepted_of_selected 13 302136 ⟨564555, by decide⟩ ⟨13, 2, 0, 564555, 302136, 2961, 16384⟩
    (by decide) selected_cut_22146

theorem selected_cut_22147 : selected 8 ⟨564631, by decide⟩
    (prefixPartial 13 302137) = some ⟨13, 2, 0, 564631, 302137, 3689, 16384⟩ := by
  decide +kernel

theorem context_13_302137_564631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302137 ⟨564631, by decide⟩ :=
  accepted_of_selected 13 302137 ⟨564631, by decide⟩ ⟨13, 2, 0, 564631, 302137, 3689, 16384⟩
    (by decide) selected_cut_22147

theorem selected_cut_22148 : selected 8 ⟨564661, by decide⟩
    (prefixPartial 13 302138) = some ⟨13, 2, 0, 564661, 302138, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_302138_564661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302138 ⟨564661, by decide⟩ :=
  accepted_of_selected 13 302138 ⟨564661, by decide⟩ ⟨13, 2, 0, 564661, 302138, 1829, 16384⟩
    (by decide) selected_cut_22148

theorem selected_cut_22149 : selected 8 ⟨564668, by decide⟩
    (prefixPartial 13 302139) = some ⟨13, 2, 0, 564668, 302139, 837, 16384⟩ := by
  decide +kernel

theorem context_13_302139_564668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302139 ⟨564668, by decide⟩ :=
  accepted_of_selected 13 302139 ⟨564668, by decide⟩ ⟨13, 2, 0, 564668, 302139, 837, 16384⟩
    (by decide) selected_cut_22149

theorem unmarked_context_12_75534_564669 : frontier 9 ⟨564669, by decide⟩
    (prefixCache 12 75534) (prefixPartial 12 75534) = false := by
  decide +kernel

theorem node_context_12_75534_564669 : EJMOriginalGlobalDAGData.nodes 9 ⟨564669, by decide⟩ =
    .split (coordinate 12) (![⟨564555, by decide⟩,⟨564631, by decide⟩,⟨564661, by decide⟩,⟨564668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75534_564669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75534 ⟨564669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75534
    ⟨564669, by decide⟩ (by decide) (![⟨564555, by decide⟩,⟨564631, by decide⟩,⟨564661, by decide⟩,⟨564668, by decide⟩]) unmarked_context_12_75534_564669 node_context_12_75534_564669
  intro a
  fin_cases a
  · exact context_13_302136_564555
  · exact context_13_302137_564631
  · exact context_13_302138_564661
  · exact context_13_302139_564668

theorem selected_cut_22150 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 75535) = some ⟨12, 1, 0, 518278, 75535, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75535_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75535 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 75535 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 75535, 1, 65536⟩
    (by decide) selected_cut_22150

theorem unmarked_context_11_18883_564670 : frontier 10 ⟨564670, by decide⟩
    (prefixCache 11 18883) (prefixPartial 11 18883) = false := by
  decide +kernel

theorem node_context_11_18883_564670 : EJMOriginalGlobalDAGData.nodes 10 ⟨564670, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨292651, by decide⟩,⟨564669, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18883_564670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18883 ⟨564670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18883
    ⟨564670, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨292651, by decide⟩,⟨564669, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_18883_564670 node_context_11_18883_564670
  intro a
  fin_cases a
  · exact context_12_75532_448748
  · exact context_12_75533_292651
  · exact context_12_75534_564669
  · exact context_12_75535_518278

theorem unmarked_context_10_4720_564671 : frontier 11 ⟨564671, by decide⟩
    (prefixCache 10 4720) (prefixPartial 10 4720) = false := by
  decide +kernel

theorem node_context_10_4720_564671 : EJMOriginalGlobalDAGData.nodes 11 ⟨564671, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨564077, by decide⟩,⟨564487, by decide⟩,⟨564670, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4720_564671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4720 ⟨564671, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4720
    ⟨564671, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨564077, by decide⟩,⟨564487, by decide⟩,⟨564670, by decide⟩]) unmarked_context_10_4720_564671 node_context_10_4720_564671
  intro a
  fin_cases a
  · exact context_11_18880_434745
  · exact context_11_18881_564077
  · exact context_11_18882_564487
  · exact context_11_18883_564670

theorem selected_cut_22151 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 75536) = some ⟨12, 1, 0, 435160, 75536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75536_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75536 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 75536 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 75536, 1, 65536⟩
    (by decide) selected_cut_22151

theorem selected_cut_22152 : selected 8 ⟨564699, by decide⟩
    (prefixPartial 13 302148) = some ⟨13, 2, 0, 564699, 302148, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_302148_564699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302148 ⟨564699, by decide⟩ :=
  accepted_of_selected 13 302148 ⟨564699, by decide⟩ ⟨13, 2, 0, 564699, 302148, 1621, 16384⟩
    (by decide) selected_cut_22152

theorem selected_cut_22153 : selected 8 ⟨564732, by decide⟩
    (prefixPartial 13 302149) = some ⟨13, 2, 0, 564732, 302149, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_302149_564732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302149 ⟨564732, by decide⟩ :=
  accepted_of_selected 13 302149 ⟨564732, by decide⟩ ⟨13, 2, 0, 564732, 302149, 2309, 16384⟩
    (by decide) selected_cut_22153

theorem selected_cut_22154 : selected 8 ⟨564757, by decide⟩
    (prefixPartial 13 302150) = some ⟨13, 2, 0, 564757, 302150, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_302150_564757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302150 ⟨564757, by decide⟩ :=
  accepted_of_selected 13 302150 ⟨564757, by decide⟩ ⟨13, 2, 0, 564757, 302150, 1525, 16384⟩
    (by decide) selected_cut_22154

theorem selected_cut_22155 : selected 8 ⟨564763, by decide⟩
    (prefixPartial 13 302151) = some ⟨13, 2, 0, 564763, 302151, 609, 16384⟩ := by
  decide +kernel

theorem context_13_302151_564763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302151 ⟨564763, by decide⟩ :=
  accepted_of_selected 13 302151 ⟨564763, by decide⟩ ⟨13, 2, 0, 564763, 302151, 609, 16384⟩
    (by decide) selected_cut_22155

theorem unmarked_context_12_75537_564764 : frontier 9 ⟨564764, by decide⟩
    (prefixCache 12 75537) (prefixPartial 12 75537) = false := by
  decide +kernel

theorem node_context_12_75537_564764 : EJMOriginalGlobalDAGData.nodes 9 ⟨564764, by decide⟩ =
    .split (coordinate 12) (![⟨564699, by decide⟩,⟨564732, by decide⟩,⟨564757, by decide⟩,⟨564763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75537_564764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75537 ⟨564764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75537
    ⟨564764, by decide⟩ (by decide) (![⟨564699, by decide⟩,⟨564732, by decide⟩,⟨564757, by decide⟩,⟨564763, by decide⟩]) unmarked_context_12_75537_564764 node_context_12_75537_564764
  intro a
  fin_cases a
  · exact context_13_302148_564699
  · exact context_13_302149_564732
  · exact context_13_302150_564757
  · exact context_13_302151_564763

theorem selected_cut_22156 : selected 8 ⟨564795, by decide⟩
    (prefixPartial 13 302152) = some ⟨13, 2, 0, 564795, 302152, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_302152_564795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302152 ⟨564795, by decide⟩ :=
  accepted_of_selected 13 302152 ⟨564795, by decide⟩ ⟨13, 2, 0, 564795, 302152, 1749, 16384⟩
    (by decide) selected_cut_22156

theorem selected_cut_22157 : selected 8 ⟨564826, by decide⟩
    (prefixPartial 13 302153) = some ⟨13, 2, 0, 564826, 302153, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_302153_564826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302153 ⟨564826, by decide⟩ :=
  accepted_of_selected 13 302153 ⟨564826, by decide⟩ ⟨13, 2, 0, 564826, 302153, 2365, 16384⟩
    (by decide) selected_cut_22157

theorem selected_cut_22158 : selected 8 ⟨564850, by decide⟩
    (prefixPartial 13 302154) = some ⟨13, 2, 0, 564850, 302154, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_302154_564850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302154 ⟨564850, by decide⟩ :=
  accepted_of_selected 13 302154 ⟨564850, by decide⟩ ⟨13, 2, 0, 564850, 302154, 1769, 16384⟩
    (by decide) selected_cut_22158

theorem selected_cut_22159 : selected 8 ⟨564857, by decide⟩
    (prefixPartial 13 302155) = some ⟨13, 2, 0, 564857, 302155, 665, 16384⟩ := by
  decide +kernel

theorem context_13_302155_564857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302155 ⟨564857, by decide⟩ :=
  accepted_of_selected 13 302155 ⟨564857, by decide⟩ ⟨13, 2, 0, 564857, 302155, 665, 16384⟩
    (by decide) selected_cut_22159

theorem unmarked_context_12_75538_564858 : frontier 9 ⟨564858, by decide⟩
    (prefixCache 12 75538) (prefixPartial 12 75538) = false := by
  decide +kernel

theorem node_context_12_75538_564858 : EJMOriginalGlobalDAGData.nodes 9 ⟨564858, by decide⟩ =
    .split (coordinate 12) (![⟨564795, by decide⟩,⟨564826, by decide⟩,⟨564850, by decide⟩,⟨564857, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75538_564858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75538 ⟨564858, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75538
    ⟨564858, by decide⟩ (by decide) (![⟨564795, by decide⟩,⟨564826, by decide⟩,⟨564850, by decide⟩,⟨564857, by decide⟩]) unmarked_context_12_75538_564858 node_context_12_75538_564858
  intro a
  fin_cases a
  · exact context_13_302152_564795
  · exact context_13_302153_564826
  · exact context_13_302154_564850
  · exact context_13_302155_564857

theorem selected_cut_22160 : selected 8 ⟨564886, by decide⟩
    (prefixPartial 13 302156) = some ⟨13, 2, 0, 564886, 302156, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_302156_564886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302156 ⟨564886, by decide⟩ :=
  accepted_of_selected 13 302156 ⟨564886, by decide⟩ ⟨13, 2, 0, 564886, 302156, 1537, 16384⟩
    (by decide) selected_cut_22160

theorem selected_cut_22161 : selected 8 ⟨564915, by decide⟩
    (prefixPartial 13 302157) = some ⟨13, 2, 0, 564915, 302157, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_302157_564915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302157 ⟨564915, by decide⟩ :=
  accepted_of_selected 13 302157 ⟨564915, by decide⟩ ⟨13, 2, 0, 564915, 302157, 2313, 16384⟩
    (by decide) selected_cut_22161

theorem selected_cut_22162 : selected 8 ⟨564938, by decide⟩
    (prefixPartial 13 302158) = some ⟨13, 2, 0, 564938, 302158, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_302158_564938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302158 ⟨564938, by decide⟩ :=
  accepted_of_selected 13 302158 ⟨564938, by decide⟩ ⟨13, 2, 0, 564938, 302158, 1721, 16384⟩
    (by decide) selected_cut_22162

theorem selected_cut_22163 : selected 8 ⟨564943, by decide⟩
    (prefixPartial 13 302159) = some ⟨13, 2, 0, 564943, 302159, 601, 16384⟩ := by
  decide +kernel

theorem context_13_302159_564943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302159 ⟨564943, by decide⟩ :=
  accepted_of_selected 13 302159 ⟨564943, by decide⟩ ⟨13, 2, 0, 564943, 302159, 601, 16384⟩
    (by decide) selected_cut_22163

theorem unmarked_context_12_75539_564944 : frontier 9 ⟨564944, by decide⟩
    (prefixCache 12 75539) (prefixPartial 12 75539) = false := by
  decide +kernel

theorem node_context_12_75539_564944 : EJMOriginalGlobalDAGData.nodes 9 ⟨564944, by decide⟩ =
    .split (coordinate 12) (![⟨564886, by decide⟩,⟨564915, by decide⟩,⟨564938, by decide⟩,⟨564943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75539_564944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75539 ⟨564944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75539
    ⟨564944, by decide⟩ (by decide) (![⟨564886, by decide⟩,⟨564915, by decide⟩,⟨564938, by decide⟩,⟨564943, by decide⟩]) unmarked_context_12_75539_564944 node_context_12_75539_564944
  intro a
  fin_cases a
  · exact context_13_302156_564886
  · exact context_13_302157_564915
  · exact context_13_302158_564938
  · exact context_13_302159_564943

theorem unmarked_context_11_18884_564945 : frontier 10 ⟨564945, by decide⟩
    (prefixCache 11 18884) (prefixPartial 11 18884) = false := by
  decide +kernel

theorem node_context_11_18884_564945 : EJMOriginalGlobalDAGData.nodes 10 ⟨564945, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨564764, by decide⟩,⟨564858, by decide⟩,⟨564944, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18884_564945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18884 ⟨564945, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18884
    ⟨564945, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨564764, by decide⟩,⟨564858, by decide⟩,⟨564944, by decide⟩]) unmarked_context_11_18884_564945 node_context_11_18884_564945
  intro a
  fin_cases a
  · exact context_12_75536_435160
  · exact context_12_75537_564764
  · exact context_12_75538_564858
  · exact context_12_75539_564944

theorem selected_cut_22164 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 75540) = some ⟨12, 1, 0, 435160, 75540, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75540_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75540 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 75540 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 75540, 1, 65536⟩
    (by decide) selected_cut_22164

theorem selected_cut_22165 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 75541) = some ⟨12, 1, 0, 449506, 75541, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75541_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75541 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 75541 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 75541, 1, 65536⟩
    (by decide) selected_cut_22165

theorem selected_cut_22166 : selected 8 ⟨565005, by decide⟩
    (prefixPartial 13 302168) = some ⟨13, 2, 0, 565005, 302168, 2801, 16384⟩ := by
  decide +kernel

theorem context_13_302168_565005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302168 ⟨565005, by decide⟩ :=
  accepted_of_selected 13 302168 ⟨565005, by decide⟩ ⟨13, 2, 0, 565005, 302168, 2801, 16384⟩
    (by decide) selected_cut_22166

theorem selected_cut_22167 : selected 8 ⟨565049, by decide⟩
    (prefixPartial 13 302169) = some ⟨13, 2, 0, 565049, 302169, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_302169_565049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302169 ⟨565049, by decide⟩ :=
  accepted_of_selected 13 302169 ⟨565049, by decide⟩ ⟨13, 2, 0, 565049, 302169, 2917, 16384⟩
    (by decide) selected_cut_22167

theorem selected_cut_22168 : selected 8 ⟨565086, by decide⟩
    (prefixPartial 13 302170) = some ⟨13, 2, 0, 565086, 302170, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_302170_565086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302170 ⟨565086, by decide⟩ :=
  accepted_of_selected 13 302170 ⟨565086, by decide⟩ ⟨13, 2, 0, 565086, 302170, 2353, 16384⟩
    (by decide) selected_cut_22168

theorem selected_cut_22169 : selected 8 ⟨565101, by decide⟩
    (prefixPartial 13 302171) = some ⟨13, 2, 0, 565101, 302171, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_302171_565101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302171 ⟨565101, by decide⟩ :=
  accepted_of_selected 13 302171 ⟨565101, by decide⟩ ⟨13, 2, 0, 565101, 302171, 1093, 16384⟩
    (by decide) selected_cut_22169

theorem unmarked_context_12_75542_565102 : frontier 9 ⟨565102, by decide⟩
    (prefixCache 12 75542) (prefixPartial 12 75542) = false := by
  decide +kernel

theorem node_context_12_75542_565102 : EJMOriginalGlobalDAGData.nodes 9 ⟨565102, by decide⟩ =
    .split (coordinate 12) (![⟨565005, by decide⟩,⟨565049, by decide⟩,⟨565086, by decide⟩,⟨565101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75542_565102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75542 ⟨565102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75542
    ⟨565102, by decide⟩ (by decide) (![⟨565005, by decide⟩,⟨565049, by decide⟩,⟨565086, by decide⟩,⟨565101, by decide⟩]) unmarked_context_12_75542_565102 node_context_12_75542_565102
  intro a
  fin_cases a
  · exact context_13_302168_565005
  · exact context_13_302169_565049
  · exact context_13_302170_565086
  · exact context_13_302171_565101

theorem selected_cut_22170 : selected 8 ⟨565147, by decide⟩
    (prefixPartial 13 302172) = some ⟨13, 2, 0, 565147, 302172, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_302172_565147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302172 ⟨565147, by decide⟩ :=
  accepted_of_selected 13 302172 ⟨565147, by decide⟩ ⟨13, 2, 0, 565147, 302172, 2457, 16384⟩
    (by decide) selected_cut_22170

theorem selected_cut_22171 : selected 8 ⟨565173, by decide⟩
    (prefixPartial 13 302173) = some ⟨13, 2, 0, 565173, 302173, 2845, 16384⟩ := by
  decide +kernel

theorem context_13_302173_565173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302173 ⟨565173, by decide⟩ :=
  accepted_of_selected 13 302173 ⟨565173, by decide⟩ ⟨13, 2, 0, 565173, 302173, 2845, 16384⟩
    (by decide) selected_cut_22171

theorem selected_cut_22172 : selected 8 ⟨565219, by decide⟩
    (prefixPartial 13 302174) = some ⟨13, 2, 0, 565219, 302174, 2481, 16384⟩ := by
  decide +kernel

theorem context_13_302174_565219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302174 ⟨565219, by decide⟩ :=
  accepted_of_selected 13 302174 ⟨565219, by decide⟩ ⟨13, 2, 0, 565219, 302174, 2481, 16384⟩
    (by decide) selected_cut_22172

theorem selected_cut_22173 : selected 8 ⟨565225, by decide⟩
    (prefixPartial 13 302175) = some ⟨13, 2, 0, 565225, 302175, 953, 16384⟩ := by
  decide +kernel

theorem context_13_302175_565225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302175 ⟨565225, by decide⟩ :=
  accepted_of_selected 13 302175 ⟨565225, by decide⟩ ⟨13, 2, 0, 565225, 302175, 953, 16384⟩
    (by decide) selected_cut_22173

theorem unmarked_context_12_75543_565226 : frontier 9 ⟨565226, by decide⟩
    (prefixCache 12 75543) (prefixPartial 12 75543) = false := by
  decide +kernel

theorem node_context_12_75543_565226 : EJMOriginalGlobalDAGData.nodes 9 ⟨565226, by decide⟩ =
    .split (coordinate 12) (![⟨565147, by decide⟩,⟨565173, by decide⟩,⟨565219, by decide⟩,⟨565225, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75543_565226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75543 ⟨565226, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75543
    ⟨565226, by decide⟩ (by decide) (![⟨565147, by decide⟩,⟨565173, by decide⟩,⟨565219, by decide⟩,⟨565225, by decide⟩]) unmarked_context_12_75543_565226 node_context_12_75543_565226
  intro a
  fin_cases a
  · exact context_13_302172_565147
  · exact context_13_302173_565173
  · exact context_13_302174_565219
  · exact context_13_302175_565225

theorem unmarked_context_11_18885_565227 : frontier 10 ⟨565227, by decide⟩
    (prefixCache 11 18885) (prefixPartial 11 18885) = false := by
  decide +kernel

theorem node_context_11_18885_565227 : EJMOriginalGlobalDAGData.nodes 10 ⟨565227, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨449506, by decide⟩,⟨565102, by decide⟩,⟨565226, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18885_565227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18885 ⟨565227, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18885
    ⟨565227, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨449506, by decide⟩,⟨565102, by decide⟩,⟨565226, by decide⟩]) unmarked_context_11_18885_565227 node_context_11_18885_565227
  intro a
  fin_cases a
  · exact context_12_75540_435160
  · exact context_12_75541_449506
  · exact context_12_75542_565102
  · exact context_12_75543_565226

theorem selected_cut_22174 : selected 8 ⟨565267, by decide⟩
    (prefixPartial 13 302176) = some ⟨13, 2, 0, 565267, 302176, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_302176_565267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302176 ⟨565267, by decide⟩ :=
  accepted_of_selected 13 302176 ⟨565267, by decide⟩ ⟨13, 2, 0, 565267, 302176, 2157, 16384⟩
    (by decide) selected_cut_22174

theorem selected_cut_22175 : selected 8 ⟨565319, by decide⟩
    (prefixPartial 13 302177) = some ⟨13, 2, 0, 565319, 302177, 3197, 16384⟩ := by
  decide +kernel

theorem context_13_302177_565319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302177 ⟨565319, by decide⟩ :=
  accepted_of_selected 13 302177 ⟨565319, by decide⟩ ⟨13, 2, 0, 565319, 302177, 3197, 16384⟩
    (by decide) selected_cut_22175

theorem selected_cut_22176 : selected 8 ⟨565362, by decide⟩
    (prefixPartial 13 302178) = some ⟨13, 2, 0, 565362, 302178, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_302178_565362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302178 ⟨565362, by decide⟩ :=
  accepted_of_selected 13 302178 ⟨565362, by decide⟩ ⟨13, 2, 0, 565362, 302178, 2485, 16384⟩
    (by decide) selected_cut_22176

theorem selected_cut_22177 : selected 8 ⟨565375, by decide⟩
    (prefixPartial 13 302179) = some ⟨13, 2, 0, 565375, 302179, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_302179_565375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302179 ⟨565375, by decide⟩ :=
  accepted_of_selected 13 302179 ⟨565375, by decide⟩ ⟨13, 2, 0, 565375, 302179, 1049, 16384⟩
    (by decide) selected_cut_22177

theorem unmarked_context_12_75544_565376 : frontier 9 ⟨565376, by decide⟩
    (prefixCache 12 75544) (prefixPartial 12 75544) = false := by
  decide +kernel

theorem node_context_12_75544_565376 : EJMOriginalGlobalDAGData.nodes 9 ⟨565376, by decide⟩ =
    .split (coordinate 12) (![⟨565267, by decide⟩,⟨565319, by decide⟩,⟨565362, by decide⟩,⟨565375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75544_565376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75544 ⟨565376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75544
    ⟨565376, by decide⟩ (by decide) (![⟨565267, by decide⟩,⟨565319, by decide⟩,⟨565362, by decide⟩,⟨565375, by decide⟩]) unmarked_context_12_75544_565376 node_context_12_75544_565376
  intro a
  fin_cases a
  · exact context_13_302176_565267
  · exact context_13_302177_565319
  · exact context_13_302178_565362
  · exact context_13_302179_565375

theorem selected_cut_22178 : selected 8 ⟨565405, by decide⟩
    (prefixPartial 13 302180) = some ⟨13, 2, 0, 565405, 302180, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_302180_565405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 302180 ⟨565405, by decide⟩ :=
  accepted_of_selected 13 302180 ⟨565405, by decide⟩ ⟨13, 2, 0, 565405, 302180, 1537, 16384⟩
    (by decide) selected_cut_22178

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
