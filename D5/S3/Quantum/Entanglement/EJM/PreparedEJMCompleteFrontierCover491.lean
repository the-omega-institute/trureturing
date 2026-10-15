/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover490
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_47140 : selected 9 ⟨1318384, by decide⟩
    (prefixPartial 12 372502) = some ⟨12, 2, 0, 1318384, 372502, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_372502_1318384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372502 ⟨1318384, by decide⟩ :=
  accepted_of_selected 12 372502 ⟨1318384, by decide⟩ ⟨12, 2, 0, 1318384, 372502, 3465, 65536⟩
    (by decide) selected_cut_47140

theorem selected_cut_47141 : selected 9 ⟨692794, by decide⟩
    (prefixPartial 12 372503) = some ⟨12, 1, 0, 692794, 372503, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372503_692794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372503 ⟨692794, by decide⟩ :=
  accepted_of_selected 12 372503 ⟨692794, by decide⟩ ⟨12, 1, 0, 692794, 372503, 1, 65536⟩
    (by decide) selected_cut_47141

theorem unmarked_context_11_93125_1318385 : frontier 10 ⟨1318385, by decide⟩
    (prefixCache 11 93125) (prefixPartial 11 93125) = false := by
  decide +kernel

theorem node_context_11_93125_1318385 : EJMOriginalGlobalDAGData.nodes 10 ⟨1318385, by decide⟩ =
    .split (coordinate 11) (![⟨1318310, by decide⟩,⟨1172003, by decide⟩,⟨1318384, by decide⟩,⟨692794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93125_1318385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93125 ⟨1318385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93125
    ⟨1318385, by decide⟩ (by decide) (![⟨1318310, by decide⟩,⟨1172003, by decide⟩,⟨1318384, by decide⟩,⟨692794, by decide⟩]) unmarked_context_11_93125_1318385 node_context_11_93125_1318385
  intro a
  fin_cases a
  · exact context_12_372500_1318310
  · exact context_12_372501_1172003
  · exact context_12_372502_1318384
  · exact context_12_372503_692794

theorem selected_cut_47142 : selected 9 ⟨1318445, by decide⟩
    (prefixPartial 12 372504) = some ⟨12, 2, 0, 1318445, 372504, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_372504_1318445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372504 ⟨1318445, by decide⟩ :=
  accepted_of_selected 12 372504 ⟨1318445, by decide⟩ ⟨12, 2, 0, 1318445, 372504, 3057, 65536⟩
    (by decide) selected_cut_47142

theorem selected_cut_47143 : selected 9 ⟨1318510, by decide⟩
    (prefixPartial 12 372505) = some ⟨12, 2, 0, 1318510, 372505, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_372505_1318510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372505 ⟨1318510, by decide⟩ :=
  accepted_of_selected 12 372505 ⟨1318510, by decide⟩ ⟨12, 2, 0, 1318510, 372505, 3301, 65536⟩
    (by decide) selected_cut_47143

theorem selected_cut_47144 : selected 9 ⟨1318561, by decide⟩
    (prefixPartial 12 372506) = some ⟨12, 2, 0, 1318561, 372506, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_372506_1318561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372506 ⟨1318561, by decide⟩ :=
  accepted_of_selected 12 372506 ⟨1318561, by decide⟩ ⟨12, 2, 0, 1318561, 372506, 2773, 65536⟩
    (by decide) selected_cut_47144

theorem selected_cut_47145 : selected 9 ⟨1318616, by decide⟩
    (prefixPartial 12 372507) = some ⟨12, 2, 0, 1318616, 372507, 3301, 65536⟩ := by
  decide +kernel

theorem context_12_372507_1318616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372507 ⟨1318616, by decide⟩ :=
  accepted_of_selected 12 372507 ⟨1318616, by decide⟩ ⟨12, 2, 0, 1318616, 372507, 3301, 65536⟩
    (by decide) selected_cut_47145

theorem unmarked_context_11_93126_1318617 : frontier 10 ⟨1318617, by decide⟩
    (prefixCache 11 93126) (prefixPartial 11 93126) = false := by
  decide +kernel

theorem node_context_11_93126_1318617 : EJMOriginalGlobalDAGData.nodes 10 ⟨1318617, by decide⟩ =
    .split (coordinate 11) (![⟨1318445, by decide⟩,⟨1318510, by decide⟩,⟨1318561, by decide⟩,⟨1318616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93126_1318617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93126 ⟨1318617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93126
    ⟨1318617, by decide⟩ (by decide) (![⟨1318445, by decide⟩,⟨1318510, by decide⟩,⟨1318561, by decide⟩,⟨1318616, by decide⟩]) unmarked_context_11_93126_1318617 node_context_11_93126_1318617
  intro a
  fin_cases a
  · exact context_12_372504_1318445
  · exact context_12_372505_1318510
  · exact context_12_372506_1318561
  · exact context_12_372507_1318616

theorem selected_cut_47146 : selected 9 ⟨1318671, by decide⟩
    (prefixPartial 12 372508) = some ⟨12, 2, 0, 1318671, 372508, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_372508_1318671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372508 ⟨1318671, by decide⟩ :=
  accepted_of_selected 12 372508 ⟨1318671, by decide⟩ ⟨12, 2, 0, 1318671, 372508, 2937, 65536⟩
    (by decide) selected_cut_47146

theorem selected_cut_47147 : selected 9 ⟨1318727, by decide⟩
    (prefixPartial 12 372509) = some ⟨12, 2, 0, 1318727, 372509, 2949, 65536⟩ := by
  decide +kernel

theorem context_12_372509_1318727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372509 ⟨1318727, by decide⟩ :=
  accepted_of_selected 12 372509 ⟨1318727, by decide⟩ ⟨12, 2, 0, 1318727, 372509, 2949, 65536⟩
    (by decide) selected_cut_47147

theorem selected_cut_47148 : selected 9 ⟨1318782, by decide⟩
    (prefixPartial 12 372510) = some ⟨12, 2, 0, 1318782, 372510, 2889, 65536⟩ := by
  decide +kernel

theorem context_12_372510_1318782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372510 ⟨1318782, by decide⟩ :=
  accepted_of_selected 12 372510 ⟨1318782, by decide⟩ ⟨12, 2, 0, 1318782, 372510, 2889, 65536⟩
    (by decide) selected_cut_47148

theorem selected_cut_47149 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 372511) = some ⟨12, 1, 0, 903806, 372511, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372511_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372511 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 372511 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 372511, 1, 65536⟩
    (by decide) selected_cut_47149

theorem unmarked_context_11_93127_1318783 : frontier 10 ⟨1318783, by decide⟩
    (prefixCache 11 93127) (prefixPartial 11 93127) = false := by
  decide +kernel

theorem node_context_11_93127_1318783 : EJMOriginalGlobalDAGData.nodes 10 ⟨1318783, by decide⟩ =
    .split (coordinate 11) (![⟨1318671, by decide⟩,⟨1318727, by decide⟩,⟨1318782, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93127_1318783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93127 ⟨1318783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93127
    ⟨1318783, by decide⟩ (by decide) (![⟨1318671, by decide⟩,⟨1318727, by decide⟩,⟨1318782, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93127_1318783 node_context_11_93127_1318783
  intro a
  fin_cases a
  · exact context_12_372508_1318671
  · exact context_12_372509_1318727
  · exact context_12_372510_1318782
  · exact context_12_372511_903806

theorem unmarked_context_10_23281_1318784 : frontier 11 ⟨1318784, by decide⟩
    (prefixCache 10 23281) (prefixPartial 10 23281) = false := by
  decide +kernel

theorem node_context_10_23281_1318784 : EJMOriginalGlobalDAGData.nodes 11 ⟨1318784, by decide⟩ =
    .split (coordinate 10) (![⟨1318218, by decide⟩,⟨1318385, by decide⟩,⟨1318617, by decide⟩,⟨1318783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23281_1318784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23281 ⟨1318784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23281
    ⟨1318784, by decide⟩ (by decide) (![⟨1318218, by decide⟩,⟨1318385, by decide⟩,⟨1318617, by decide⟩,⟨1318783, by decide⟩]) unmarked_context_10_23281_1318784 node_context_10_23281_1318784
  intro a
  fin_cases a
  · exact context_11_93124_1318218
  · exact context_11_93125_1318385
  · exact context_11_93126_1318617
  · exact context_11_93127_1318783

theorem selected_cut_47150 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 372512) = some ⟨12, 1, 0, 435790, 372512, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372512_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372512 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 372512 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 372512, 1, 65536⟩
    (by decide) selected_cut_47150

theorem selected_cut_47151 : selected 9 ⟨1318838, by decide⟩
    (prefixPartial 12 372513) = some ⟨12, 2, 0, 1318838, 372513, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_372513_1318838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372513 ⟨1318838, by decide⟩ :=
  accepted_of_selected 12 372513 ⟨1318838, by decide⟩ ⟨12, 2, 0, 1318838, 372513, 3101, 65536⟩
    (by decide) selected_cut_47151

theorem selected_cut_47152 : selected 9 ⟨1318892, by decide⟩
    (prefixPartial 12 372514) = some ⟨12, 2, 0, 1318892, 372514, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_372514_1318892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372514 ⟨1318892, by decide⟩ :=
  accepted_of_selected 12 372514 ⟨1318892, by decide⟩ ⟨12, 2, 0, 1318892, 372514, 2877, 65536⟩
    (by decide) selected_cut_47152

theorem selected_cut_47153 : selected 9 ⟨1318950, by decide⟩
    (prefixPartial 12 372515) = some ⟨12, 2, 0, 1318950, 372515, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_372515_1318950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372515 ⟨1318950, by decide⟩ :=
  accepted_of_selected 12 372515 ⟨1318950, by decide⟩ ⟨12, 2, 0, 1318950, 372515, 3257, 65536⟩
    (by decide) selected_cut_47153

theorem unmarked_context_11_93128_1318951 : frontier 10 ⟨1318951, by decide⟩
    (prefixCache 11 93128) (prefixPartial 11 93128) = false := by
  decide +kernel

theorem node_context_11_93128_1318951 : EJMOriginalGlobalDAGData.nodes 10 ⟨1318951, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1318838, by decide⟩,⟨1318892, by decide⟩,⟨1318950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93128_1318951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93128 ⟨1318951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93128
    ⟨1318951, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1318838, by decide⟩,⟨1318892, by decide⟩,⟨1318950, by decide⟩]) unmarked_context_11_93128_1318951 node_context_11_93128_1318951
  intro a
  fin_cases a
  · exact context_12_372512_435790
  · exact context_12_372513_1318838
  · exact context_12_372514_1318892
  · exact context_12_372515_1318950

theorem selected_cut_47154 : selected 9 ⟨1319013, by decide⟩
    (prefixPartial 12 372516) = some ⟨12, 2, 0, 1319013, 372516, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_372516_1319013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372516 ⟨1319013, by decide⟩ :=
  accepted_of_selected 12 372516 ⟨1319013, by decide⟩ ⟨12, 2, 0, 1319013, 372516, 1905, 65536⟩
    (by decide) selected_cut_47154

theorem selected_cut_47155 : selected 9 ⟨1319101, by decide⟩
    (prefixPartial 12 372517) = some ⟨12, 2, 0, 1319101, 372517, 3697, 65536⟩ := by
  decide +kernel

theorem context_12_372517_1319101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372517 ⟨1319101, by decide⟩ :=
  accepted_of_selected 12 372517 ⟨1319101, by decide⟩ ⟨12, 2, 0, 1319101, 372517, 3697, 65536⟩
    (by decide) selected_cut_47155

theorem selected_cut_47156 : selected 9 ⟨1319177, by decide⟩
    (prefixPartial 12 372518) = some ⟨12, 2, 0, 1319177, 372518, 3197, 65536⟩ := by
  decide +kernel

theorem context_12_372518_1319177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372518 ⟨1319177, by decide⟩ :=
  accepted_of_selected 12 372518 ⟨1319177, by decide⟩ ⟨12, 2, 0, 1319177, 372518, 3197, 65536⟩
    (by decide) selected_cut_47156

theorem selected_cut_47157 : selected 9 ⟨1319273, by decide⟩
    (prefixPartial 12 372519) = some ⟨12, 2, 0, 1319273, 372519, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_372519_1319273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372519 ⟨1319273, by decide⟩ :=
  accepted_of_selected 12 372519 ⟨1319273, by decide⟩ ⟨12, 2, 0, 1319273, 372519, 3653, 65536⟩
    (by decide) selected_cut_47157

theorem unmarked_context_11_93129_1319274 : frontier 10 ⟨1319274, by decide⟩
    (prefixCache 11 93129) (prefixPartial 11 93129) = false := by
  decide +kernel

theorem node_context_11_93129_1319274 : EJMOriginalGlobalDAGData.nodes 10 ⟨1319274, by decide⟩ =
    .split (coordinate 11) (![⟨1319013, by decide⟩,⟨1319101, by decide⟩,⟨1319177, by decide⟩,⟨1319273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93129_1319274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93129 ⟨1319274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93129
    ⟨1319274, by decide⟩ (by decide) (![⟨1319013, by decide⟩,⟨1319101, by decide⟩,⟨1319177, by decide⟩,⟨1319273, by decide⟩]) unmarked_context_11_93129_1319274 node_context_11_93129_1319274
  intro a
  fin_cases a
  · exact context_12_372516_1319013
  · exact context_12_372517_1319101
  · exact context_12_372518_1319177
  · exact context_12_372519_1319273

theorem selected_cut_47158 : selected 10 ⟨1319330, by decide⟩
    (prefixPartial 11 93130) = some ⟨11, 2, 0, 1319330, 93130, 2977, 262144⟩ := by
  decide +kernel

theorem context_11_93130_1319330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93130 ⟨1319330, by decide⟩ :=
  accepted_of_selected 11 93130 ⟨1319330, by decide⟩ ⟨11, 2, 0, 1319330, 93130, 2977, 262144⟩
    (by decide) selected_cut_47158

theorem selected_cut_47159 : selected 9 ⟨1319382, by decide⟩
    (prefixPartial 12 372524) = some ⟨12, 2, 0, 1319382, 372524, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_372524_1319382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372524 ⟨1319382, by decide⟩ :=
  accepted_of_selected 12 372524 ⟨1319382, by decide⟩ ⟨12, 2, 0, 1319382, 372524, 2797, 65536⟩
    (by decide) selected_cut_47159

theorem selected_cut_47160 : selected 9 ⟨1319431, by decide⟩
    (prefixPartial 12 372525) = some ⟨12, 2, 0, 1319431, 372525, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_372525_1319431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372525 ⟨1319431, by decide⟩ :=
  accepted_of_selected 12 372525 ⟨1319431, by decide⟩ ⟨12, 2, 0, 1319431, 372525, 2713, 65536⟩
    (by decide) selected_cut_47160

theorem selected_cut_47161 : selected 9 ⟨1319481, by decide⟩
    (prefixPartial 12 372526) = some ⟨12, 2, 0, 1319481, 372526, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_372526_1319481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372526 ⟨1319481, by decide⟩ :=
  accepted_of_selected 12 372526 ⟨1319481, by decide⟩ ⟨12, 2, 0, 1319481, 372526, 2585, 65536⟩
    (by decide) selected_cut_47161

theorem selected_cut_47162 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 372527) = some ⟨12, 1, 0, 903806, 372527, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372527_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372527 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 372527 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 372527, 1, 65536⟩
    (by decide) selected_cut_47162

theorem unmarked_context_11_93131_1319482 : frontier 10 ⟨1319482, by decide⟩
    (prefixCache 11 93131) (prefixPartial 11 93131) = false := by
  decide +kernel

theorem node_context_11_93131_1319482 : EJMOriginalGlobalDAGData.nodes 10 ⟨1319482, by decide⟩ =
    .split (coordinate 11) (![⟨1319382, by decide⟩,⟨1319431, by decide⟩,⟨1319481, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93131_1319482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93131 ⟨1319482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93131
    ⟨1319482, by decide⟩ (by decide) (![⟨1319382, by decide⟩,⟨1319431, by decide⟩,⟨1319481, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93131_1319482 node_context_11_93131_1319482
  intro a
  fin_cases a
  · exact context_12_372524_1319382
  · exact context_12_372525_1319431
  · exact context_12_372526_1319481
  · exact context_12_372527_903806

theorem unmarked_context_10_23282_1319483 : frontier 11 ⟨1319483, by decide⟩
    (prefixCache 10 23282) (prefixPartial 10 23282) = false := by
  decide +kernel

theorem node_context_10_23282_1319483 : EJMOriginalGlobalDAGData.nodes 11 ⟨1319483, by decide⟩ =
    .split (coordinate 10) (![⟨1318951, by decide⟩,⟨1319274, by decide⟩,⟨1319330, by decide⟩,⟨1319482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23282_1319483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23282 ⟨1319483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23282
    ⟨1319483, by decide⟩ (by decide) (![⟨1318951, by decide⟩,⟨1319274, by decide⟩,⟨1319330, by decide⟩,⟨1319482, by decide⟩]) unmarked_context_10_23282_1319483 node_context_10_23282_1319483
  intro a
  fin_cases a
  · exact context_11_93128_1318951
  · exact context_11_93129_1319274
  · exact context_11_93130_1319330
  · exact context_11_93131_1319482

theorem selected_cut_47163 : selected 9 ⟨792260, by decide⟩
    (prefixPartial 12 372528) = some ⟨12, 1, 0, 792260, 372528, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372528_792260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372528 ⟨792260, by decide⟩ :=
  accepted_of_selected 12 372528 ⟨792260, by decide⟩ ⟨12, 1, 0, 792260, 372528, 1, 65536⟩
    (by decide) selected_cut_47163

theorem selected_cut_47164 : selected 9 ⟨1319522, by decide⟩
    (prefixPartial 12 372529) = some ⟨12, 2, 0, 1319522, 372529, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_372529_1319522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372529 ⟨1319522, by decide⟩ :=
  accepted_of_selected 12 372529 ⟨1319522, by decide⟩ ⟨12, 2, 0, 1319522, 372529, 2109, 65536⟩
    (by decide) selected_cut_47164

theorem selected_cut_47165 : selected 9 ⟨1319562, by decide⟩
    (prefixPartial 12 372530) = some ⟨12, 2, 0, 1319562, 372530, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_372530_1319562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372530 ⟨1319562, by decide⟩ :=
  accepted_of_selected 12 372530 ⟨1319562, by decide⟩ ⟨12, 2, 0, 1319562, 372530, 2129, 65536⟩
    (by decide) selected_cut_47165

theorem selected_cut_47166 : selected 9 ⟨1319598, by decide⟩
    (prefixPartial 12 372531) = some ⟨12, 2, 0, 1319598, 372531, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_372531_1319598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372531 ⟨1319598, by decide⟩ :=
  accepted_of_selected 12 372531 ⟨1319598, by decide⟩ ⟨12, 2, 0, 1319598, 372531, 2381, 65536⟩
    (by decide) selected_cut_47166

theorem unmarked_context_11_93132_1319599 : frontier 10 ⟨1319599, by decide⟩
    (prefixCache 11 93132) (prefixPartial 11 93132) = false := by
  decide +kernel

theorem node_context_11_93132_1319599 : EJMOriginalGlobalDAGData.nodes 10 ⟨1319599, by decide⟩ =
    .split (coordinate 11) (![⟨792260, by decide⟩,⟨1319522, by decide⟩,⟨1319562, by decide⟩,⟨1319598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93132_1319599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93132 ⟨1319599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93132
    ⟨1319599, by decide⟩ (by decide) (![⟨792260, by decide⟩,⟨1319522, by decide⟩,⟨1319562, by decide⟩,⟨1319598, by decide⟩]) unmarked_context_11_93132_1319599 node_context_11_93132_1319599
  intro a
  fin_cases a
  · exact context_12_372528_792260
  · exact context_12_372529_1319522
  · exact context_12_372530_1319562
  · exact context_12_372531_1319598

theorem selected_cut_47167 : selected 9 ⟨1319672, by decide⟩
    (prefixPartial 12 372532) = some ⟨12, 2, 0, 1319672, 372532, 2625, 65536⟩ := by
  decide +kernel

theorem context_12_372532_1319672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372532 ⟨1319672, by decide⟩ :=
  accepted_of_selected 12 372532 ⟨1319672, by decide⟩ ⟨12, 2, 0, 1319672, 372532, 2625, 65536⟩
    (by decide) selected_cut_47167

theorem selected_cut_47168 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 372533) = some ⟨12, 1, 0, 689956, 372533, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372533_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372533 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 372533 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 372533, 1, 65536⟩
    (by decide) selected_cut_47168

theorem selected_cut_47169 : selected 9 ⟨1319719, by decide⟩
    (prefixPartial 12 372534) = some ⟨12, 2, 0, 1319719, 372534, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_372534_1319719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372534 ⟨1319719, by decide⟩ :=
  accepted_of_selected 12 372534 ⟨1319719, by decide⟩ ⟨12, 2, 0, 1319719, 372534, 2337, 65536⟩
    (by decide) selected_cut_47169

theorem selected_cut_47170 : selected 9 ⟨1319776, by decide⟩
    (prefixPartial 12 372535) = some ⟨12, 2, 0, 1319776, 372535, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_372535_1319776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372535 ⟨1319776, by decide⟩ :=
  accepted_of_selected 12 372535 ⟨1319776, by decide⟩ ⟨12, 2, 0, 1319776, 372535, 2561, 65536⟩
    (by decide) selected_cut_47170

theorem unmarked_context_11_93133_1319777 : frontier 10 ⟨1319777, by decide⟩
    (prefixCache 11 93133) (prefixPartial 11 93133) = false := by
  decide +kernel

theorem node_context_11_93133_1319777 : EJMOriginalGlobalDAGData.nodes 10 ⟨1319777, by decide⟩ =
    .split (coordinate 11) (![⟨1319672, by decide⟩,⟨689956, by decide⟩,⟨1319719, by decide⟩,⟨1319776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93133_1319777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93133 ⟨1319777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93133
    ⟨1319777, by decide⟩ (by decide) (![⟨1319672, by decide⟩,⟨689956, by decide⟩,⟨1319719, by decide⟩,⟨1319776, by decide⟩]) unmarked_context_11_93133_1319777 node_context_11_93133_1319777
  intro a
  fin_cases a
  · exact context_12_372532_1319672
  · exact context_12_372533_689956
  · exact context_12_372534_1319719
  · exact context_12_372535_1319776

theorem selected_cut_47171 : selected 9 ⟨1066629, by decide⟩
    (prefixPartial 12 372536) = some ⟨12, 1, 0, 1066629, 372536, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372536_1066629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372536 ⟨1066629, by decide⟩ :=
  accepted_of_selected 12 372536 ⟨1066629, by decide⟩ ⟨12, 1, 0, 1066629, 372536, 1, 65536⟩
    (by decide) selected_cut_47171

theorem selected_cut_47172 : selected 9 ⟨1319818, by decide⟩
    (prefixPartial 12 372537) = some ⟨12, 2, 0, 1319818, 372537, 2173, 65536⟩ := by
  decide +kernel

theorem context_12_372537_1319818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372537 ⟨1319818, by decide⟩ :=
  accepted_of_selected 12 372537 ⟨1319818, by decide⟩ ⟨12, 2, 0, 1319818, 372537, 2173, 65536⟩
    (by decide) selected_cut_47172

theorem selected_cut_47173 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 372538) = some ⟨12, 1, 0, 662655, 372538, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372538_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372538 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 372538 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 372538, 1, 65536⟩
    (by decide) selected_cut_47173

theorem selected_cut_47174 : selected 9 ⟨1319853, by decide⟩
    (prefixPartial 12 372539) = some ⟨12, 2, 0, 1319853, 372539, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_372539_1319853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372539 ⟨1319853, by decide⟩ :=
  accepted_of_selected 12 372539 ⟨1319853, by decide⟩ ⟨12, 2, 0, 1319853, 372539, 2145, 65536⟩
    (by decide) selected_cut_47174

theorem unmarked_context_11_93134_1319854 : frontier 10 ⟨1319854, by decide⟩
    (prefixCache 11 93134) (prefixPartial 11 93134) = false := by
  decide +kernel

theorem node_context_11_93134_1319854 : EJMOriginalGlobalDAGData.nodes 10 ⟨1319854, by decide⟩ =
    .split (coordinate 11) (![⟨1066629, by decide⟩,⟨1319818, by decide⟩,⟨662655, by decide⟩,⟨1319853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93134_1319854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93134 ⟨1319854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93134
    ⟨1319854, by decide⟩ (by decide) (![⟨1066629, by decide⟩,⟨1319818, by decide⟩,⟨662655, by decide⟩,⟨1319853, by decide⟩]) unmarked_context_11_93134_1319854 node_context_11_93134_1319854
  intro a
  fin_cases a
  · exact context_12_372536_1066629
  · exact context_12_372537_1319818
  · exact context_12_372538_662655
  · exact context_12_372539_1319853

theorem selected_cut_47175 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 93135) = some ⟨11, 1, 0, 977886, 93135, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93135_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93135 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 93135 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 93135, 1, 262144⟩
    (by decide) selected_cut_47175

theorem unmarked_context_10_23283_1319855 : frontier 11 ⟨1319855, by decide⟩
    (prefixCache 10 23283) (prefixPartial 10 23283) = false := by
  decide +kernel

theorem node_context_10_23283_1319855 : EJMOriginalGlobalDAGData.nodes 11 ⟨1319855, by decide⟩ =
    .split (coordinate 10) (![⟨1319599, by decide⟩,⟨1319777, by decide⟩,⟨1319854, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23283_1319855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23283 ⟨1319855, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23283
    ⟨1319855, by decide⟩ (by decide) (![⟨1319599, by decide⟩,⟨1319777, by decide⟩,⟨1319854, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23283_1319855 node_context_10_23283_1319855
  intro a
  fin_cases a
  · exact context_11_93132_1319599
  · exact context_11_93133_1319777
  · exact context_11_93134_1319854
  · exact context_11_93135_977886

theorem unmarked_context_9_5820_1319856 : frontier 12 ⟨1319856, by decide⟩
    (prefixCache 9 5820) (prefixPartial 9 5820) = false := by
  decide +kernel

theorem node_context_9_5820_1319856 : EJMOriginalGlobalDAGData.nodes 12 ⟨1319856, by decide⟩ =
    .split (coordinate 9) (![⟨1318017, by decide⟩,⟨1318784, by decide⟩,⟨1319483, by decide⟩,⟨1319855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5820_1319856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5820 ⟨1319856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5820
    ⟨1319856, by decide⟩ (by decide) (![⟨1318017, by decide⟩,⟨1318784, by decide⟩,⟨1319483, by decide⟩,⟨1319855, by decide⟩]) unmarked_context_9_5820_1319856 node_context_9_5820_1319856
  intro a
  fin_cases a
  · exact context_10_23280_1318017
  · exact context_10_23281_1318784
  · exact context_10_23282_1319483
  · exact context_10_23283_1319855

theorem selected_cut_47176 : selected 10 ⟨1319917, by decide⟩
    (prefixPartial 11 93136) = some ⟨11, 2, 0, 1319917, 93136, 3821, 262144⟩ := by
  decide +kernel

theorem context_11_93136_1319917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93136 ⟨1319917, by decide⟩ :=
  accepted_of_selected 11 93136 ⟨1319917, by decide⟩ ⟨11, 2, 0, 1319917, 93136, 3821, 262144⟩
    (by decide) selected_cut_47176

theorem selected_cut_47177 : selected 9 ⟨1319956, by decide⟩
    (prefixPartial 12 372548) = some ⟨12, 2, 0, 1319956, 372548, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_372548_1319956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372548 ⟨1319956, by decide⟩ :=
  accepted_of_selected 12 372548 ⟨1319956, by decide⟩ ⟨12, 2, 0, 1319956, 372548, 2241, 65536⟩
    (by decide) selected_cut_47177

theorem selected_cut_47178 : selected 9 ⟨1257136, by decide⟩
    (prefixPartial 12 372549) = some ⟨12, 1, 0, 1257136, 372549, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372549_1257136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372549 ⟨1257136, by decide⟩ :=
  accepted_of_selected 12 372549 ⟨1257136, by decide⟩ ⟨12, 1, 0, 1257136, 372549, 1, 65536⟩
    (by decide) selected_cut_47178

theorem selected_cut_47179 : selected 9 ⟨1319992, by decide⟩
    (prefixPartial 12 372550) = some ⟨12, 2, 0, 1319992, 372550, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_372550_1319992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372550 ⟨1319992, by decide⟩ :=
  accepted_of_selected 12 372550 ⟨1319992, by decide⟩ ⟨12, 2, 0, 1319992, 372550, 1941, 65536⟩
    (by decide) selected_cut_47179

theorem selected_cut_47180 : selected 9 ⟨1320031, by decide⟩
    (prefixPartial 12 372551) = some ⟨12, 2, 0, 1320031, 372551, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_372551_1320031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372551 ⟨1320031, by decide⟩ :=
  accepted_of_selected 12 372551 ⟨1320031, by decide⟩ ⟨12, 2, 0, 1320031, 372551, 2045, 65536⟩
    (by decide) selected_cut_47180

theorem unmarked_context_11_93137_1320032 : frontier 10 ⟨1320032, by decide⟩
    (prefixCache 11 93137) (prefixPartial 11 93137) = false := by
  decide +kernel

theorem node_context_11_93137_1320032 : EJMOriginalGlobalDAGData.nodes 10 ⟨1320032, by decide⟩ =
    .split (coordinate 11) (![⟨1319956, by decide⟩,⟨1257136, by decide⟩,⟨1319992, by decide⟩,⟨1320031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93137_1320032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93137 ⟨1320032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93137
    ⟨1320032, by decide⟩ (by decide) (![⟨1319956, by decide⟩,⟨1257136, by decide⟩,⟨1319992, by decide⟩,⟨1320031, by decide⟩]) unmarked_context_11_93137_1320032 node_context_11_93137_1320032
  intro a
  fin_cases a
  · exact context_12_372548_1319956
  · exact context_12_372549_1257136
  · exact context_12_372550_1319992
  · exact context_12_372551_1320031

theorem selected_cut_47181 : selected 9 ⟨1320068, by decide⟩
    (prefixPartial 12 372552) = some ⟨12, 2, 0, 1320068, 372552, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_372552_1320068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372552 ⟨1320068, by decide⟩ :=
  accepted_of_selected 12 372552 ⟨1320068, by decide⟩ ⟨12, 2, 0, 1320068, 372552, 1865, 65536⟩
    (by decide) selected_cut_47181

theorem selected_cut_47182 : selected 9 ⟨1320097, by decide⟩
    (prefixPartial 12 372553) = some ⟨12, 2, 0, 1320097, 372553, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_372553_1320097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372553 ⟨1320097, by decide⟩ :=
  accepted_of_selected 12 372553 ⟨1320097, by decide⟩ ⟨12, 2, 0, 1320097, 372553, 1769, 65536⟩
    (by decide) selected_cut_47182

theorem selected_cut_47183 : selected 9 ⟨1320125, by decide⟩
    (prefixPartial 12 372554) = some ⟨12, 2, 0, 1320125, 372554, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_372554_1320125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372554 ⟨1320125, by decide⟩ :=
  accepted_of_selected 12 372554 ⟨1320125, by decide⟩ ⟨12, 2, 0, 1320125, 372554, 1577, 65536⟩
    (by decide) selected_cut_47183

theorem selected_cut_47184 : selected 9 ⟨1320153, by decide⟩
    (prefixPartial 12 372555) = some ⟨12, 2, 0, 1320153, 372555, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_372555_1320153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372555 ⟨1320153, by decide⟩ :=
  accepted_of_selected 12 372555 ⟨1320153, by decide⟩ ⟨12, 2, 0, 1320153, 372555, 1697, 65536⟩
    (by decide) selected_cut_47184

theorem unmarked_context_11_93138_1320154 : frontier 10 ⟨1320154, by decide⟩
    (prefixCache 11 93138) (prefixPartial 11 93138) = false := by
  decide +kernel

theorem node_context_11_93138_1320154 : EJMOriginalGlobalDAGData.nodes 10 ⟨1320154, by decide⟩ =
    .split (coordinate 11) (![⟨1320068, by decide⟩,⟨1320097, by decide⟩,⟨1320125, by decide⟩,⟨1320153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93138_1320154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93138 ⟨1320154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93138
    ⟨1320154, by decide⟩ (by decide) (![⟨1320068, by decide⟩,⟨1320097, by decide⟩,⟨1320125, by decide⟩,⟨1320153, by decide⟩]) unmarked_context_11_93138_1320154 node_context_11_93138_1320154
  intro a
  fin_cases a
  · exact context_12_372552_1320068
  · exact context_12_372553_1320097
  · exact context_12_372554_1320125
  · exact context_12_372555_1320153

theorem selected_cut_47185 : selected 9 ⟨1320182, by decide⟩
    (prefixPartial 12 372556) = some ⟨12, 2, 0, 1320182, 372556, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_372556_1320182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372556 ⟨1320182, by decide⟩ :=
  accepted_of_selected 12 372556 ⟨1320182, by decide⟩ ⟨12, 2, 0, 1320182, 372556, 1689, 65536⟩
    (by decide) selected_cut_47185

theorem selected_cut_47186 : selected 9 ⟨1320214, by decide⟩
    (prefixPartial 12 372557) = some ⟨12, 2, 0, 1320214, 372557, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_372557_1320214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372557 ⟨1320214, by decide⟩ :=
  accepted_of_selected 12 372557 ⟨1320214, by decide⟩ ⟨12, 2, 0, 1320214, 372557, 1501, 65536⟩
    (by decide) selected_cut_47186

theorem selected_cut_47187 : selected 9 ⟨1320234, by decide⟩
    (prefixPartial 12 372558) = some ⟨12, 2, 0, 1320234, 372558, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_372558_1320234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372558 ⟨1320234, by decide⟩ :=
  accepted_of_selected 12 372558 ⟨1320234, by decide⟩ ⟨12, 2, 0, 1320234, 372558, 1465, 65536⟩
    (by decide) selected_cut_47187

theorem selected_cut_47188 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 372559) = some ⟨12, 1, 0, 903806, 372559, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372559_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372559 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 372559 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 372559, 1, 65536⟩
    (by decide) selected_cut_47188

theorem unmarked_context_11_93139_1320235 : frontier 10 ⟨1320235, by decide⟩
    (prefixCache 11 93139) (prefixPartial 11 93139) = false := by
  decide +kernel

theorem node_context_11_93139_1320235 : EJMOriginalGlobalDAGData.nodes 10 ⟨1320235, by decide⟩ =
    .split (coordinate 11) (![⟨1320182, by decide⟩,⟨1320214, by decide⟩,⟨1320234, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93139_1320235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93139 ⟨1320235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93139
    ⟨1320235, by decide⟩ (by decide) (![⟨1320182, by decide⟩,⟨1320214, by decide⟩,⟨1320234, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_93139_1320235 node_context_11_93139_1320235
  intro a
  fin_cases a
  · exact context_12_372556_1320182
  · exact context_12_372557_1320214
  · exact context_12_372558_1320234
  · exact context_12_372559_903806

theorem unmarked_context_10_23284_1320236 : frontier 11 ⟨1320236, by decide⟩
    (prefixCache 10 23284) (prefixPartial 10 23284) = false := by
  decide +kernel

theorem node_context_10_23284_1320236 : EJMOriginalGlobalDAGData.nodes 11 ⟨1320236, by decide⟩ =
    .split (coordinate 10) (![⟨1319917, by decide⟩,⟨1320032, by decide⟩,⟨1320154, by decide⟩,⟨1320235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23284_1320236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23284 ⟨1320236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23284
    ⟨1320236, by decide⟩ (by decide) (![⟨1319917, by decide⟩,⟨1320032, by decide⟩,⟨1320154, by decide⟩,⟨1320235, by decide⟩]) unmarked_context_10_23284_1320236 node_context_10_23284_1320236
  intro a
  fin_cases a
  · exact context_11_93136_1319917
  · exact context_11_93137_1320032
  · exact context_11_93138_1320154
  · exact context_11_93139_1320235

theorem selected_cut_47189 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23285) = some ⟨10, 1, 0, 893098, 23285, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23285_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23285 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23285 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23285, 1, 1048576⟩
    (by decide) selected_cut_47189

theorem selected_cut_47190 : selected 9 ⟨1320261, by decide⟩
    (prefixPartial 12 372576) = some ⟨12, 2, 0, 1320261, 372576, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_372576_1320261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372576 ⟨1320261, by decide⟩ :=
  accepted_of_selected 12 372576 ⟨1320261, by decide⟩ ⟨12, 2, 0, 1320261, 372576, 1637, 65536⟩
    (by decide) selected_cut_47190

theorem selected_cut_47191 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 372577) = some ⟨12, 1, 0, 1256866, 372577, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372577_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372577 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 372577 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 372577, 1, 65536⟩
    (by decide) selected_cut_47191

theorem selected_cut_47192 : selected 9 ⟨1320289, by decide⟩
    (prefixPartial 12 372578) = some ⟨12, 2, 0, 1320289, 372578, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_372578_1320289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372578 ⟨1320289, by decide⟩ :=
  accepted_of_selected 12 372578 ⟨1320289, by decide⟩ ⟨12, 2, 0, 1320289, 372578, 1501, 65536⟩
    (by decide) selected_cut_47192

theorem selected_cut_47193 : selected 9 ⟨1320316, by decide⟩
    (prefixPartial 12 372579) = some ⟨12, 2, 0, 1320316, 372579, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_372579_1320316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372579 ⟨1320316, by decide⟩ :=
  accepted_of_selected 12 372579 ⟨1320316, by decide⟩ ⟨12, 2, 0, 1320316, 372579, 1521, 65536⟩
    (by decide) selected_cut_47193

theorem unmarked_context_11_93144_1320317 : frontier 10 ⟨1320317, by decide⟩
    (prefixCache 11 93144) (prefixPartial 11 93144) = false := by
  decide +kernel

theorem node_context_11_93144_1320317 : EJMOriginalGlobalDAGData.nodes 10 ⟨1320317, by decide⟩ =
    .split (coordinate 11) (![⟨1320261, by decide⟩,⟨1256866, by decide⟩,⟨1320289, by decide⟩,⟨1320316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93144_1320317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93144 ⟨1320317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93144
    ⟨1320317, by decide⟩ (by decide) (![⟨1320261, by decide⟩,⟨1256866, by decide⟩,⟨1320289, by decide⟩,⟨1320316, by decide⟩]) unmarked_context_11_93144_1320317 node_context_11_93144_1320317
  intro a
  fin_cases a
  · exact context_12_372576_1320261
  · exact context_12_372577_1256866
  · exact context_12_372578_1320289
  · exact context_12_372579_1320316

theorem selected_cut_47194 : selected 9 ⟨1320344, by decide⟩
    (prefixPartial 12 372580) = some ⟨12, 2, 0, 1320344, 372580, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_372580_1320344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372580 ⟨1320344, by decide⟩ :=
  accepted_of_selected 12 372580 ⟨1320344, by decide⟩ ⟨12, 2, 0, 1320344, 372580, 1657, 65536⟩
    (by decide) selected_cut_47194

theorem selected_cut_47195 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 372581) = some ⟨12, 1, 0, 1256866, 372581, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372581_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372581 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 372581 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 372581, 1, 65536⟩
    (by decide) selected_cut_47195

theorem selected_cut_47196 : selected 9 ⟨1320369, by decide⟩
    (prefixPartial 12 372582) = some ⟨12, 2, 0, 1320369, 372582, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_372582_1320369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372582 ⟨1320369, by decide⟩ :=
  accepted_of_selected 12 372582 ⟨1320369, by decide⟩ ⟨12, 2, 0, 1320369, 372582, 1409, 65536⟩
    (by decide) selected_cut_47196

theorem selected_cut_47197 : selected 9 ⟨1320395, by decide⟩
    (prefixPartial 12 372583) = some ⟨12, 2, 0, 1320395, 372583, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_372583_1320395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372583 ⟨1320395, by decide⟩ :=
  accepted_of_selected 12 372583 ⟨1320395, by decide⟩ ⟨12, 2, 0, 1320395, 372583, 1569, 65536⟩
    (by decide) selected_cut_47197

theorem unmarked_context_11_93145_1320396 : frontier 10 ⟨1320396, by decide⟩
    (prefixCache 11 93145) (prefixPartial 11 93145) = false := by
  decide +kernel

theorem node_context_11_93145_1320396 : EJMOriginalGlobalDAGData.nodes 10 ⟨1320396, by decide⟩ =
    .split (coordinate 11) (![⟨1320344, by decide⟩,⟨1256866, by decide⟩,⟨1320369, by decide⟩,⟨1320395, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93145_1320396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93145 ⟨1320396, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93145
    ⟨1320396, by decide⟩ (by decide) (![⟨1320344, by decide⟩,⟨1256866, by decide⟩,⟨1320369, by decide⟩,⟨1320395, by decide⟩]) unmarked_context_11_93145_1320396 node_context_11_93145_1320396
  intro a
  fin_cases a
  · exact context_12_372580_1320344
  · exact context_12_372581_1256866
  · exact context_12_372582_1320369
  · exact context_12_372583_1320395

theorem selected_cut_47198 : selected 10 ⟨1320420, by decide⟩
    (prefixPartial 11 93146) = some ⟨11, 2, 0, 1320420, 93146, 1317, 262144⟩ := by
  decide +kernel

theorem context_11_93146_1320420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93146 ⟨1320420, by decide⟩ :=
  accepted_of_selected 11 93146 ⟨1320420, by decide⟩ ⟨11, 2, 0, 1320420, 93146, 1317, 262144⟩
    (by decide) selected_cut_47198

theorem selected_cut_47199 : selected 10 ⟨1320465, by decide⟩
    (prefixPartial 11 93147) = some ⟨11, 2, 0, 1320465, 93147, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_93147_1320465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93147 ⟨1320465, by decide⟩ :=
  accepted_of_selected 11 93147 ⟨1320465, by decide⟩ ⟨11, 2, 0, 1320465, 93147, 2461, 262144⟩
    (by decide) selected_cut_47199

theorem unmarked_context_10_23286_1320466 : frontier 11 ⟨1320466, by decide⟩
    (prefixCache 10 23286) (prefixPartial 10 23286) = false := by
  decide +kernel

theorem node_context_10_23286_1320466 : EJMOriginalGlobalDAGData.nodes 11 ⟨1320466, by decide⟩ =
    .split (coordinate 10) (![⟨1320317, by decide⟩,⟨1320396, by decide⟩,⟨1320420, by decide⟩,⟨1320465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23286_1320466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23286 ⟨1320466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23286
    ⟨1320466, by decide⟩ (by decide) (![⟨1320317, by decide⟩,⟨1320396, by decide⟩,⟨1320420, by decide⟩,⟨1320465, by decide⟩]) unmarked_context_10_23286_1320466 node_context_10_23286_1320466
  intro a
  fin_cases a
  · exact context_11_93144_1320317
  · exact context_11_93145_1320396
  · exact context_11_93146_1320420
  · exact context_11_93147_1320465

theorem selected_cut_47200 : selected 10 ⟨1320528, by decide⟩
    (prefixPartial 11 93148) = some ⟨11, 2, 0, 1320528, 93148, 3589, 262144⟩ := by
  decide +kernel

theorem context_11_93148_1320528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93148 ⟨1320528, by decide⟩ :=
  accepted_of_selected 11 93148 ⟨1320528, by decide⟩ ⟨11, 2, 0, 1320528, 93148, 3589, 262144⟩
    (by decide) selected_cut_47200

theorem selected_cut_47201 : selected 10 ⟨1320603, by decide⟩
    (prefixPartial 11 93149) = some ⟨11, 2, 0, 1320603, 93149, 3565, 262144⟩ := by
  decide +kernel

theorem context_11_93149_1320603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93149 ⟨1320603, by decide⟩ :=
  accepted_of_selected 11 93149 ⟨1320603, by decide⟩ ⟨11, 2, 0, 1320603, 93149, 3565, 262144⟩
    (by decide) selected_cut_47201

theorem selected_cut_47202 : selected 10 ⟨1320633, by decide⟩
    (prefixPartial 11 93150) = some ⟨11, 2, 0, 1320633, 93150, 1865, 262144⟩ := by
  decide +kernel

theorem context_11_93150_1320633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93150 ⟨1320633, by decide⟩ :=
  accepted_of_selected 11 93150 ⟨1320633, by decide⟩ ⟨11, 2, 0, 1320633, 93150, 1865, 262144⟩
    (by decide) selected_cut_47202

theorem selected_cut_47203 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 93151) = some ⟨11, 1, 0, 977886, 93151, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93151_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93151 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 93151 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 93151, 1, 262144⟩
    (by decide) selected_cut_47203

theorem unmarked_context_10_23287_1320634 : frontier 11 ⟨1320634, by decide⟩
    (prefixCache 10 23287) (prefixPartial 10 23287) = false := by
  decide +kernel

theorem node_context_10_23287_1320634 : EJMOriginalGlobalDAGData.nodes 11 ⟨1320634, by decide⟩ =
    .split (coordinate 10) (![⟨1320528, by decide⟩,⟨1320603, by decide⟩,⟨1320633, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23287_1320634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23287 ⟨1320634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23287
    ⟨1320634, by decide⟩ (by decide) (![⟨1320528, by decide⟩,⟨1320603, by decide⟩,⟨1320633, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23287_1320634 node_context_10_23287_1320634
  intro a
  fin_cases a
  · exact context_11_93148_1320528
  · exact context_11_93149_1320603
  · exact context_11_93150_1320633
  · exact context_11_93151_977886

theorem unmarked_context_9_5821_1320635 : frontier 12 ⟨1320635, by decide⟩
    (prefixCache 9 5821) (prefixPartial 9 5821) = false := by
  decide +kernel

theorem node_context_9_5821_1320635 : EJMOriginalGlobalDAGData.nodes 12 ⟨1320635, by decide⟩ =
    .split (coordinate 9) (![⟨1320236, by decide⟩,⟨893098, by decide⟩,⟨1320466, by decide⟩,⟨1320634, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5821_1320635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5821 ⟨1320635, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5821
    ⟨1320635, by decide⟩ (by decide) (![⟨1320236, by decide⟩,⟨893098, by decide⟩,⟨1320466, by decide⟩,⟨1320634, by decide⟩]) unmarked_context_9_5821_1320635 node_context_9_5821_1320635
  intro a
  fin_cases a
  · exact context_10_23284_1320236
  · exact context_10_23285_893098
  · exact context_10_23286_1320466
  · exact context_10_23287_1320634

theorem selected_cut_47204 : selected 10 ⟨1320651, by decide⟩
    (prefixPartial 11 93152) = some ⟨11, 2, 0, 1320651, 93152, 1113, 262144⟩ := by
  decide +kernel

theorem context_11_93152_1320651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93152 ⟨1320651, by decide⟩ :=
  accepted_of_selected 11 93152 ⟨1320651, by decide⟩ ⟨11, 2, 0, 1320651, 93152, 1113, 262144⟩
    (by decide) selected_cut_47204

theorem selected_cut_47205 : selected 10 ⟨1320723, by decide⟩
    (prefixPartial 11 93153) = some ⟨11, 2, 0, 1320723, 93153, 3781, 262144⟩ := by
  decide +kernel

theorem context_11_93153_1320723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93153 ⟨1320723, by decide⟩ :=
  accepted_of_selected 11 93153 ⟨1320723, by decide⟩ ⟨11, 2, 0, 1320723, 93153, 3781, 262144⟩
    (by decide) selected_cut_47205

theorem selected_cut_47206 : selected 10 ⟨1320780, by decide⟩
    (prefixPartial 11 93154) = some ⟨11, 2, 0, 1320780, 93154, 2961, 262144⟩ := by
  decide +kernel

theorem context_11_93154_1320780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93154 ⟨1320780, by decide⟩ :=
  accepted_of_selected 11 93154 ⟨1320780, by decide⟩ ⟨11, 2, 0, 1320780, 93154, 2961, 262144⟩
    (by decide) selected_cut_47206

theorem selected_cut_47207 : selected 10 ⟨1320813, by decide⟩
    (prefixPartial 11 93155) = some ⟨11, 2, 0, 1320813, 93155, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_93155_1320813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93155 ⟨1320813, by decide⟩ :=
  accepted_of_selected 11 93155 ⟨1320813, by decide⟩ ⟨11, 2, 0, 1320813, 93155, 1857, 262144⟩
    (by decide) selected_cut_47207

theorem unmarked_context_10_23288_1320814 : frontier 11 ⟨1320814, by decide⟩
    (prefixCache 10 23288) (prefixPartial 10 23288) = false := by
  decide +kernel

theorem node_context_10_23288_1320814 : EJMOriginalGlobalDAGData.nodes 11 ⟨1320814, by decide⟩ =
    .split (coordinate 10) (![⟨1320651, by decide⟩,⟨1320723, by decide⟩,⟨1320780, by decide⟩,⟨1320813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23288_1320814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23288 ⟨1320814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23288
    ⟨1320814, by decide⟩ (by decide) (![⟨1320651, by decide⟩,⟨1320723, by decide⟩,⟨1320780, by decide⟩,⟨1320813, by decide⟩]) unmarked_context_10_23288_1320814 node_context_10_23288_1320814
  intro a
  fin_cases a
  · exact context_11_93152_1320651
  · exact context_11_93153_1320723
  · exact context_11_93154_1320780
  · exact context_11_93155_1320813

theorem selected_cut_47208 : selected 10 ⟨1320863, by decide⟩
    (prefixPartial 11 93156) = some ⟨11, 2, 0, 1320863, 93156, 2793, 262144⟩ := by
  decide +kernel

theorem context_11_93156_1320863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93156 ⟨1320863, by decide⟩ :=
  accepted_of_selected 11 93156 ⟨1320863, by decide⟩ ⟨11, 2, 0, 1320863, 93156, 2793, 262144⟩
    (by decide) selected_cut_47208

theorem selected_cut_47209 : selected 10 ⟨1320888, by decide⟩
    (prefixPartial 11 93157) = some ⟨11, 2, 0, 1320888, 93157, 985, 262144⟩ := by
  decide +kernel

theorem context_11_93157_1320888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93157 ⟨1320888, by decide⟩ :=
  accepted_of_selected 11 93157 ⟨1320888, by decide⟩ ⟨11, 2, 0, 1320888, 93157, 985, 262144⟩
    (by decide) selected_cut_47209

theorem selected_cut_47210 : selected 10 ⟨1320921, by decide⟩
    (prefixPartial 11 93158) = some ⟨11, 2, 0, 1320921, 93158, 2209, 262144⟩ := by
  decide +kernel

theorem context_11_93158_1320921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93158 ⟨1320921, by decide⟩ :=
  accepted_of_selected 11 93158 ⟨1320921, by decide⟩ ⟨11, 2, 0, 1320921, 93158, 2209, 262144⟩
    (by decide) selected_cut_47210

theorem selected_cut_47211 : selected 10 ⟨1320951, by decide⟩
    (prefixPartial 11 93159) = some ⟨11, 2, 0, 1320951, 93159, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_93159_1320951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93159 ⟨1320951, by decide⟩ :=
  accepted_of_selected 11 93159 ⟨1320951, by decide⟩ ⟨11, 2, 0, 1320951, 93159, 1413, 262144⟩
    (by decide) selected_cut_47211

theorem unmarked_context_10_23289_1320952 : frontier 11 ⟨1320952, by decide⟩
    (prefixCache 10 23289) (prefixPartial 10 23289) = false := by
  decide +kernel

theorem node_context_10_23289_1320952 : EJMOriginalGlobalDAGData.nodes 11 ⟨1320952, by decide⟩ =
    .split (coordinate 10) (![⟨1320863, by decide⟩,⟨1320888, by decide⟩,⟨1320921, by decide⟩,⟨1320951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23289_1320952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23289 ⟨1320952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23289
    ⟨1320952, by decide⟩ (by decide) (![⟨1320863, by decide⟩,⟨1320888, by decide⟩,⟨1320921, by decide⟩,⟨1320951, by decide⟩]) unmarked_context_10_23289_1320952 node_context_10_23289_1320952
  intro a
  fin_cases a
  · exact context_11_93156_1320863
  · exact context_11_93157_1320888
  · exact context_11_93158_1320921
  · exact context_11_93159_1320951

theorem selected_cut_47212 : selected 11 ⟨1320994, by decide⟩
    (prefixPartial 10 23290) = some ⟨10, 2, 0, 1320994, 23290, 2301, 1048576⟩ := by
  decide +kernel

theorem context_10_23290_1320994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23290 ⟨1320994, by decide⟩ :=
  accepted_of_selected 10 23290 ⟨1320994, by decide⟩ ⟨10, 2, 0, 1320994, 23290, 2301, 1048576⟩
    (by decide) selected_cut_47212

theorem selected_cut_47213 : selected 11 ⟨1321052, by decide⟩
    (prefixPartial 10 23291) = some ⟨10, 2, 0, 1321052, 23291, 3181, 1048576⟩ := by
  decide +kernel

theorem context_10_23291_1321052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23291 ⟨1321052, by decide⟩ :=
  accepted_of_selected 10 23291 ⟨1321052, by decide⟩ ⟨10, 2, 0, 1321052, 23291, 3181, 1048576⟩
    (by decide) selected_cut_47213

theorem unmarked_context_9_5822_1321053 : frontier 12 ⟨1321053, by decide⟩
    (prefixCache 9 5822) (prefixPartial 9 5822) = false := by
  decide +kernel

theorem node_context_9_5822_1321053 : EJMOriginalGlobalDAGData.nodes 12 ⟨1321053, by decide⟩ =
    .split (coordinate 9) (![⟨1320814, by decide⟩,⟨1320952, by decide⟩,⟨1320994, by decide⟩,⟨1321052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5822_1321053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5822 ⟨1321053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5822
    ⟨1321053, by decide⟩ (by decide) (![⟨1320814, by decide⟩,⟨1320952, by decide⟩,⟨1320994, by decide⟩,⟨1321052, by decide⟩]) unmarked_context_9_5822_1321053 node_context_9_5822_1321053
  intro a
  fin_cases a
  · exact context_10_23288_1320814
  · exact context_10_23289_1320952
  · exact context_10_23290_1320994
  · exact context_10_23291_1321052

theorem selected_cut_47214 : selected 11 ⟨1321098, by decide⟩
    (prefixPartial 10 23292) = some ⟨10, 2, 0, 1321098, 23292, 2729, 1048576⟩ := by
  decide +kernel

theorem context_10_23292_1321098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23292 ⟨1321098, by decide⟩ :=
  accepted_of_selected 10 23292 ⟨1321098, by decide⟩ ⟨10, 2, 0, 1321098, 23292, 2729, 1048576⟩
    (by decide) selected_cut_47214

theorem selected_cut_47215 : selected 11 ⟨1321126, by decide⟩
    (prefixPartial 10 23293) = some ⟨10, 2, 0, 1321126, 23293, 1593, 1048576⟩ := by
  decide +kernel

theorem context_10_23293_1321126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23293 ⟨1321126, by decide⟩ :=
  accepted_of_selected 10 23293 ⟨1321126, by decide⟩ ⟨10, 2, 0, 1321126, 23293, 1593, 1048576⟩
    (by decide) selected_cut_47215

theorem selected_cut_47216 : selected 11 ⟨1321158, by decide⟩
    (prefixPartial 10 23294) = some ⟨10, 2, 0, 1321158, 23294, 985, 1048576⟩ := by
  decide +kernel

theorem context_10_23294_1321158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23294 ⟨1321158, by decide⟩ :=
  accepted_of_selected 10 23294 ⟨1321158, by decide⟩ ⟨10, 2, 0, 1321158, 23294, 985, 1048576⟩
    (by decide) selected_cut_47216

theorem selected_cut_47217 : selected 11 ⟨1321170, by decide⟩
    (prefixPartial 10 23295) = some ⟨10, 2, 0, 1321170, 23295, 117, 1048576⟩ := by
  decide +kernel

theorem context_10_23295_1321170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23295 ⟨1321170, by decide⟩ :=
  accepted_of_selected 10 23295 ⟨1321170, by decide⟩ ⟨10, 2, 0, 1321170, 23295, 117, 1048576⟩
    (by decide) selected_cut_47217

theorem unmarked_context_9_5823_1321171 : frontier 12 ⟨1321171, by decide⟩
    (prefixCache 9 5823) (prefixPartial 9 5823) = false := by
  decide +kernel

theorem node_context_9_5823_1321171 : EJMOriginalGlobalDAGData.nodes 12 ⟨1321171, by decide⟩ =
    .split (coordinate 9) (![⟨1321098, by decide⟩,⟨1321126, by decide⟩,⟨1321158, by decide⟩,⟨1321170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5823_1321171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5823 ⟨1321171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5823
    ⟨1321171, by decide⟩ (by decide) (![⟨1321098, by decide⟩,⟨1321126, by decide⟩,⟨1321158, by decide⟩,⟨1321170, by decide⟩]) unmarked_context_9_5823_1321171 node_context_9_5823_1321171
  intro a
  fin_cases a
  · exact context_10_23292_1321098
  · exact context_10_23293_1321126
  · exact context_10_23294_1321158
  · exact context_10_23295_1321170

theorem unmarked_context_8_1455_1321172 : frontier 13 ⟨1321172, by decide⟩
    (prefixCache 8 1455) (prefixPartial 8 1455) = false := by
  decide +kernel

theorem node_context_8_1455_1321172 : EJMOriginalGlobalDAGData.nodes 13 ⟨1321172, by decide⟩ =
    .split (coordinate 8) (![⟨1319856, by decide⟩,⟨1320635, by decide⟩,⟨1321053, by decide⟩,⟨1321171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1455_1321172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1455 ⟨1321172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1455
    ⟨1321172, by decide⟩ (by decide) (![⟨1319856, by decide⟩,⟨1320635, by decide⟩,⟨1321053, by decide⟩,⟨1321171, by decide⟩]) unmarked_context_8_1455_1321172 node_context_8_1455_1321172
  intro a
  fin_cases a
  · exact context_9_5820_1319856
  · exact context_9_5821_1320635
  · exact context_9_5822_1321053
  · exact context_9_5823_1321171

theorem unmarked_context_7_363_1321173 : frontier 14 ⟨1321173, by decide⟩
    (prefixCache 7 363) (prefixPartial 7 363) = false := by
  decide +kernel

theorem node_context_7_363_1321173 : EJMOriginalGlobalDAGData.nodes 14 ⟨1321173, by decide⟩ =
    .split (coordinate 7) (![⟨1310882, by decide⟩,⟨1314163, by decide⟩,⟨1317501, by decide⟩,⟨1321172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_363_1321173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 363 ⟨1321173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 363
    ⟨1321173, by decide⟩ (by decide) (![⟨1310882, by decide⟩,⟨1314163, by decide⟩,⟨1317501, by decide⟩,⟨1321172, by decide⟩]) unmarked_context_7_363_1321173 node_context_7_363_1321173
  intro a
  fin_cases a
  · exact context_8_1452_1310882
  · exact context_8_1453_1314163
  · exact context_8_1454_1317501
  · exact context_8_1455_1321172

theorem unmarked_context_6_90_1321174 : frontier 15 ⟨1321174, by decide⟩
    (prefixCache 6 90) (prefixPartial 6 90) = false := by
  decide +kernel

theorem node_context_6_90_1321174 : EJMOriginalGlobalDAGData.nodes 15 ⟨1321174, by decide⟩ =
    .split (coordinate 6) (![⟨1281019, by decide⟩,⟨1294178, by decide⟩,⟨1306955, by decide⟩,⟨1321173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_90_1321174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 90 ⟨1321174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 90
    ⟨1321174, by decide⟩ (by decide) (![⟨1281019, by decide⟩,⟨1294178, by decide⟩,⟨1306955, by decide⟩,⟨1321173, by decide⟩]) unmarked_context_6_90_1321174 node_context_6_90_1321174
  intro a
  fin_cases a
  · exact context_7_360_1281019
  · exact context_7_361_1294178
  · exact context_7_362_1306955
  · exact context_7_363_1321173

theorem selected_cut_47218 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93184) = some ⟨11, 1, 0, 434745, 93184, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93184_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93184 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93184 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93184, 1, 262144⟩
    (by decide) selected_cut_47218

theorem selected_cut_47219 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 93185) = some ⟨11, 1, 0, 167448, 93185, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93185_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93185 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 93185 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 93185, 1, 262144⟩
    (by decide) selected_cut_47219

theorem selected_cut_47220 : selected 10 ⟨1321224, by decide⟩
    (prefixPartial 11 93186) = some ⟨11, 2, 0, 1321224, 93186, 2457, 262144⟩ := by
  decide +kernel

theorem context_11_93186_1321224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93186 ⟨1321224, by decide⟩ :=
  accepted_of_selected 11 93186 ⟨1321224, by decide⟩ ⟨11, 2, 0, 1321224, 93186, 2457, 262144⟩
    (by decide) selected_cut_47220

theorem selected_cut_47221 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 372748) = some ⟨12, 1, 0, 448748, 372748, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372748_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372748 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 372748 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 372748, 1, 65536⟩
    (by decide) selected_cut_47221

theorem selected_cut_47222 : selected 9 ⟨1321278, by decide⟩
    (prefixPartial 12 372749) = some ⟨12, 2, 0, 1321278, 372749, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_372749_1321278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372749 ⟨1321278, by decide⟩ :=
  accepted_of_selected 12 372749 ⟨1321278, by decide⟩ ⟨12, 2, 0, 1321278, 372749, 2549, 65536⟩
    (by decide) selected_cut_47222

theorem selected_cut_47223 : selected 9 ⟨1321323, by decide⟩
    (prefixPartial 12 372750) = some ⟨12, 2, 0, 1321323, 372750, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_372750_1321323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372750 ⟨1321323, by decide⟩ :=
  accepted_of_selected 12 372750 ⟨1321323, by decide⟩ ⟨12, 2, 0, 1321323, 372750, 2593, 65536⟩
    (by decide) selected_cut_47223

theorem selected_cut_47224 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 372751) = some ⟨12, 1, 0, 760511, 372751, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372751_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372751 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 372751 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 372751, 1, 65536⟩
    (by decide) selected_cut_47224

theorem unmarked_context_11_93187_1321324 : frontier 10 ⟨1321324, by decide⟩
    (prefixCache 11 93187) (prefixPartial 11 93187) = false := by
  decide +kernel

theorem node_context_11_93187_1321324 : EJMOriginalGlobalDAGData.nodes 10 ⟨1321324, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1321278, by decide⟩,⟨1321323, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93187_1321324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93187 ⟨1321324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93187
    ⟨1321324, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1321278, by decide⟩,⟨1321323, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_93187_1321324 node_context_11_93187_1321324
  intro a
  fin_cases a
  · exact context_12_372748_448748
  · exact context_12_372749_1321278
  · exact context_12_372750_1321323
  · exact context_12_372751_760511

theorem unmarked_context_10_23296_1321325 : frontier 11 ⟨1321325, by decide⟩
    (prefixCache 10 23296) (prefixPartial 10 23296) = false := by
  decide +kernel

theorem node_context_10_23296_1321325 : EJMOriginalGlobalDAGData.nodes 11 ⟨1321325, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1321224, by decide⟩,⟨1321324, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23296_1321325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23296 ⟨1321325, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23296
    ⟨1321325, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨167448, by decide⟩,⟨1321224, by decide⟩,⟨1321324, by decide⟩]) unmarked_context_10_23296_1321325 node_context_10_23296_1321325
  intro a
  fin_cases a
  · exact context_11_93184_434745
  · exact context_11_93185_167448
  · exact context_11_93186_1321224
  · exact context_11_93187_1321324

theorem selected_cut_47225 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 372752) = some ⟨12, 1, 0, 985390, 372752, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372752_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372752 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 372752 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 372752, 1, 65536⟩
    (by decide) selected_cut_47225

theorem selected_cut_47226 : selected 9 ⟨1321358, by decide⟩
    (prefixPartial 12 372753) = some ⟨12, 2, 0, 1321358, 372753, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_372753_1321358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372753 ⟨1321358, by decide⟩ :=
  accepted_of_selected 12 372753 ⟨1321358, by decide⟩ ⟨12, 2, 0, 1321358, 372753, 2021, 65536⟩
    (by decide) selected_cut_47226

theorem selected_cut_47227 : selected 9 ⟨1321389, by decide⟩
    (prefixPartial 12 372754) = some ⟨12, 2, 0, 1321389, 372754, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_372754_1321389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372754 ⟨1321389, by decide⟩ :=
  accepted_of_selected 12 372754 ⟨1321389, by decide⟩ ⟨12, 2, 0, 1321389, 372754, 1909, 65536⟩
    (by decide) selected_cut_47227

theorem selected_cut_47228 : selected 9 ⟨1321419, by decide⟩
    (prefixPartial 12 372755) = some ⟨12, 2, 0, 1321419, 372755, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_372755_1321419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372755 ⟨1321419, by decide⟩ :=
  accepted_of_selected 12 372755 ⟨1321419, by decide⟩ ⟨12, 2, 0, 1321419, 372755, 2033, 65536⟩
    (by decide) selected_cut_47228

theorem unmarked_context_11_93188_1321420 : frontier 10 ⟨1321420, by decide⟩
    (prefixCache 11 93188) (prefixPartial 11 93188) = false := by
  decide +kernel

theorem node_context_11_93188_1321420 : EJMOriginalGlobalDAGData.nodes 10 ⟨1321420, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1321358, by decide⟩,⟨1321389, by decide⟩,⟨1321419, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93188_1321420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93188 ⟨1321420, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93188
    ⟨1321420, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1321358, by decide⟩,⟨1321389, by decide⟩,⟨1321419, by decide⟩]) unmarked_context_11_93188_1321420 node_context_11_93188_1321420
  intro a
  fin_cases a
  · exact context_12_372752_985390
  · exact context_12_372753_1321358
  · exact context_12_372754_1321389
  · exact context_12_372755_1321419

theorem selected_cut_47229 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 93189) = some ⟨11, 1, 0, 815620, 93189, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93189_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93189 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 93189 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 93189, 1, 262144⟩
    (by decide) selected_cut_47229

theorem selected_cut_47230 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 372760) = some ⟨12, 1, 0, 994572, 372760, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372760_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372760 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 372760 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 372760, 1, 65536⟩
    (by decide) selected_cut_47230

theorem selected_cut_47231 : selected 9 ⟨1321457, by decide⟩
    (prefixPartial 12 372761) = some ⟨12, 2, 0, 1321457, 372761, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_372761_1321457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372761 ⟨1321457, by decide⟩ :=
  accepted_of_selected 12 372761 ⟨1321457, by decide⟩ ⟨12, 2, 0, 1321457, 372761, 2297, 65536⟩
    (by decide) selected_cut_47231

theorem selected_cut_47232 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 372762) = some ⟨12, 1, 0, 806997, 372762, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372762_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372762 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 372762 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 372762, 1, 65536⟩
    (by decide) selected_cut_47232

theorem selected_cut_47233 : selected 9 ⟨1321496, by decide⟩
    (prefixPartial 12 372763) = some ⟨12, 2, 0, 1321496, 372763, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_372763_1321496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372763 ⟨1321496, by decide⟩ :=
  accepted_of_selected 12 372763 ⟨1321496, by decide⟩ ⟨12, 2, 0, 1321496, 372763, 2493, 65536⟩
    (by decide) selected_cut_47233

theorem unmarked_context_11_93190_1321497 : frontier 10 ⟨1321497, by decide⟩
    (prefixCache 11 93190) (prefixPartial 11 93190) = false := by
  decide +kernel

theorem node_context_11_93190_1321497 : EJMOriginalGlobalDAGData.nodes 10 ⟨1321497, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1321457, by decide⟩,⟨806997, by decide⟩,⟨1321496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93190_1321497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93190 ⟨1321497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93190
    ⟨1321497, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1321457, by decide⟩,⟨806997, by decide⟩,⟨1321496, by decide⟩]) unmarked_context_11_93190_1321497 node_context_11_93190_1321497
  intro a
  fin_cases a
  · exact context_12_372760_994572
  · exact context_12_372761_1321457
  · exact context_12_372762_806997
  · exact context_12_372763_1321496

theorem selected_cut_47234 : selected 9 ⟨1321536, by decide⟩
    (prefixPartial 12 372764) = some ⟨12, 2, 0, 1321536, 372764, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_372764_1321536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372764 ⟨1321536, by decide⟩ :=
  accepted_of_selected 12 372764 ⟨1321536, by decide⟩ ⟨12, 2, 0, 1321536, 372764, 2405, 65536⟩
    (by decide) selected_cut_47234

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
