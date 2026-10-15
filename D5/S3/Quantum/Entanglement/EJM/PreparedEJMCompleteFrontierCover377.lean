/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover376
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36195 : selected 9 ⟨956833, by decide⟩
    (prefixPartial 12 288306) = some ⟨12, 2, 0, 956833, 288306, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_288306_956833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288306 ⟨956833, by decide⟩ :=
  accepted_of_selected 12 288306 ⟨956833, by decide⟩ ⟨12, 2, 0, 956833, 288306, 2725, 65536⟩
    (by decide) selected_cut_36195

theorem selected_cut_36196 : selected 9 ⟨956904, by decide⟩
    (prefixPartial 12 288307) = some ⟨12, 2, 0, 956904, 288307, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_288307_956904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288307 ⟨956904, by decide⟩ :=
  accepted_of_selected 12 288307 ⟨956904, by decide⟩ ⟨12, 2, 0, 956904, 288307, 3425, 65536⟩
    (by decide) selected_cut_36196

theorem unmarked_context_11_72076_956905 : frontier 10 ⟨956905, by decide⟩
    (prefixCache 11 72076) (prefixPartial 11 72076) = false := by
  decide +kernel

theorem node_context_11_72076_956905 : EJMOriginalGlobalDAGData.nodes 10 ⟨956905, by decide⟩ =
    .split (coordinate 11) (![⟨956751, by decide⟩,⟨956786, by decide⟩,⟨956833, by decide⟩,⟨956904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72076_956905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72076 ⟨956905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72076
    ⟨956905, by decide⟩ (by decide) (![⟨956751, by decide⟩,⟨956786, by decide⟩,⟨956833, by decide⟩,⟨956904, by decide⟩]) unmarked_context_11_72076_956905 node_context_11_72076_956905
  intro a
  fin_cases a
  · exact context_12_288304_956751
  · exact context_12_288305_956786
  · exact context_12_288306_956833
  · exact context_12_288307_956904

theorem selected_cut_36197 : selected 9 ⟨956940, by decide⟩
    (prefixPartial 12 288308) = some ⟨12, 2, 0, 956940, 288308, 2477, 65536⟩ := by
  decide +kernel

theorem context_12_288308_956940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288308 ⟨956940, by decide⟩ :=
  accepted_of_selected 12 288308 ⟨956940, by decide⟩ ⟨12, 2, 0, 956940, 288308, 2477, 65536⟩
    (by decide) selected_cut_36197

theorem selected_cut_36198 : selected 9 ⟨956973, by decide⟩
    (prefixPartial 12 288309) = some ⟨12, 2, 0, 956973, 288309, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_288309_956973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288309 ⟨956973, by decide⟩ :=
  accepted_of_selected 12 288309 ⟨956973, by decide⟩ ⟨12, 2, 0, 956973, 288309, 2229, 65536⟩
    (by decide) selected_cut_36198

theorem selected_cut_36199 : selected 9 ⟨957007, by decide⟩
    (prefixPartial 12 288310) = some ⟨12, 2, 0, 957007, 288310, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_288310_957007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288310 ⟨957007, by decide⟩ :=
  accepted_of_selected 12 288310 ⟨957007, by decide⟩ ⟨12, 2, 0, 957007, 288310, 2469, 65536⟩
    (by decide) selected_cut_36199

theorem selected_cut_36200 : selected 9 ⟨957059, by decide⟩
    (prefixPartial 12 288311) = some ⟨12, 2, 0, 957059, 288311, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_288311_957059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288311 ⟨957059, by decide⟩ :=
  accepted_of_selected 12 288311 ⟨957059, by decide⟩ ⟨12, 2, 0, 957059, 288311, 2825, 65536⟩
    (by decide) selected_cut_36200

theorem unmarked_context_11_72077_957060 : frontier 10 ⟨957060, by decide⟩
    (prefixCache 11 72077) (prefixPartial 11 72077) = false := by
  decide +kernel

theorem node_context_11_72077_957060 : EJMOriginalGlobalDAGData.nodes 10 ⟨957060, by decide⟩ =
    .split (coordinate 11) (![⟨956940, by decide⟩,⟨956973, by decide⟩,⟨957007, by decide⟩,⟨957059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72077_957060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72077 ⟨957060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72077
    ⟨957060, by decide⟩ (by decide) (![⟨956940, by decide⟩,⟨956973, by decide⟩,⟨957007, by decide⟩,⟨957059, by decide⟩]) unmarked_context_11_72077_957060 node_context_11_72077_957060
  intro a
  fin_cases a
  · exact context_12_288308_956940
  · exact context_12_288309_956973
  · exact context_12_288310_957007
  · exact context_12_288311_957059

theorem selected_cut_36201 : selected 9 ⟨957111, by decide⟩
    (prefixPartial 12 288312) = some ⟨12, 2, 0, 957111, 288312, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_288312_957111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288312 ⟨957111, by decide⟩ :=
  accepted_of_selected 12 288312 ⟨957111, by decide⟩ ⟨12, 2, 0, 957111, 288312, 2841, 65536⟩
    (by decide) selected_cut_36201

theorem selected_cut_36202 : selected 9 ⟨957140, by decide⟩
    (prefixPartial 12 288313) = some ⟨12, 2, 0, 957140, 288313, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_288313_957140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288313 ⟨957140, by decide⟩ :=
  accepted_of_selected 12 288313 ⟨957140, by decide⟩ ⟨12, 2, 0, 957140, 288313, 2229, 65536⟩
    (by decide) selected_cut_36202

theorem selected_cut_36203 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 288314) = some ⟨12, 1, 0, 893903, 288314, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288314_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288314 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 288314 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 288314, 1, 65536⟩
    (by decide) selected_cut_36203

theorem selected_cut_36204 : selected 9 ⟨957207, by decide⟩
    (prefixPartial 12 288315) = some ⟨12, 2, 0, 957207, 288315, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_288315_957207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288315 ⟨957207, by decide⟩ :=
  accepted_of_selected 12 288315 ⟨957207, by decide⟩ ⟨12, 2, 0, 957207, 288315, 3141, 65536⟩
    (by decide) selected_cut_36204

theorem unmarked_context_11_72078_957208 : frontier 10 ⟨957208, by decide⟩
    (prefixCache 11 72078) (prefixPartial 11 72078) = false := by
  decide +kernel

theorem node_context_11_72078_957208 : EJMOriginalGlobalDAGData.nodes 10 ⟨957208, by decide⟩ =
    .split (coordinate 11) (![⟨957111, by decide⟩,⟨957140, by decide⟩,⟨893903, by decide⟩,⟨957207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72078_957208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72078 ⟨957208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72078
    ⟨957208, by decide⟩ (by decide) (![⟨957111, by decide⟩,⟨957140, by decide⟩,⟨893903, by decide⟩,⟨957207, by decide⟩]) unmarked_context_11_72078_957208 node_context_11_72078_957208
  intro a
  fin_cases a
  · exact context_12_288312_957111
  · exact context_12_288313_957140
  · exact context_12_288314_893903
  · exact context_12_288315_957207

theorem selected_cut_36205 : selected 9 ⟨957248, by decide⟩
    (prefixPartial 12 288316) = some ⟨12, 2, 0, 957248, 288316, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_288316_957248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288316 ⟨957248, by decide⟩ :=
  accepted_of_selected 12 288316 ⟨957248, by decide⟩ ⟨12, 2, 0, 957248, 288316, 2505, 65536⟩
    (by decide) selected_cut_36205

theorem selected_cut_36206 : selected 9 ⟨957277, by decide⟩
    (prefixPartial 12 288317) = some ⟨12, 2, 0, 957277, 288317, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_288317_957277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288317 ⟨957277, by decide⟩ :=
  accepted_of_selected 12 288317 ⟨957277, by decide⟩ ⟨12, 2, 0, 957277, 288317, 2137, 65536⟩
    (by decide) selected_cut_36206

theorem selected_cut_36207 : selected 9 ⟨957316, by decide⟩
    (prefixPartial 12 288318) = some ⟨12, 2, 0, 957316, 288318, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_288318_957316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288318 ⟨957316, by decide⟩ :=
  accepted_of_selected 12 288318 ⟨957316, by decide⟩ ⟨12, 2, 0, 957316, 288318, 2569, 65536⟩
    (by decide) selected_cut_36207

theorem selected_cut_36208 : selected 9 ⟨957359, by decide⟩
    (prefixPartial 12 288319) = some ⟨12, 2, 0, 957359, 288319, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_288319_957359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288319 ⟨957359, by decide⟩ :=
  accepted_of_selected 12 288319 ⟨957359, by decide⟩ ⟨12, 2, 0, 957359, 288319, 2825, 65536⟩
    (by decide) selected_cut_36208

theorem unmarked_context_11_72079_957360 : frontier 10 ⟨957360, by decide⟩
    (prefixCache 11 72079) (prefixPartial 11 72079) = false := by
  decide +kernel

theorem node_context_11_72079_957360 : EJMOriginalGlobalDAGData.nodes 10 ⟨957360, by decide⟩ =
    .split (coordinate 11) (![⟨957248, by decide⟩,⟨957277, by decide⟩,⟨957316, by decide⟩,⟨957359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72079_957360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72079 ⟨957360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72079
    ⟨957360, by decide⟩ (by decide) (![⟨957248, by decide⟩,⟨957277, by decide⟩,⟨957316, by decide⟩,⟨957359, by decide⟩]) unmarked_context_11_72079_957360 node_context_11_72079_957360
  intro a
  fin_cases a
  · exact context_12_288316_957248
  · exact context_12_288317_957277
  · exact context_12_288318_957316
  · exact context_12_288319_957359

theorem unmarked_context_10_18019_957361 : frontier 11 ⟨957361, by decide⟩
    (prefixCache 10 18019) (prefixPartial 10 18019) = false := by
  decide +kernel

theorem node_context_10_18019_957361 : EJMOriginalGlobalDAGData.nodes 11 ⟨957361, by decide⟩ =
    .split (coordinate 10) (![⟨956905, by decide⟩,⟨957060, by decide⟩,⟨957208, by decide⟩,⟨957360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18019_957361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18019 ⟨957361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18019
    ⟨957361, by decide⟩ (by decide) (![⟨956905, by decide⟩,⟨957060, by decide⟩,⟨957208, by decide⟩,⟨957360, by decide⟩]) unmarked_context_10_18019_957361 node_context_10_18019_957361
  intro a
  fin_cases a
  · exact context_11_72076_956905
  · exact context_11_72077_957060
  · exact context_11_72078_957208
  · exact context_11_72079_957360

theorem unmarked_context_9_4504_957362 : frontier 12 ⟨957362, by decide⟩
    (prefixCache 9 4504) (prefixPartial 9 4504) = false := by
  decide +kernel

theorem node_context_9_4504_957362 : EJMOriginalGlobalDAGData.nodes 12 ⟨957362, by decide⟩ =
    .split (coordinate 9) (![⟨955399, by decide⟩,⟨955931, by decide⟩,⟨956713, by decide⟩,⟨957361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4504_957362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4504 ⟨957362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4504
    ⟨957362, by decide⟩ (by decide) (![⟨955399, by decide⟩,⟨955931, by decide⟩,⟨956713, by decide⟩,⟨957361, by decide⟩]) unmarked_context_9_4504_957362 node_context_9_4504_957362
  intro a
  fin_cases a
  · exact context_10_18016_955399
  · exact context_10_18017_955931
  · exact context_10_18018_956713
  · exact context_10_18019_957361

theorem selected_cut_36209 : selected 9 ⟨957422, by decide⟩
    (prefixPartial 12 288320) = some ⟨12, 2, 0, 957422, 288320, 3113, 65536⟩ := by
  decide +kernel

theorem context_12_288320_957422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288320 ⟨957422, by decide⟩ :=
  accepted_of_selected 12 288320 ⟨957422, by decide⟩ ⟨12, 2, 0, 957422, 288320, 3113, 65536⟩
    (by decide) selected_cut_36209

theorem selected_cut_36210 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288321) = some ⟨12, 1, 0, 896706, 288321, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288321_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288321 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288321 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288321, 1, 65536⟩
    (by decide) selected_cut_36210

theorem selected_cut_36211 : selected 9 ⟨957477, by decide⟩
    (prefixPartial 12 288322) = some ⟨12, 2, 0, 957477, 288322, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_288322_957477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288322 ⟨957477, by decide⟩ :=
  accepted_of_selected 12 288322 ⟨957477, by decide⟩ ⟨12, 2, 0, 957477, 288322, 2609, 65536⟩
    (by decide) selected_cut_36211

theorem selected_cut_36212 : selected 9 ⟨957533, by decide⟩
    (prefixPartial 12 288323) = some ⟨12, 2, 0, 957533, 288323, 3161, 65536⟩ := by
  decide +kernel

theorem context_12_288323_957533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288323 ⟨957533, by decide⟩ :=
  accepted_of_selected 12 288323 ⟨957533, by decide⟩ ⟨12, 2, 0, 957533, 288323, 3161, 65536⟩
    (by decide) selected_cut_36212

theorem unmarked_context_11_72080_957534 : frontier 10 ⟨957534, by decide⟩
    (prefixCache 11 72080) (prefixPartial 11 72080) = false := by
  decide +kernel

theorem node_context_11_72080_957534 : EJMOriginalGlobalDAGData.nodes 10 ⟨957534, by decide⟩ =
    .split (coordinate 11) (![⟨957422, by decide⟩,⟨896706, by decide⟩,⟨957477, by decide⟩,⟨957533, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72080_957534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72080 ⟨957534, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72080
    ⟨957534, by decide⟩ (by decide) (![⟨957422, by decide⟩,⟨896706, by decide⟩,⟨957477, by decide⟩,⟨957533, by decide⟩]) unmarked_context_11_72080_957534 node_context_11_72080_957534
  intro a
  fin_cases a
  · exact context_12_288320_957422
  · exact context_12_288321_896706
  · exact context_12_288322_957477
  · exact context_12_288323_957533

theorem selected_cut_36213 : selected 9 ⟨957573, by decide⟩
    (prefixPartial 12 288324) = some ⟨12, 2, 0, 957573, 288324, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_288324_957573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288324 ⟨957573, by decide⟩ :=
  accepted_of_selected 12 288324 ⟨957573, by decide⟩ ⟨12, 2, 0, 957573, 288324, 2509, 65536⟩
    (by decide) selected_cut_36213

theorem selected_cut_36214 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288325) = some ⟨12, 1, 0, 896706, 288325, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288325_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288325 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288325 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288325, 1, 65536⟩
    (by decide) selected_cut_36214

theorem selected_cut_36215 : selected 9 ⟨957609, by decide⟩
    (prefixPartial 12 288326) = some ⟨12, 2, 0, 957609, 288326, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_288326_957609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288326 ⟨957609, by decide⟩ :=
  accepted_of_selected 12 288326 ⟨957609, by decide⟩ ⟨12, 2, 0, 957609, 288326, 2097, 65536⟩
    (by decide) selected_cut_36215

theorem selected_cut_36216 : selected 9 ⟨957649, by decide⟩
    (prefixPartial 12 288327) = some ⟨12, 2, 0, 957649, 288327, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_288327_957649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288327 ⟨957649, by decide⟩ :=
  accepted_of_selected 12 288327 ⟨957649, by decide⟩ ⟨12, 2, 0, 957649, 288327, 2353, 65536⟩
    (by decide) selected_cut_36216

theorem unmarked_context_11_72081_957650 : frontier 10 ⟨957650, by decide⟩
    (prefixCache 11 72081) (prefixPartial 11 72081) = false := by
  decide +kernel

theorem node_context_11_72081_957650 : EJMOriginalGlobalDAGData.nodes 10 ⟨957650, by decide⟩ =
    .split (coordinate 11) (![⟨957573, by decide⟩,⟨896706, by decide⟩,⟨957609, by decide⟩,⟨957649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72081_957650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72081 ⟨957650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72081
    ⟨957650, by decide⟩ (by decide) (![⟨957573, by decide⟩,⟨896706, by decide⟩,⟨957609, by decide⟩,⟨957649, by decide⟩]) unmarked_context_11_72081_957650 node_context_11_72081_957650
  intro a
  fin_cases a
  · exact context_12_288324_957573
  · exact context_12_288325_896706
  · exact context_12_288326_957609
  · exact context_12_288327_957649

theorem selected_cut_36217 : selected 9 ⟨957710, by decide⟩
    (prefixPartial 12 288328) = some ⟨12, 2, 0, 957710, 288328, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_288328_957710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288328 ⟨957710, by decide⟩ :=
  accepted_of_selected 12 288328 ⟨957710, by decide⟩ ⟨12, 2, 0, 957710, 288328, 3029, 65536⟩
    (by decide) selected_cut_36217

theorem selected_cut_36218 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288329) = some ⟨12, 1, 0, 896706, 288329, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288329_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288329 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288329 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288329, 1, 65536⟩
    (by decide) selected_cut_36218

theorem selected_cut_36219 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 288330) = some ⟨12, 1, 0, 893903, 288330, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288330_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288330 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 288330 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 288330, 1, 65536⟩
    (by decide) selected_cut_36219

theorem selected_cut_36220 : selected 9 ⟨957764, by decide⟩
    (prefixPartial 12 288331) = some ⟨12, 2, 0, 957764, 288331, 2837, 65536⟩ := by
  decide +kernel

theorem context_12_288331_957764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288331 ⟨957764, by decide⟩ :=
  accepted_of_selected 12 288331 ⟨957764, by decide⟩ ⟨12, 2, 0, 957764, 288331, 2837, 65536⟩
    (by decide) selected_cut_36220

theorem unmarked_context_11_72082_957765 : frontier 10 ⟨957765, by decide⟩
    (prefixCache 11 72082) (prefixPartial 11 72082) = false := by
  decide +kernel

theorem node_context_11_72082_957765 : EJMOriginalGlobalDAGData.nodes 10 ⟨957765, by decide⟩ =
    .split (coordinate 11) (![⟨957710, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨957764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72082_957765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72082 ⟨957765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72082
    ⟨957765, by decide⟩ (by decide) (![⟨957710, by decide⟩,⟨896706, by decide⟩,⟨893903, by decide⟩,⟨957764, by decide⟩]) unmarked_context_11_72082_957765 node_context_11_72082_957765
  intro a
  fin_cases a
  · exact context_12_288328_957710
  · exact context_12_288329_896706
  · exact context_12_288330_893903
  · exact context_12_288331_957764

theorem selected_cut_36221 : selected 9 ⟨957833, by decide⟩
    (prefixPartial 12 288332) = some ⟨12, 2, 0, 957833, 288332, 2985, 65536⟩ := by
  decide +kernel

theorem context_12_288332_957833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288332 ⟨957833, by decide⟩ :=
  accepted_of_selected 12 288332 ⟨957833, by decide⟩ ⟨12, 2, 0, 957833, 288332, 2985, 65536⟩
    (by decide) selected_cut_36221

theorem selected_cut_36222 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288333) = some ⟨12, 1, 0, 896706, 288333, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288333_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288333 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288333 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288333, 1, 65536⟩
    (by decide) selected_cut_36222

theorem selected_cut_36223 : selected 9 ⟨957891, by decide⟩
    (prefixPartial 12 288334) = some ⟨12, 2, 0, 957891, 288334, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_288334_957891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288334 ⟨957891, by decide⟩ :=
  accepted_of_selected 12 288334 ⟨957891, by decide⟩ ⟨12, 2, 0, 957891, 288334, 2569, 65536⟩
    (by decide) selected_cut_36223

theorem selected_cut_36224 : selected 9 ⟨957939, by decide⟩
    (prefixPartial 12 288335) = some ⟨12, 2, 0, 957939, 288335, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_288335_957939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288335 ⟨957939, by decide⟩ :=
  accepted_of_selected 12 288335 ⟨957939, by decide⟩ ⟨12, 2, 0, 957939, 288335, 2733, 65536⟩
    (by decide) selected_cut_36224

theorem unmarked_context_11_72083_957940 : frontier 10 ⟨957940, by decide⟩
    (prefixCache 11 72083) (prefixPartial 11 72083) = false := by
  decide +kernel

theorem node_context_11_72083_957940 : EJMOriginalGlobalDAGData.nodes 10 ⟨957940, by decide⟩ =
    .split (coordinate 11) (![⟨957833, by decide⟩,⟨896706, by decide⟩,⟨957891, by decide⟩,⟨957939, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72083_957940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72083 ⟨957940, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72083
    ⟨957940, by decide⟩ (by decide) (![⟨957833, by decide⟩,⟨896706, by decide⟩,⟨957891, by decide⟩,⟨957939, by decide⟩]) unmarked_context_11_72083_957940 node_context_11_72083_957940
  intro a
  fin_cases a
  · exact context_12_288332_957833
  · exact context_12_288333_896706
  · exact context_12_288334_957891
  · exact context_12_288335_957939

theorem unmarked_context_10_18020_957941 : frontier 11 ⟨957941, by decide⟩
    (prefixCache 10 18020) (prefixPartial 10 18020) = false := by
  decide +kernel

theorem node_context_10_18020_957941 : EJMOriginalGlobalDAGData.nodes 11 ⟨957941, by decide⟩ =
    .split (coordinate 10) (![⟨957534, by decide⟩,⟨957650, by decide⟩,⟨957765, by decide⟩,⟨957940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18020_957941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18020 ⟨957941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18020
    ⟨957941, by decide⟩ (by decide) (![⟨957534, by decide⟩,⟨957650, by decide⟩,⟨957765, by decide⟩,⟨957940, by decide⟩]) unmarked_context_10_18020_957941 node_context_10_18020_957941
  intro a
  fin_cases a
  · exact context_11_72080_957534
  · exact context_11_72081_957650
  · exact context_11_72082_957765
  · exact context_11_72083_957940

theorem selected_cut_36225 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18021) = some ⟨10, 1, 0, 893098, 18021, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18021_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18021 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18021 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18021, 1, 1048576⟩
    (by decide) selected_cut_36225

theorem selected_cut_36226 : selected 9 ⟨957983, by decide⟩
    (prefixPartial 12 288352) = some ⟨12, 2, 0, 957983, 288352, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_288352_957983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288352 ⟨957983, by decide⟩ :=
  accepted_of_selected 12 288352 ⟨957983, by decide⟩ ⟨12, 2, 0, 957983, 288352, 2213, 65536⟩
    (by decide) selected_cut_36226

theorem selected_cut_36227 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288353) = some ⟨12, 1, 0, 896706, 288353, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288353_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288353 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288353 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288353, 1, 65536⟩
    (by decide) selected_cut_36227

theorem selected_cut_36228 : selected 9 ⟨958024, by decide⟩
    (prefixPartial 12 288354) = some ⟨12, 2, 0, 958024, 288354, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_288354_958024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288354 ⟨958024, by decide⟩ :=
  accepted_of_selected 12 288354 ⟨958024, by decide⟩ ⟨12, 2, 0, 958024, 288354, 2189, 65536⟩
    (by decide) selected_cut_36228

theorem selected_cut_36229 : selected 9 ⟨958082, by decide⟩
    (prefixPartial 12 288355) = some ⟨12, 2, 0, 958082, 288355, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_288355_958082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288355 ⟨958082, by decide⟩ :=
  accepted_of_selected 12 288355 ⟨958082, by decide⟩ ⟨12, 2, 0, 958082, 288355, 2709, 65536⟩
    (by decide) selected_cut_36229

theorem unmarked_context_11_72088_958083 : frontier 10 ⟨958083, by decide⟩
    (prefixCache 11 72088) (prefixPartial 11 72088) = false := by
  decide +kernel

theorem node_context_11_72088_958083 : EJMOriginalGlobalDAGData.nodes 10 ⟨958083, by decide⟩ =
    .split (coordinate 11) (![⟨957983, by decide⟩,⟨896706, by decide⟩,⟨958024, by decide⟩,⟨958082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72088_958083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72088 ⟨958083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72088
    ⟨958083, by decide⟩ (by decide) (![⟨957983, by decide⟩,⟨896706, by decide⟩,⟨958024, by decide⟩,⟨958082, by decide⟩]) unmarked_context_11_72088_958083 node_context_11_72088_958083
  intro a
  fin_cases a
  · exact context_12_288352_957983
  · exact context_12_288353_896706
  · exact context_12_288354_958024
  · exact context_12_288355_958082

theorem selected_cut_36230 : selected 9 ⟨958105, by decide⟩
    (prefixPartial 12 288356) = some ⟨12, 2, 0, 958105, 288356, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_288356_958105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288356 ⟨958105, by decide⟩ :=
  accepted_of_selected 12 288356 ⟨958105, by decide⟩ ⟨12, 2, 0, 958105, 288356, 1721, 65536⟩
    (by decide) selected_cut_36230

theorem selected_cut_36231 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288357) = some ⟨12, 1, 0, 896706, 288357, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288357_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288357 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288357 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288357, 1, 65536⟩
    (by decide) selected_cut_36231

theorem selected_cut_36232 : selected 9 ⟨958132, by decide⟩
    (prefixPartial 12 288358) = some ⟨12, 2, 0, 958132, 288358, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_288358_958132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288358 ⟨958132, by decide⟩ :=
  accepted_of_selected 12 288358 ⟨958132, by decide⟩ ⟨12, 2, 0, 958132, 288358, 1705, 65536⟩
    (by decide) selected_cut_36232

theorem selected_cut_36233 : selected 9 ⟨958172, by decide⟩
    (prefixPartial 12 288359) = some ⟨12, 2, 0, 958172, 288359, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_288359_958172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288359 ⟨958172, by decide⟩ :=
  accepted_of_selected 12 288359 ⟨958172, by decide⟩ ⟨12, 2, 0, 958172, 288359, 1873, 65536⟩
    (by decide) selected_cut_36233

theorem unmarked_context_11_72089_958173 : frontier 10 ⟨958173, by decide⟩
    (prefixCache 11 72089) (prefixPartial 11 72089) = false := by
  decide +kernel

theorem node_context_11_72089_958173 : EJMOriginalGlobalDAGData.nodes 10 ⟨958173, by decide⟩ =
    .split (coordinate 11) (![⟨958105, by decide⟩,⟨896706, by decide⟩,⟨958132, by decide⟩,⟨958172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72089_958173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72089 ⟨958173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72089
    ⟨958173, by decide⟩ (by decide) (![⟨958105, by decide⟩,⟨896706, by decide⟩,⟨958132, by decide⟩,⟨958172, by decide⟩]) unmarked_context_11_72089_958173 node_context_11_72089_958173
  intro a
  fin_cases a
  · exact context_12_288356_958105
  · exact context_12_288357_896706
  · exact context_12_288358_958132
  · exact context_12_288359_958172

theorem selected_cut_36234 : selected 9 ⟨958209, by decide⟩
    (prefixPartial 12 288360) = some ⟨12, 2, 0, 958209, 288360, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_288360_958209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288360 ⟨958209, by decide⟩ :=
  accepted_of_selected 12 288360 ⟨958209, by decide⟩ ⟨12, 2, 0, 958209, 288360, 2085, 65536⟩
    (by decide) selected_cut_36234

theorem selected_cut_36235 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288361) = some ⟨12, 1, 0, 896706, 288361, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288361_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288361 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288361 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288361, 1, 65536⟩
    (by decide) selected_cut_36235

theorem selected_cut_36236 : selected 9 ⟨661671, by decide⟩
    (prefixPartial 12 288362) = some ⟨12, 1, 0, 661671, 288362, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288362_661671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288362 ⟨661671, by decide⟩ :=
  accepted_of_selected 12 288362 ⟨661671, by decide⟩ ⟨12, 1, 0, 661671, 288362, 1, 65536⟩
    (by decide) selected_cut_36236

theorem selected_cut_36237 : selected 9 ⟨958244, by decide⟩
    (prefixPartial 12 288363) = some ⟨12, 2, 0, 958244, 288363, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_288363_958244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288363 ⟨958244, by decide⟩ :=
  accepted_of_selected 12 288363 ⟨958244, by decide⟩ ⟨12, 2, 0, 958244, 288363, 2233, 65536⟩
    (by decide) selected_cut_36237

theorem unmarked_context_11_72090_958245 : frontier 10 ⟨958245, by decide⟩
    (prefixCache 11 72090) (prefixPartial 11 72090) = false := by
  decide +kernel

theorem node_context_11_72090_958245 : EJMOriginalGlobalDAGData.nodes 10 ⟨958245, by decide⟩ =
    .split (coordinate 11) (![⟨958209, by decide⟩,⟨896706, by decide⟩,⟨661671, by decide⟩,⟨958244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72090_958245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72090 ⟨958245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72090
    ⟨958245, by decide⟩ (by decide) (![⟨958209, by decide⟩,⟨896706, by decide⟩,⟨661671, by decide⟩,⟨958244, by decide⟩]) unmarked_context_11_72090_958245 node_context_11_72090_958245
  intro a
  fin_cases a
  · exact context_12_288360_958209
  · exact context_12_288361_896706
  · exact context_12_288362_661671
  · exact context_12_288363_958244

theorem selected_cut_36238 : selected 9 ⟨958293, by decide⟩
    (prefixPartial 12 288364) = some ⟨12, 2, 0, 958293, 288364, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_288364_958293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288364 ⟨958293, by decide⟩ :=
  accepted_of_selected 12 288364 ⟨958293, by decide⟩ ⟨12, 2, 0, 958293, 288364, 2197, 65536⟩
    (by decide) selected_cut_36238

theorem selected_cut_36239 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288365) = some ⟨12, 1, 0, 896706, 288365, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288365_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288365 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288365 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288365, 1, 65536⟩
    (by decide) selected_cut_36239

theorem selected_cut_36240 : selected 9 ⟨958329, by decide⟩
    (prefixPartial 12 288366) = some ⟨12, 2, 0, 958329, 288366, 2085, 65536⟩ := by
  decide +kernel

theorem context_12_288366_958329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288366 ⟨958329, by decide⟩ :=
  accepted_of_selected 12 288366 ⟨958329, by decide⟩ ⟨12, 2, 0, 958329, 288366, 2085, 65536⟩
    (by decide) selected_cut_36240

theorem selected_cut_36241 : selected 9 ⟨958372, by decide⟩
    (prefixPartial 12 288367) = some ⟨12, 2, 0, 958372, 288367, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_288367_958372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288367 ⟨958372, by decide⟩ :=
  accepted_of_selected 12 288367 ⟨958372, by decide⟩ ⟨12, 2, 0, 958372, 288367, 2281, 65536⟩
    (by decide) selected_cut_36241

theorem unmarked_context_11_72091_958373 : frontier 10 ⟨958373, by decide⟩
    (prefixCache 11 72091) (prefixPartial 11 72091) = false := by
  decide +kernel

theorem node_context_11_72091_958373 : EJMOriginalGlobalDAGData.nodes 10 ⟨958373, by decide⟩ =
    .split (coordinate 11) (![⟨958293, by decide⟩,⟨896706, by decide⟩,⟨958329, by decide⟩,⟨958372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72091_958373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72091 ⟨958373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72091
    ⟨958373, by decide⟩ (by decide) (![⟨958293, by decide⟩,⟨896706, by decide⟩,⟨958329, by decide⟩,⟨958372, by decide⟩]) unmarked_context_11_72091_958373 node_context_11_72091_958373
  intro a
  fin_cases a
  · exact context_12_288364_958293
  · exact context_12_288365_896706
  · exact context_12_288366_958329
  · exact context_12_288367_958372

theorem unmarked_context_10_18022_958374 : frontier 11 ⟨958374, by decide⟩
    (prefixCache 10 18022) (prefixPartial 10 18022) = false := by
  decide +kernel

theorem node_context_10_18022_958374 : EJMOriginalGlobalDAGData.nodes 11 ⟨958374, by decide⟩ =
    .split (coordinate 10) (![⟨958083, by decide⟩,⟨958173, by decide⟩,⟨958245, by decide⟩,⟨958373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18022_958374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18022 ⟨958374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18022
    ⟨958374, by decide⟩ (by decide) (![⟨958083, by decide⟩,⟨958173, by decide⟩,⟨958245, by decide⟩,⟨958373, by decide⟩]) unmarked_context_10_18022_958374 node_context_10_18022_958374
  intro a
  fin_cases a
  · exact context_11_72088_958083
  · exact context_11_72089_958173
  · exact context_11_72090_958245
  · exact context_11_72091_958373

theorem selected_cut_36242 : selected 9 ⟨958410, by decide⟩
    (prefixPartial 12 288368) = some ⟨12, 2, 0, 958410, 288368, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_288368_958410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288368 ⟨958410, by decide⟩ :=
  accepted_of_selected 12 288368 ⟨958410, by decide⟩ ⟨12, 2, 0, 958410, 288368, 1945, 65536⟩
    (by decide) selected_cut_36242

theorem selected_cut_36243 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288369) = some ⟨12, 1, 0, 896706, 288369, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288369_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288369 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288369 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288369, 1, 65536⟩
    (by decide) selected_cut_36243

theorem selected_cut_36244 : selected 9 ⟨958447, by decide⟩
    (prefixPartial 12 288370) = some ⟨12, 2, 0, 958447, 288370, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_288370_958447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288370 ⟨958447, by decide⟩ :=
  accepted_of_selected 12 288370 ⟨958447, by decide⟩ ⟨12, 2, 0, 958447, 288370, 1901, 65536⟩
    (by decide) selected_cut_36244

theorem selected_cut_36245 : selected 9 ⟨958488, by decide⟩
    (prefixPartial 12 288371) = some ⟨12, 2, 0, 958488, 288371, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_288371_958488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288371 ⟨958488, by decide⟩ :=
  accepted_of_selected 12 288371 ⟨958488, by decide⟩ ⟨12, 2, 0, 958488, 288371, 2249, 65536⟩
    (by decide) selected_cut_36245

theorem unmarked_context_11_72092_958489 : frontier 10 ⟨958489, by decide⟩
    (prefixCache 11 72092) (prefixPartial 11 72092) = false := by
  decide +kernel

theorem node_context_11_72092_958489 : EJMOriginalGlobalDAGData.nodes 10 ⟨958489, by decide⟩ =
    .split (coordinate 11) (![⟨958410, by decide⟩,⟨896706, by decide⟩,⟨958447, by decide⟩,⟨958488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72092_958489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72092 ⟨958489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72092
    ⟨958489, by decide⟩ (by decide) (![⟨958410, by decide⟩,⟨896706, by decide⟩,⟨958447, by decide⟩,⟨958488, by decide⟩]) unmarked_context_11_72092_958489 node_context_11_72092_958489
  intro a
  fin_cases a
  · exact context_12_288368_958410
  · exact context_12_288369_896706
  · exact context_12_288370_958447
  · exact context_12_288371_958488

theorem selected_cut_36246 : selected 9 ⟨958512, by decide⟩
    (prefixPartial 12 288372) = some ⟨12, 2, 0, 958512, 288372, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_288372_958512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288372 ⟨958512, by decide⟩ :=
  accepted_of_selected 12 288372 ⟨958512, by decide⟩ ⟨12, 2, 0, 958512, 288372, 1429, 65536⟩
    (by decide) selected_cut_36246

theorem selected_cut_36247 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288373) = some ⟨12, 1, 0, 896706, 288373, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288373_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288373 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288373 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288373, 1, 65536⟩
    (by decide) selected_cut_36247

theorem selected_cut_36248 : selected 9 ⟨958531, by decide⟩
    (prefixPartial 12 288374) = some ⟨12, 2, 0, 958531, 288374, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_288374_958531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288374 ⟨958531, by decide⟩ :=
  accepted_of_selected 12 288374 ⟨958531, by decide⟩ ⟨12, 2, 0, 958531, 288374, 1421, 65536⟩
    (by decide) selected_cut_36248

theorem selected_cut_36249 : selected 9 ⟨958558, by decide⟩
    (prefixPartial 12 288375) = some ⟨12, 2, 0, 958558, 288375, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_288375_958558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288375 ⟨958558, by decide⟩ :=
  accepted_of_selected 12 288375 ⟨958558, by decide⟩ ⟨12, 2, 0, 958558, 288375, 1585, 65536⟩
    (by decide) selected_cut_36249

theorem unmarked_context_11_72093_958559 : frontier 10 ⟨958559, by decide⟩
    (prefixCache 11 72093) (prefixPartial 11 72093) = false := by
  decide +kernel

theorem node_context_11_72093_958559 : EJMOriginalGlobalDAGData.nodes 10 ⟨958559, by decide⟩ =
    .split (coordinate 11) (![⟨958512, by decide⟩,⟨896706, by decide⟩,⟨958531, by decide⟩,⟨958558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72093_958559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72093 ⟨958559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72093
    ⟨958559, by decide⟩ (by decide) (![⟨958512, by decide⟩,⟨896706, by decide⟩,⟨958531, by decide⟩,⟨958558, by decide⟩]) unmarked_context_11_72093_958559 node_context_11_72093_958559
  intro a
  fin_cases a
  · exact context_12_288372_958512
  · exact context_12_288373_896706
  · exact context_12_288374_958531
  · exact context_12_288375_958558

theorem selected_cut_36250 : selected 10 ⟨958620, by decide⟩
    (prefixPartial 11 72094) = some ⟨11, 2, 0, 958620, 72094, 3521, 262144⟩ := by
  decide +kernel

theorem context_11_72094_958620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72094 ⟨958620, by decide⟩ :=
  accepted_of_selected 11 72094 ⟨958620, by decide⟩ ⟨11, 2, 0, 958620, 72094, 3521, 262144⟩
    (by decide) selected_cut_36250

theorem selected_cut_36251 : selected 9 ⟨958651, by decide⟩
    (prefixPartial 12 288380) = some ⟨12, 2, 0, 958651, 288380, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_288380_958651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288380 ⟨958651, by decide⟩ :=
  accepted_of_selected 12 288380 ⟨958651, by decide⟩ ⟨12, 2, 0, 958651, 288380, 1717, 65536⟩
    (by decide) selected_cut_36251

theorem selected_cut_36252 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 288381) = some ⟨12, 1, 0, 896706, 288381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288381_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288381 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 288381 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 288381, 1, 65536⟩
    (by decide) selected_cut_36252

theorem selected_cut_36253 : selected 9 ⟨958681, by decide⟩
    (prefixPartial 12 288382) = some ⟨12, 2, 0, 958681, 288382, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_288382_958681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288382 ⟨958681, by decide⟩ :=
  accepted_of_selected 12 288382 ⟨958681, by decide⟩ ⟨12, 2, 0, 958681, 288382, 1705, 65536⟩
    (by decide) selected_cut_36253

theorem selected_cut_36254 : selected 9 ⟨958710, by decide⟩
    (prefixPartial 12 288383) = some ⟨12, 2, 0, 958710, 288383, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_288383_958710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288383 ⟨958710, by decide⟩ :=
  accepted_of_selected 12 288383 ⟨958710, by decide⟩ ⟨12, 2, 0, 958710, 288383, 1813, 65536⟩
    (by decide) selected_cut_36254

theorem unmarked_context_11_72095_958711 : frontier 10 ⟨958711, by decide⟩
    (prefixCache 11 72095) (prefixPartial 11 72095) = false := by
  decide +kernel

theorem node_context_11_72095_958711 : EJMOriginalGlobalDAGData.nodes 10 ⟨958711, by decide⟩ =
    .split (coordinate 11) (![⟨958651, by decide⟩,⟨896706, by decide⟩,⟨958681, by decide⟩,⟨958710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72095_958711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72095 ⟨958711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72095
    ⟨958711, by decide⟩ (by decide) (![⟨958651, by decide⟩,⟨896706, by decide⟩,⟨958681, by decide⟩,⟨958710, by decide⟩]) unmarked_context_11_72095_958711 node_context_11_72095_958711
  intro a
  fin_cases a
  · exact context_12_288380_958651
  · exact context_12_288381_896706
  · exact context_12_288382_958681
  · exact context_12_288383_958710

theorem unmarked_context_10_18023_958712 : frontier 11 ⟨958712, by decide⟩
    (prefixCache 10 18023) (prefixPartial 10 18023) = false := by
  decide +kernel

theorem node_context_10_18023_958712 : EJMOriginalGlobalDAGData.nodes 11 ⟨958712, by decide⟩ =
    .split (coordinate 10) (![⟨958489, by decide⟩,⟨958559, by decide⟩,⟨958620, by decide⟩,⟨958711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18023_958712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18023 ⟨958712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18023
    ⟨958712, by decide⟩ (by decide) (![⟨958489, by decide⟩,⟨958559, by decide⟩,⟨958620, by decide⟩,⟨958711, by decide⟩]) unmarked_context_10_18023_958712 node_context_10_18023_958712
  intro a
  fin_cases a
  · exact context_11_72092_958489
  · exact context_11_72093_958559
  · exact context_11_72094_958620
  · exact context_11_72095_958711

theorem unmarked_context_9_4505_958713 : frontier 12 ⟨958713, by decide⟩
    (prefixCache 9 4505) (prefixPartial 9 4505) = false := by
  decide +kernel

theorem node_context_9_4505_958713 : EJMOriginalGlobalDAGData.nodes 12 ⟨958713, by decide⟩ =
    .split (coordinate 9) (![⟨957941, by decide⟩,⟨893098, by decide⟩,⟨958374, by decide⟩,⟨958712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4505_958713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4505 ⟨958713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4505
    ⟨958713, by decide⟩ (by decide) (![⟨957941, by decide⟩,⟨893098, by decide⟩,⟨958374, by decide⟩,⟨958712, by decide⟩]) unmarked_context_9_4505_958713 node_context_9_4505_958713
  intro a
  fin_cases a
  · exact context_10_18020_957941
  · exact context_10_18021_893098
  · exact context_10_18022_958374
  · exact context_10_18023_958712

theorem selected_cut_36255 : selected 9 ⟨958745, by decide⟩
    (prefixPartial 12 288384) = some ⟨12, 2, 0, 958745, 288384, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_288384_958745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288384 ⟨958745, by decide⟩ :=
  accepted_of_selected 12 288384 ⟨958745, by decide⟩ ⟨12, 2, 0, 958745, 288384, 1973, 65536⟩
    (by decide) selected_cut_36255

theorem selected_cut_36256 : selected 9 ⟨958770, by decide⟩
    (prefixPartial 12 288385) = some ⟨12, 2, 0, 958770, 288385, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_288385_958770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288385 ⟨958770, by decide⟩ :=
  accepted_of_selected 12 288385 ⟨958770, by decide⟩ ⟨12, 2, 0, 958770, 288385, 1525, 65536⟩
    (by decide) selected_cut_36256

theorem selected_cut_36257 : selected 9 ⟨958792, by decide⟩
    (prefixPartial 12 288386) = some ⟨12, 2, 0, 958792, 288386, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_288386_958792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288386 ⟨958792, by decide⟩ :=
  accepted_of_selected 12 288386 ⟨958792, by decide⟩ ⟨12, 2, 0, 958792, 288386, 1385, 65536⟩
    (by decide) selected_cut_36257

theorem selected_cut_36258 : selected 9 ⟨958822, by decide⟩
    (prefixPartial 12 288387) = some ⟨12, 2, 0, 958822, 288387, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_288387_958822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288387 ⟨958822, by decide⟩ :=
  accepted_of_selected 12 288387 ⟨958822, by decide⟩ ⟨12, 2, 0, 958822, 288387, 1897, 65536⟩
    (by decide) selected_cut_36258

theorem unmarked_context_11_72096_958823 : frontier 10 ⟨958823, by decide⟩
    (prefixCache 11 72096) (prefixPartial 11 72096) = false := by
  decide +kernel

theorem node_context_11_72096_958823 : EJMOriginalGlobalDAGData.nodes 10 ⟨958823, by decide⟩ =
    .split (coordinate 11) (![⟨958745, by decide⟩,⟨958770, by decide⟩,⟨958792, by decide⟩,⟨958822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72096_958823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72096 ⟨958823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72096
    ⟨958823, by decide⟩ (by decide) (![⟨958745, by decide⟩,⟨958770, by decide⟩,⟨958792, by decide⟩,⟨958822, by decide⟩]) unmarked_context_11_72096_958823 node_context_11_72096_958823
  intro a
  fin_cases a
  · exact context_12_288384_958745
  · exact context_12_288385_958770
  · exact context_12_288386_958792
  · exact context_12_288387_958822

theorem selected_cut_36259 : selected 9 ⟨958858, by decide⟩
    (prefixPartial 12 288388) = some ⟨12, 2, 0, 958858, 288388, 1953, 65536⟩ := by
  decide +kernel

theorem context_12_288388_958858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288388 ⟨958858, by decide⟩ :=
  accepted_of_selected 12 288388 ⟨958858, by decide⟩ ⟨12, 2, 0, 958858, 288388, 1953, 65536⟩
    (by decide) selected_cut_36259

theorem selected_cut_36260 : selected 9 ⟨958880, by decide⟩
    (prefixPartial 12 288389) = some ⟨12, 2, 0, 958880, 288389, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_288389_958880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288389 ⟨958880, by decide⟩ :=
  accepted_of_selected 12 288389 ⟨958880, by decide⟩ ⟨12, 2, 0, 958880, 288389, 1409, 65536⟩
    (by decide) selected_cut_36260

theorem selected_cut_36261 : selected 9 ⟨958903, by decide⟩
    (prefixPartial 12 288390) = some ⟨12, 2, 0, 958903, 288390, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_288390_958903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288390 ⟨958903, by decide⟩ :=
  accepted_of_selected 12 288390 ⟨958903, by decide⟩ ⟨12, 2, 0, 958903, 288390, 1513, 65536⟩
    (by decide) selected_cut_36261

theorem selected_cut_36262 : selected 9 ⟨958933, by decide⟩
    (prefixPartial 12 288391) = some ⟨12, 2, 0, 958933, 288391, 1761, 65536⟩ := by
  decide +kernel

theorem context_12_288391_958933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288391 ⟨958933, by decide⟩ :=
  accepted_of_selected 12 288391 ⟨958933, by decide⟩ ⟨12, 2, 0, 958933, 288391, 1761, 65536⟩
    (by decide) selected_cut_36262

theorem unmarked_context_11_72097_958934 : frontier 10 ⟨958934, by decide⟩
    (prefixCache 11 72097) (prefixPartial 11 72097) = false := by
  decide +kernel

theorem node_context_11_72097_958934 : EJMOriginalGlobalDAGData.nodes 10 ⟨958934, by decide⟩ =
    .split (coordinate 11) (![⟨958858, by decide⟩,⟨958880, by decide⟩,⟨958903, by decide⟩,⟨958933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72097_958934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72097 ⟨958934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72097
    ⟨958934, by decide⟩ (by decide) (![⟨958858, by decide⟩,⟨958880, by decide⟩,⟨958903, by decide⟩,⟨958933, by decide⟩]) unmarked_context_11_72097_958934 node_context_11_72097_958934
  intro a
  fin_cases a
  · exact context_12_288388_958858
  · exact context_12_288389_958880
  · exact context_12_288390_958903
  · exact context_12_288391_958933

theorem selected_cut_36263 : selected 9 ⟨958964, by decide⟩
    (prefixPartial 12 288392) = some ⟨12, 2, 0, 958964, 288392, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_288392_958964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288392 ⟨958964, by decide⟩ :=
  accepted_of_selected 12 288392 ⟨958964, by decide⟩ ⟨12, 2, 0, 958964, 288392, 1929, 65536⟩
    (by decide) selected_cut_36263

theorem selected_cut_36264 : selected 9 ⟨958985, by decide⟩
    (prefixPartial 12 288393) = some ⟨12, 2, 0, 958985, 288393, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_288393_958985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288393 ⟨958985, by decide⟩ :=
  accepted_of_selected 12 288393 ⟨958985, by decide⟩ ⟨12, 2, 0, 958985, 288393, 1429, 65536⟩
    (by decide) selected_cut_36264

theorem selected_cut_36265 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 288394) = some ⟨12, 1, 0, 893903, 288394, 1, 65536⟩ := by
  decide +kernel

theorem context_12_288394_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288394 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 288394 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 288394, 1, 65536⟩
    (by decide) selected_cut_36265

theorem selected_cut_36266 : selected 9 ⟨959013, by decide⟩
    (prefixPartial 12 288395) = some ⟨12, 2, 0, 959013, 288395, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_288395_959013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288395 ⟨959013, by decide⟩ :=
  accepted_of_selected 12 288395 ⟨959013, by decide⟩ ⟨12, 2, 0, 959013, 288395, 1721, 65536⟩
    (by decide) selected_cut_36266

theorem unmarked_context_11_72098_959014 : frontier 10 ⟨959014, by decide⟩
    (prefixCache 11 72098) (prefixPartial 11 72098) = false := by
  decide +kernel

theorem node_context_11_72098_959014 : EJMOriginalGlobalDAGData.nodes 10 ⟨959014, by decide⟩ =
    .split (coordinate 11) (![⟨958964, by decide⟩,⟨958985, by decide⟩,⟨893903, by decide⟩,⟨959013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72098_959014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72098 ⟨959014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72098
    ⟨959014, by decide⟩ (by decide) (![⟨958964, by decide⟩,⟨958985, by decide⟩,⟨893903, by decide⟩,⟨959013, by decide⟩]) unmarked_context_11_72098_959014 node_context_11_72098_959014
  intro a
  fin_cases a
  · exact context_12_288392_958964
  · exact context_12_288393_958985
  · exact context_12_288394_893903
  · exact context_12_288395_959013

theorem selected_cut_36267 : selected 9 ⟨959049, by decide⟩
    (prefixPartial 12 288396) = some ⟨12, 2, 0, 959049, 288396, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_288396_959049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288396 ⟨959049, by decide⟩ :=
  accepted_of_selected 12 288396 ⟨959049, by decide⟩ ⟨12, 2, 0, 959049, 288396, 1821, 65536⟩
    (by decide) selected_cut_36267

theorem selected_cut_36268 : selected 9 ⟨959068, by decide⟩
    (prefixPartial 12 288397) = some ⟨12, 2, 0, 959068, 288397, 1281, 65536⟩ := by
  decide +kernel

theorem context_12_288397_959068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288397 ⟨959068, by decide⟩ :=
  accepted_of_selected 12 288397 ⟨959068, by decide⟩ ⟨12, 2, 0, 959068, 288397, 1281, 65536⟩
    (by decide) selected_cut_36268

theorem selected_cut_36269 : selected 9 ⟨959092, by decide⟩
    (prefixPartial 12 288398) = some ⟨12, 2, 0, 959092, 288398, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_288398_959092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288398 ⟨959092, by decide⟩ :=
  accepted_of_selected 12 288398 ⟨959092, by decide⟩ ⟨12, 2, 0, 959092, 288398, 1389, 65536⟩
    (by decide) selected_cut_36269

theorem selected_cut_36270 : selected 9 ⟨959117, by decide⟩
    (prefixPartial 12 288399) = some ⟨12, 2, 0, 959117, 288399, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_288399_959117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288399 ⟨959117, by decide⟩ :=
  accepted_of_selected 12 288399 ⟨959117, by decide⟩ ⟨12, 2, 0, 959117, 288399, 1629, 65536⟩
    (by decide) selected_cut_36270

theorem unmarked_context_11_72099_959118 : frontier 10 ⟨959118, by decide⟩
    (prefixCache 11 72099) (prefixPartial 11 72099) = false := by
  decide +kernel

theorem node_context_11_72099_959118 : EJMOriginalGlobalDAGData.nodes 10 ⟨959118, by decide⟩ =
    .split (coordinate 11) (![⟨959049, by decide⟩,⟨959068, by decide⟩,⟨959092, by decide⟩,⟨959117, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72099_959118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72099 ⟨959118, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72099
    ⟨959118, by decide⟩ (by decide) (![⟨959049, by decide⟩,⟨959068, by decide⟩,⟨959092, by decide⟩,⟨959117, by decide⟩]) unmarked_context_11_72099_959118 node_context_11_72099_959118
  intro a
  fin_cases a
  · exact context_12_288396_959049
  · exact context_12_288397_959068
  · exact context_12_288398_959092
  · exact context_12_288399_959117

theorem unmarked_context_10_18024_959119 : frontier 11 ⟨959119, by decide⟩
    (prefixCache 10 18024) (prefixPartial 10 18024) = false := by
  decide +kernel

theorem node_context_10_18024_959119 : EJMOriginalGlobalDAGData.nodes 11 ⟨959119, by decide⟩ =
    .split (coordinate 10) (![⟨958823, by decide⟩,⟨958934, by decide⟩,⟨959014, by decide⟩,⟨959118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18024_959119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18024 ⟨959119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18024
    ⟨959119, by decide⟩ (by decide) (![⟨958823, by decide⟩,⟨958934, by decide⟩,⟨959014, by decide⟩,⟨959118, by decide⟩]) unmarked_context_10_18024_959119 node_context_10_18024_959119
  intro a
  fin_cases a
  · exact context_11_72096_958823
  · exact context_11_72097_958934
  · exact context_11_72098_959014
  · exact context_11_72099_959118

theorem selected_cut_36271 : selected 9 ⟨959138, by decide⟩
    (prefixPartial 12 288400) = some ⟨12, 2, 0, 959138, 288400, 1273, 65536⟩ := by
  decide +kernel

theorem context_12_288400_959138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288400 ⟨959138, by decide⟩ :=
  accepted_of_selected 12 288400 ⟨959138, by decide⟩ ⟨12, 2, 0, 959138, 288400, 1273, 65536⟩
    (by decide) selected_cut_36271

theorem selected_cut_36272 : selected 9 ⟨959157, by decide⟩
    (prefixPartial 12 288401) = some ⟨12, 2, 0, 959157, 288401, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_288401_959157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288401 ⟨959157, by decide⟩ :=
  accepted_of_selected 12 288401 ⟨959157, by decide⟩ ⟨12, 2, 0, 959157, 288401, 1117, 65536⟩
    (by decide) selected_cut_36272

theorem selected_cut_36273 : selected 9 ⟨959173, by decide⟩
    (prefixPartial 12 288402) = some ⟨12, 2, 0, 959173, 288402, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_288402_959173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288402 ⟨959173, by decide⟩ :=
  accepted_of_selected 12 288402 ⟨959173, by decide⟩ ⟨12, 2, 0, 959173, 288402, 1101, 65536⟩
    (by decide) selected_cut_36273

theorem selected_cut_36274 : selected 9 ⟨959192, by decide⟩
    (prefixPartial 12 288403) = some ⟨12, 2, 0, 959192, 288403, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_288403_959192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288403 ⟨959192, by decide⟩ :=
  accepted_of_selected 12 288403 ⟨959192, by decide⟩ ⟨12, 2, 0, 959192, 288403, 1349, 65536⟩
    (by decide) selected_cut_36274

theorem unmarked_context_11_72100_959193 : frontier 10 ⟨959193, by decide⟩
    (prefixCache 11 72100) (prefixPartial 11 72100) = false := by
  decide +kernel

theorem node_context_11_72100_959193 : EJMOriginalGlobalDAGData.nodes 10 ⟨959193, by decide⟩ =
    .split (coordinate 11) (![⟨959138, by decide⟩,⟨959157, by decide⟩,⟨959173, by decide⟩,⟨959192, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72100_959193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72100 ⟨959193, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72100
    ⟨959193, by decide⟩ (by decide) (![⟨959138, by decide⟩,⟨959157, by decide⟩,⟨959173, by decide⟩,⟨959192, by decide⟩]) unmarked_context_11_72100_959193 node_context_11_72100_959193
  intro a
  fin_cases a
  · exact context_12_288400_959138
  · exact context_12_288401_959157
  · exact context_12_288402_959173
  · exact context_12_288403_959192

theorem selected_cut_36275 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 72101) = some ⟨11, 1, 0, 892405, 72101, 1, 262144⟩ := by
  decide +kernel

theorem context_11_72101_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72101 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 72101 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 72101, 1, 262144⟩
    (by decide) selected_cut_36275

theorem selected_cut_36276 : selected 10 ⟨959253, by decide⟩
    (prefixPartial 11 72102) = some ⟨11, 2, 0, 959253, 72102, 3701, 262144⟩ := by
  decide +kernel

theorem context_11_72102_959253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72102 ⟨959253, by decide⟩ :=
  accepted_of_selected 11 72102 ⟨959253, by decide⟩ ⟨11, 2, 0, 959253, 72102, 3701, 262144⟩
    (by decide) selected_cut_36276

theorem selected_cut_36277 : selected 9 ⟨959272, by decide⟩
    (prefixPartial 12 288412) = some ⟨12, 2, 0, 959272, 288412, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_288412_959272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288412 ⟨959272, by decide⟩ :=
  accepted_of_selected 12 288412 ⟨959272, by decide⟩ ⟨12, 2, 0, 959272, 288412, 1229, 65536⟩
    (by decide) selected_cut_36277

theorem selected_cut_36278 : selected 9 ⟨959290, by decide⟩
    (prefixPartial 12 288413) = some ⟨12, 2, 0, 959290, 288413, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_288413_959290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288413 ⟨959290, by decide⟩ :=
  accepted_of_selected 12 288413 ⟨959290, by decide⟩ ⟨12, 2, 0, 959290, 288413, 1049, 65536⟩
    (by decide) selected_cut_36278

theorem selected_cut_36279 : selected 9 ⟨959310, by decide⟩
    (prefixPartial 12 288414) = some ⟨12, 2, 0, 959310, 288414, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_288414_959310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288414 ⟨959310, by decide⟩ :=
  accepted_of_selected 12 288414 ⟨959310, by decide⟩ ⟨12, 2, 0, 959310, 288414, 1117, 65536⟩
    (by decide) selected_cut_36279

theorem selected_cut_36280 : selected 9 ⟨959331, by decide⟩
    (prefixPartial 12 288415) = some ⟨12, 2, 0, 959331, 288415, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_288415_959331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 288415 ⟨959331, by decide⟩ :=
  accepted_of_selected 12 288415 ⟨959331, by decide⟩ ⟨12, 2, 0, 959331, 288415, 1269, 65536⟩
    (by decide) selected_cut_36280

theorem unmarked_context_11_72103_959332 : frontier 10 ⟨959332, by decide⟩
    (prefixCache 11 72103) (prefixPartial 11 72103) = false := by
  decide +kernel

theorem node_context_11_72103_959332 : EJMOriginalGlobalDAGData.nodes 10 ⟨959332, by decide⟩ =
    .split (coordinate 11) (![⟨959272, by decide⟩,⟨959290, by decide⟩,⟨959310, by decide⟩,⟨959331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_72103_959332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72103 ⟨959332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 72103
    ⟨959332, by decide⟩ (by decide) (![⟨959272, by decide⟩,⟨959290, by decide⟩,⟨959310, by decide⟩,⟨959331, by decide⟩]) unmarked_context_11_72103_959332 node_context_11_72103_959332
  intro a
  fin_cases a
  · exact context_12_288412_959272
  · exact context_12_288413_959290
  · exact context_12_288414_959310
  · exact context_12_288415_959331

theorem unmarked_context_10_18025_959333 : frontier 11 ⟨959333, by decide⟩
    (prefixCache 10 18025) (prefixPartial 10 18025) = false := by
  decide +kernel

theorem node_context_10_18025_959333 : EJMOriginalGlobalDAGData.nodes 11 ⟨959333, by decide⟩ =
    .split (coordinate 10) (![⟨959193, by decide⟩,⟨892405, by decide⟩,⟨959253, by decide⟩,⟨959332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18025_959333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18025 ⟨959333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18025
    ⟨959333, by decide⟩ (by decide) (![⟨959193, by decide⟩,⟨892405, by decide⟩,⟨959253, by decide⟩,⟨959332, by decide⟩]) unmarked_context_10_18025_959333 node_context_10_18025_959333
  intro a
  fin_cases a
  · exact context_11_72100_959193
  · exact context_11_72101_892405
  · exact context_11_72102_959253
  · exact context_11_72103_959332

theorem selected_cut_36281 : selected 10 ⟨959384, by decide⟩
    (prefixPartial 11 72104) = some ⟨11, 2, 0, 959384, 72104, 3253, 262144⟩ := by
  decide +kernel

theorem context_11_72104_959384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72104 ⟨959384, by decide⟩ :=
  accepted_of_selected 11 72104 ⟨959384, by decide⟩ ⟨11, 2, 0, 959384, 72104, 3253, 262144⟩
    (by decide) selected_cut_36281

theorem selected_cut_36282 : selected 10 ⟨959425, by decide⟩
    (prefixPartial 11 72105) = some ⟨11, 2, 0, 959425, 72105, 2825, 262144⟩ := by
  decide +kernel

theorem context_11_72105_959425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72105 ⟨959425, by decide⟩ :=
  accepted_of_selected 11 72105 ⟨959425, by decide⟩ ⟨11, 2, 0, 959425, 72105, 2825, 262144⟩
    (by decide) selected_cut_36282

theorem selected_cut_36283 : selected 10 ⟨959428, by decide⟩
    (prefixPartial 11 72106) = some ⟨11, 2, 0, 959428, 72106, 5, 262144⟩ := by
  decide +kernel

theorem context_11_72106_959428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72106 ⟨959428, by decide⟩ :=
  accepted_of_selected 11 72106 ⟨959428, by decide⟩ ⟨11, 2, 0, 959428, 72106, 5, 262144⟩
    (by decide) selected_cut_36283

theorem selected_cut_36284 : selected 10 ⟨959483, by decide⟩
    (prefixPartial 11 72107) = some ⟨11, 2, 0, 959483, 72107, 3089, 262144⟩ := by
  decide +kernel

theorem context_11_72107_959483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72107 ⟨959483, by decide⟩ :=
  accepted_of_selected 11 72107 ⟨959483, by decide⟩ ⟨11, 2, 0, 959483, 72107, 3089, 262144⟩
    (by decide) selected_cut_36284

theorem unmarked_context_10_18026_959484 : frontier 11 ⟨959484, by decide⟩
    (prefixCache 10 18026) (prefixPartial 10 18026) = false := by
  decide +kernel

theorem node_context_10_18026_959484 : EJMOriginalGlobalDAGData.nodes 11 ⟨959484, by decide⟩ =
    .split (coordinate 10) (![⟨959384, by decide⟩,⟨959425, by decide⟩,⟨959428, by decide⟩,⟨959483, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18026_959484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18026 ⟨959484, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18026
    ⟨959484, by decide⟩ (by decide) (![⟨959384, by decide⟩,⟨959425, by decide⟩,⟨959428, by decide⟩,⟨959483, by decide⟩]) unmarked_context_10_18026_959484 node_context_10_18026_959484
  intro a
  fin_cases a
  · exact context_11_72104_959384
  · exact context_11_72105_959425
  · exact context_11_72106_959428
  · exact context_11_72107_959483

theorem selected_cut_36285 : selected 10 ⟨959536, by decide⟩
    (prefixPartial 11 72108) = some ⟨11, 2, 0, 959536, 72108, 3469, 262144⟩ := by
  decide +kernel

theorem context_11_72108_959536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72108 ⟨959536, by decide⟩ :=
  accepted_of_selected 11 72108 ⟨959536, by decide⟩ ⟨11, 2, 0, 959536, 72108, 3469, 262144⟩
    (by decide) selected_cut_36285

theorem selected_cut_36286 : selected 10 ⟨959576, by decide⟩
    (prefixPartial 11 72109) = some ⟨11, 2, 0, 959576, 72109, 3065, 262144⟩ := by
  decide +kernel

theorem context_11_72109_959576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72109 ⟨959576, by decide⟩ :=
  accepted_of_selected 11 72109 ⟨959576, by decide⟩ ⟨11, 2, 0, 959576, 72109, 3065, 262144⟩
    (by decide) selected_cut_36286

theorem selected_cut_36287 : selected 10 ⟨959608, by decide⟩
    (prefixPartial 11 72110) = some ⟨11, 2, 0, 959608, 72110, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_72110_959608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72110 ⟨959608, by decide⟩ :=
  accepted_of_selected 11 72110 ⟨959608, by decide⟩ ⟨11, 2, 0, 959608, 72110, 2089, 262144⟩
    (by decide) selected_cut_36287

theorem selected_cut_36288 : selected 10 ⟨959655, by decide⟩
    (prefixPartial 11 72111) = some ⟨11, 2, 0, 959655, 72111, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_72111_959655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72111 ⟨959655, by decide⟩ :=
  accepted_of_selected 11 72111 ⟨959655, by decide⟩ ⟨11, 2, 0, 959655, 72111, 2817, 262144⟩
    (by decide) selected_cut_36288

theorem unmarked_context_10_18027_959656 : frontier 11 ⟨959656, by decide⟩
    (prefixCache 10 18027) (prefixPartial 10 18027) = false := by
  decide +kernel

theorem node_context_10_18027_959656 : EJMOriginalGlobalDAGData.nodes 11 ⟨959656, by decide⟩ =
    .split (coordinate 10) (![⟨959536, by decide⟩,⟨959576, by decide⟩,⟨959608, by decide⟩,⟨959655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18027_959656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18027 ⟨959656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18027
    ⟨959656, by decide⟩ (by decide) (![⟨959536, by decide⟩,⟨959576, by decide⟩,⟨959608, by decide⟩,⟨959655, by decide⟩]) unmarked_context_10_18027_959656 node_context_10_18027_959656
  intro a
  fin_cases a
  · exact context_11_72108_959536
  · exact context_11_72109_959576
  · exact context_11_72110_959608
  · exact context_11_72111_959655

theorem unmarked_context_9_4506_959657 : frontier 12 ⟨959657, by decide⟩
    (prefixCache 9 4506) (prefixPartial 9 4506) = false := by
  decide +kernel

theorem node_context_9_4506_959657 : EJMOriginalGlobalDAGData.nodes 12 ⟨959657, by decide⟩ =
    .split (coordinate 9) (![⟨959119, by decide⟩,⟨959333, by decide⟩,⟨959484, by decide⟩,⟨959656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4506_959657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4506 ⟨959657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4506
    ⟨959657, by decide⟩ (by decide) (![⟨959119, by decide⟩,⟨959333, by decide⟩,⟨959484, by decide⟩,⟨959656, by decide⟩]) unmarked_context_9_4506_959657 node_context_9_4506_959657
  intro a
  fin_cases a
  · exact context_10_18024_959119
  · exact context_10_18025_959333
  · exact context_10_18026_959484
  · exact context_10_18027_959656

theorem selected_cut_36289 : selected 10 ⟨959721, by decide⟩
    (prefixPartial 11 72112) = some ⟨11, 2, 0, 959721, 72112, 2985, 262144⟩ := by
  decide +kernel

theorem context_11_72112_959721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72112 ⟨959721, by decide⟩ :=
  accepted_of_selected 11 72112 ⟨959721, by decide⟩ ⟨11, 2, 0, 959721, 72112, 2985, 262144⟩
    (by decide) selected_cut_36289

theorem selected_cut_36290 : selected 10 ⟨959759, by decide⟩
    (prefixPartial 11 72113) = some ⟨11, 2, 0, 959759, 72113, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_72113_959759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 72113 ⟨959759, by decide⟩ :=
  accepted_of_selected 11 72113 ⟨959759, by decide⟩ ⟨11, 2, 0, 959759, 72113, 2377, 262144⟩
    (by decide) selected_cut_36290

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
