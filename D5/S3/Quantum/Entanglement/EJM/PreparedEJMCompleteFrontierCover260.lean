/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover259
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_24963 : selected 8 ⟨630945, by decide⟩
    (prefixPartial 13 310308) = some ⟨13, 2, 0, 630945, 310308, 3381, 16384⟩ := by
  decide +kernel

theorem context_13_310308_630945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310308 ⟨630945, by decide⟩ :=
  accepted_of_selected 13 310308 ⟨630945, by decide⟩ ⟨13, 2, 0, 630945, 310308, 3381, 16384⟩
    (by decide) selected_cut_24963

theorem selected_cut_24964 : selected 8 ⟨631049, by decide⟩
    (prefixPartial 13 310309) = some ⟨13, 2, 0, 631049, 310309, 3509, 16384⟩ := by
  decide +kernel

theorem context_13_310309_631049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310309 ⟨631049, by decide⟩ :=
  accepted_of_selected 13 310309 ⟨631049, by decide⟩ ⟨13, 2, 0, 631049, 310309, 3509, 16384⟩
    (by decide) selected_cut_24964

theorem selected_cut_24965 : selected 8 ⟨631176, by decide⟩
    (prefixPartial 13 310310) = some ⟨13, 2, 0, 631176, 310310, 2705, 16384⟩ := by
  decide +kernel

theorem context_13_310310_631176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310310 ⟨631176, by decide⟩ :=
  accepted_of_selected 13 310310 ⟨631176, by decide⟩ ⟨13, 2, 0, 631176, 310310, 2705, 16384⟩
    (by decide) selected_cut_24965

theorem selected_cut_24966 : selected 8 ⟨631208, by decide⟩
    (prefixPartial 13 310311) = some ⟨13, 2, 0, 631208, 310311, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_310311_631208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310311 ⟨631208, by decide⟩ :=
  accepted_of_selected 13 310311 ⟨631208, by decide⟩ ⟨13, 2, 0, 631208, 310311, 1025, 16384⟩
    (by decide) selected_cut_24966

theorem unmarked_context_12_77577_631209 : frontier 9 ⟨631209, by decide⟩
    (prefixCache 12 77577) (prefixPartial 12 77577) = false := by
  decide +kernel

theorem node_context_12_77577_631209 : EJMOriginalGlobalDAGData.nodes 9 ⟨631209, by decide⟩ =
    .split (coordinate 12) (![⟨630945, by decide⟩,⟨631049, by decide⟩,⟨631176, by decide⟩,⟨631208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77577_631209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77577 ⟨631209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77577
    ⟨631209, by decide⟩ (by decide) (![⟨630945, by decide⟩,⟨631049, by decide⟩,⟨631176, by decide⟩,⟨631208, by decide⟩]) unmarked_context_12_77577_631209 node_context_12_77577_631209
  intro a
  fin_cases a
  · exact context_13_310308_630945
  · exact context_13_310309_631049
  · exact context_13_310310_631176
  · exact context_13_310311_631208

theorem selected_cut_24967 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 77578) = some ⟨12, 1, 0, 524302, 77578, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77578_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77578 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 77578 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 77578, 1, 65536⟩
    (by decide) selected_cut_24967

theorem selected_cut_24968 : selected 9 ⟨604131, by decide⟩
    (prefixPartial 12 77579) = some ⟨12, 1, 0, 604131, 77579, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77579_604131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77579 ⟨604131, by decide⟩ :=
  accepted_of_selected 12 77579 ⟨604131, by decide⟩ ⟨12, 1, 0, 604131, 77579, 1, 65536⟩
    (by decide) selected_cut_24968

theorem unmarked_context_11_19394_631210 : frontier 10 ⟨631210, by decide⟩
    (prefixCache 11 19394) (prefixPartial 11 19394) = false := by
  decide +kernel

theorem node_context_11_19394_631210 : EJMOriginalGlobalDAGData.nodes 10 ⟨631210, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨631209, by decide⟩,⟨524302, by decide⟩,⟨604131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19394_631210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19394 ⟨631210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19394
    ⟨631210, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨631209, by decide⟩,⟨524302, by decide⟩,⟨604131, by decide⟩]) unmarked_context_11_19394_631210 node_context_11_19394_631210
  intro a
  fin_cases a
  · exact context_12_77576_448748
  · exact context_12_77577_631209
  · exact context_12_77578_524302
  · exact context_12_77579_604131

theorem selected_cut_24969 : selected 10 ⟨604133, by decide⟩
    (prefixPartial 11 19395) = some ⟨11, 2, 0, 604133, 19395, 5, 262144⟩ := by
  decide +kernel

theorem context_11_19395_604133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19395 ⟨604133, by decide⟩ :=
  accepted_of_selected 11 19395 ⟨604133, by decide⟩ ⟨11, 2, 0, 604133, 19395, 5, 262144⟩
    (by decide) selected_cut_24969

theorem unmarked_context_10_4848_631211 : frontier 11 ⟨631211, by decide⟩
    (prefixCache 10 4848) (prefixPartial 10 4848) = false := by
  decide +kernel

theorem node_context_10_4848_631211 : EJMOriginalGlobalDAGData.nodes 11 ⟨631211, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨630821, by decide⟩,⟨631210, by decide⟩,⟨604133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4848_631211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4848 ⟨631211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4848
    ⟨631211, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨630821, by decide⟩,⟨631210, by decide⟩,⟨604133, by decide⟩]) unmarked_context_10_4848_631211 node_context_10_4848_631211
  intro a
  fin_cases a
  · exact context_11_19392_434745
  · exact context_11_19393_630821
  · exact context_11_19394_631210
  · exact context_11_19395_604133

theorem selected_cut_24970 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 77584) = some ⟨12, 1, 0, 435160, 77584, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77584_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77584 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 77584 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 77584, 1, 65536⟩
    (by decide) selected_cut_24970

theorem selected_cut_24971 : selected 8 ⟨631276, by decide⟩
    (prefixPartial 13 310340) = some ⟨13, 2, 0, 631276, 310340, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_310340_631276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310340 ⟨631276, by decide⟩ :=
  accepted_of_selected 13 310340 ⟨631276, by decide⟩ ⟨13, 2, 0, 631276, 310340, 2329, 16384⟩
    (by decide) selected_cut_24971

theorem selected_cut_24972 : selected 8 ⟨631319, by decide⟩
    (prefixPartial 13 310341) = some ⟨13, 2, 0, 631319, 310341, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_310341_631319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310341 ⟨631319, by decide⟩ :=
  accepted_of_selected 13 310341 ⟨631319, by decide⟩ ⟨13, 2, 0, 631319, 310341, 2289, 16384⟩
    (by decide) selected_cut_24972

theorem selected_cut_24973 : selected 8 ⟨631375, by decide⟩
    (prefixPartial 13 310342) = some ⟨13, 2, 0, 631375, 310342, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_310342_631375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310342 ⟨631375, by decide⟩ :=
  accepted_of_selected 13 310342 ⟨631375, by decide⟩ ⟨13, 2, 0, 631375, 310342, 2037, 16384⟩
    (by decide) selected_cut_24973

theorem selected_cut_24974 : selected 8 ⟨631384, by decide⟩
    (prefixPartial 13 310343) = some ⟨13, 2, 0, 631384, 310343, 685, 16384⟩ := by
  decide +kernel

theorem context_13_310343_631384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310343 ⟨631384, by decide⟩ :=
  accepted_of_selected 13 310343 ⟨631384, by decide⟩ ⟨13, 2, 0, 631384, 310343, 685, 16384⟩
    (by decide) selected_cut_24974

theorem unmarked_context_12_77585_631385 : frontier 9 ⟨631385, by decide⟩
    (prefixCache 12 77585) (prefixPartial 12 77585) = false := by
  decide +kernel

theorem node_context_12_77585_631385 : EJMOriginalGlobalDAGData.nodes 9 ⟨631385, by decide⟩ =
    .split (coordinate 12) (![⟨631276, by decide⟩,⟨631319, by decide⟩,⟨631375, by decide⟩,⟨631384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77585_631385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77585 ⟨631385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77585
    ⟨631385, by decide⟩ (by decide) (![⟨631276, by decide⟩,⟨631319, by decide⟩,⟨631375, by decide⟩,⟨631384, by decide⟩]) unmarked_context_12_77585_631385 node_context_12_77585_631385
  intro a
  fin_cases a
  · exact context_13_310340_631276
  · exact context_13_310341_631319
  · exact context_13_310342_631375
  · exact context_13_310343_631384

theorem selected_cut_24975 : selected 8 ⟨631444, by decide⟩
    (prefixPartial 13 310344) = some ⟨13, 2, 0, 631444, 310344, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_310344_631444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310344 ⟨631444, by decide⟩ :=
  accepted_of_selected 13 310344 ⟨631444, by decide⟩ ⟨13, 2, 0, 631444, 310344, 2001, 16384⟩
    (by decide) selected_cut_24975

theorem selected_cut_24976 : selected 8 ⟨631492, by decide⟩
    (prefixPartial 13 310345) = some ⟨13, 2, 0, 631492, 310345, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_310345_631492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310345 ⟨631492, by decide⟩ :=
  accepted_of_selected 13 310345 ⟨631492, by decide⟩ ⟨13, 2, 0, 631492, 310345, 2229, 16384⟩
    (by decide) selected_cut_24976

theorem selected_cut_24977 : selected 8 ⟨631527, by decide⟩
    (prefixPartial 13 310346) = some ⟨13, 2, 0, 631527, 310346, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_310346_631527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310346 ⟨631527, by decide⟩ :=
  accepted_of_selected 13 310346 ⟨631527, by decide⟩ ⟨13, 2, 0, 631527, 310346, 1813, 16384⟩
    (by decide) selected_cut_24977

theorem selected_cut_24978 : selected 8 ⟨631537, by decide⟩
    (prefixPartial 13 310347) = some ⟨13, 2, 0, 631537, 310347, 645, 16384⟩ := by
  decide +kernel

theorem context_13_310347_631537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310347 ⟨631537, by decide⟩ :=
  accepted_of_selected 13 310347 ⟨631537, by decide⟩ ⟨13, 2, 0, 631537, 310347, 645, 16384⟩
    (by decide) selected_cut_24978

theorem unmarked_context_12_77586_631538 : frontier 9 ⟨631538, by decide⟩
    (prefixCache 12 77586) (prefixPartial 12 77586) = false := by
  decide +kernel

theorem node_context_12_77586_631538 : EJMOriginalGlobalDAGData.nodes 9 ⟨631538, by decide⟩ =
    .split (coordinate 12) (![⟨631444, by decide⟩,⟨631492, by decide⟩,⟨631527, by decide⟩,⟨631537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77586_631538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77586 ⟨631538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77586
    ⟨631538, by decide⟩ (by decide) (![⟨631444, by decide⟩,⟨631492, by decide⟩,⟨631527, by decide⟩,⟨631537, by decide⟩]) unmarked_context_12_77586_631538 node_context_12_77586_631538
  intro a
  fin_cases a
  · exact context_13_310344_631444
  · exact context_13_310345_631492
  · exact context_13_310346_631527
  · exact context_13_310347_631537

theorem selected_cut_24979 : selected 8 ⟨631581, by decide⟩
    (prefixPartial 13 310348) = some ⟨13, 2, 0, 631581, 310348, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_310348_631581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310348 ⟨631581, by decide⟩ :=
  accepted_of_selected 13 310348 ⟨631581, by decide⟩ ⟨13, 2, 0, 631581, 310348, 2021, 16384⟩
    (by decide) selected_cut_24979

theorem selected_cut_24980 : selected 8 ⟨631611, by decide⟩
    (prefixPartial 13 310349) = some ⟨13, 2, 0, 631611, 310349, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_310349_631611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310349 ⟨631611, by decide⟩ :=
  accepted_of_selected 13 310349 ⟨631611, by decide⟩ ⟨13, 2, 0, 631611, 310349, 2229, 16384⟩
    (by decide) selected_cut_24980

theorem selected_cut_24981 : selected 8 ⟨631636, by decide⟩
    (prefixPartial 13 310350) = some ⟨13, 2, 0, 631636, 310350, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_310350_631636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310350 ⟨631636, by decide⟩ :=
  accepted_of_selected 13 310350 ⟨631636, by decide⟩ ⟨13, 2, 0, 631636, 310350, 1837, 16384⟩
    (by decide) selected_cut_24981

theorem selected_cut_24982 : selected 8 ⟨631643, by decide⟩
    (prefixPartial 13 310351) = some ⟨13, 2, 0, 631643, 310351, 661, 16384⟩ := by
  decide +kernel

theorem context_13_310351_631643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310351 ⟨631643, by decide⟩ :=
  accepted_of_selected 13 310351 ⟨631643, by decide⟩ ⟨13, 2, 0, 631643, 310351, 661, 16384⟩
    (by decide) selected_cut_24982

theorem unmarked_context_12_77587_631644 : frontier 9 ⟨631644, by decide⟩
    (prefixCache 12 77587) (prefixPartial 12 77587) = false := by
  decide +kernel

theorem node_context_12_77587_631644 : EJMOriginalGlobalDAGData.nodes 9 ⟨631644, by decide⟩ =
    .split (coordinate 12) (![⟨631581, by decide⟩,⟨631611, by decide⟩,⟨631636, by decide⟩,⟨631643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77587_631644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77587 ⟨631644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77587
    ⟨631644, by decide⟩ (by decide) (![⟨631581, by decide⟩,⟨631611, by decide⟩,⟨631636, by decide⟩,⟨631643, by decide⟩]) unmarked_context_12_77587_631644 node_context_12_77587_631644
  intro a
  fin_cases a
  · exact context_13_310348_631581
  · exact context_13_310349_631611
  · exact context_13_310350_631636
  · exact context_13_310351_631643

theorem unmarked_context_11_19396_631645 : frontier 10 ⟨631645, by decide⟩
    (prefixCache 11 19396) (prefixPartial 11 19396) = false := by
  decide +kernel

theorem node_context_11_19396_631645 : EJMOriginalGlobalDAGData.nodes 10 ⟨631645, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨631385, by decide⟩,⟨631538, by decide⟩,⟨631644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19396_631645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19396 ⟨631645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19396
    ⟨631645, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨631385, by decide⟩,⟨631538, by decide⟩,⟨631644, by decide⟩]) unmarked_context_11_19396_631645 node_context_11_19396_631645
  intro a
  fin_cases a
  · exact context_12_77584_435160
  · exact context_12_77585_631385
  · exact context_12_77586_631538
  · exact context_12_77587_631644

theorem selected_cut_24983 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 77588) = some ⟨12, 1, 0, 435160, 77588, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77588_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77588 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 77588 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 77588, 1, 65536⟩
    (by decide) selected_cut_24983

theorem selected_cut_24984 : selected 8 ⟨631690, by decide⟩
    (prefixPartial 13 310356) = some ⟨13, 2, 0, 631690, 310356, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_310356_631690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310356 ⟨631690, by decide⟩ :=
  accepted_of_selected 13 310356 ⟨631690, by decide⟩ ⟨13, 2, 0, 631690, 310356, 2033, 16384⟩
    (by decide) selected_cut_24984

theorem selected_cut_24985 : selected 8 ⟨631732, by decide⟩
    (prefixPartial 13 310357) = some ⟨13, 2, 0, 631732, 310357, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_310357_631732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310357 ⟨631732, by decide⟩ :=
  accepted_of_selected 13 310357 ⟨631732, by decide⟩ ⟨13, 2, 0, 631732, 310357, 2305, 16384⟩
    (by decide) selected_cut_24985

theorem selected_cut_24986 : selected 8 ⟨631776, by decide⟩
    (prefixPartial 13 310358) = some ⟨13, 2, 0, 631776, 310358, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_310358_631776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310358 ⟨631776, by decide⟩ :=
  accepted_of_selected 13 310358 ⟨631776, by decide⟩ ⟨13, 2, 0, 631776, 310358, 2049, 16384⟩
    (by decide) selected_cut_24986

theorem selected_cut_24987 : selected 8 ⟨631785, by decide⟩
    (prefixPartial 13 310359) = some ⟨13, 2, 0, 631785, 310359, 713, 16384⟩ := by
  decide +kernel

theorem context_13_310359_631785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310359 ⟨631785, by decide⟩ :=
  accepted_of_selected 13 310359 ⟨631785, by decide⟩ ⟨13, 2, 0, 631785, 310359, 713, 16384⟩
    (by decide) selected_cut_24987

theorem unmarked_context_12_77589_631786 : frontier 9 ⟨631786, by decide⟩
    (prefixCache 12 77589) (prefixPartial 12 77589) = false := by
  decide +kernel

theorem node_context_12_77589_631786 : EJMOriginalGlobalDAGData.nodes 9 ⟨631786, by decide⟩ =
    .split (coordinate 12) (![⟨631690, by decide⟩,⟨631732, by decide⟩,⟨631776, by decide⟩,⟨631785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77589_631786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77589 ⟨631786, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77589
    ⟨631786, by decide⟩ (by decide) (![⟨631690, by decide⟩,⟨631732, by decide⟩,⟨631776, by decide⟩,⟨631785, by decide⟩]) unmarked_context_12_77589_631786 node_context_12_77589_631786
  intro a
  fin_cases a
  · exact context_13_310356_631690
  · exact context_13_310357_631732
  · exact context_13_310358_631776
  · exact context_13_310359_631785

theorem selected_cut_24988 : selected 8 ⟨631831, by decide⟩
    (prefixPartial 13 310360) = some ⟨13, 2, 0, 631831, 310360, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_310360_631831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310360 ⟨631831, by decide⟩ :=
  accepted_of_selected 13 310360 ⟨631831, by decide⟩ ⟨13, 2, 0, 631831, 310360, 1941, 16384⟩
    (by decide) selected_cut_24988

theorem selected_cut_24989 : selected 8 ⟨631870, by decide⟩
    (prefixPartial 13 310361) = some ⟨13, 2, 0, 631870, 310361, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_310361_631870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310361 ⟨631870, by decide⟩ :=
  accepted_of_selected 13 310361 ⟨631870, by decide⟩ ⟨13, 2, 0, 631870, 310361, 2345, 16384⟩
    (by decide) selected_cut_24989

theorem selected_cut_24990 : selected 8 ⟨631890, by decide⟩
    (prefixPartial 13 310362) = some ⟨13, 2, 0, 631890, 310362, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_310362_631890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310362 ⟨631890, by decide⟩ :=
  accepted_of_selected 13 310362 ⟨631890, by decide⟩ ⟨13, 2, 0, 631890, 310362, 1757, 16384⟩
    (by decide) selected_cut_24990

theorem selected_cut_24991 : selected 8 ⟨631898, by decide⟩
    (prefixPartial 13 310363) = some ⟨13, 2, 0, 631898, 310363, 761, 16384⟩ := by
  decide +kernel

theorem context_13_310363_631898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310363 ⟨631898, by decide⟩ :=
  accepted_of_selected 13 310363 ⟨631898, by decide⟩ ⟨13, 2, 0, 631898, 310363, 761, 16384⟩
    (by decide) selected_cut_24991

theorem unmarked_context_12_77590_631899 : frontier 9 ⟨631899, by decide⟩
    (prefixCache 12 77590) (prefixPartial 12 77590) = false := by
  decide +kernel

theorem node_context_12_77590_631899 : EJMOriginalGlobalDAGData.nodes 9 ⟨631899, by decide⟩ =
    .split (coordinate 12) (![⟨631831, by decide⟩,⟨631870, by decide⟩,⟨631890, by decide⟩,⟨631898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77590_631899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77590 ⟨631899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77590
    ⟨631899, by decide⟩ (by decide) (![⟨631831, by decide⟩,⟨631870, by decide⟩,⟨631890, by decide⟩,⟨631898, by decide⟩]) unmarked_context_12_77590_631899 node_context_12_77590_631899
  intro a
  fin_cases a
  · exact context_13_310360_631831
  · exact context_13_310361_631870
  · exact context_13_310362_631890
  · exact context_13_310363_631898

theorem selected_cut_24992 : selected 8 ⟨631934, by decide⟩
    (prefixPartial 13 310364) = some ⟨13, 2, 0, 631934, 310364, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_310364_631934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310364 ⟨631934, by decide⟩ :=
  accepted_of_selected 13 310364 ⟨631934, by decide⟩ ⟨13, 2, 0, 631934, 310364, 1841, 16384⟩
    (by decide) selected_cut_24992

theorem selected_cut_24993 : selected 8 ⟨631963, by decide⟩
    (prefixPartial 13 310365) = some ⟨13, 2, 0, 631963, 310365, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_310365_631963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310365 ⟨631963, by decide⟩ :=
  accepted_of_selected 13 310365 ⟨631963, by decide⟩ ⟨13, 2, 0, 631963, 310365, 2381, 16384⟩
    (by decide) selected_cut_24993

theorem selected_cut_24994 : selected 8 ⟨632000, by decide⟩
    (prefixPartial 13 310366) = some ⟨13, 2, 0, 632000, 310366, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_310366_632000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310366 ⟨632000, by decide⟩ :=
  accepted_of_selected 13 310366 ⟨632000, by decide⟩ ⟨13, 2, 0, 632000, 310366, 2009, 16384⟩
    (by decide) selected_cut_24994

theorem selected_cut_24995 : selected 8 ⟨632006, by decide⟩
    (prefixPartial 13 310367) = some ⟨13, 2, 0, 632006, 310367, 757, 16384⟩ := by
  decide +kernel

theorem context_13_310367_632006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310367 ⟨632006, by decide⟩ :=
  accepted_of_selected 13 310367 ⟨632006, by decide⟩ ⟨13, 2, 0, 632006, 310367, 757, 16384⟩
    (by decide) selected_cut_24995

theorem unmarked_context_12_77591_632007 : frontier 9 ⟨632007, by decide⟩
    (prefixCache 12 77591) (prefixPartial 12 77591) = false := by
  decide +kernel

theorem node_context_12_77591_632007 : EJMOriginalGlobalDAGData.nodes 9 ⟨632007, by decide⟩ =
    .split (coordinate 12) (![⟨631934, by decide⟩,⟨631963, by decide⟩,⟨632000, by decide⟩,⟨632006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77591_632007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77591 ⟨632007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77591
    ⟨632007, by decide⟩ (by decide) (![⟨631934, by decide⟩,⟨631963, by decide⟩,⟨632000, by decide⟩,⟨632006, by decide⟩]) unmarked_context_12_77591_632007 node_context_12_77591_632007
  intro a
  fin_cases a
  · exact context_13_310364_631934
  · exact context_13_310365_631963
  · exact context_13_310366_632000
  · exact context_13_310367_632006

theorem unmarked_context_11_19397_632008 : frontier 10 ⟨632008, by decide⟩
    (prefixCache 11 19397) (prefixPartial 11 19397) = false := by
  decide +kernel

theorem node_context_11_19397_632008 : EJMOriginalGlobalDAGData.nodes 10 ⟨632008, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨631786, by decide⟩,⟨631899, by decide⟩,⟨632007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19397_632008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19397 ⟨632008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19397
    ⟨632008, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨631786, by decide⟩,⟨631899, by decide⟩,⟨632007, by decide⟩]) unmarked_context_11_19397_632008 node_context_11_19397_632008
  intro a
  fin_cases a
  · exact context_12_77588_435160
  · exact context_12_77589_631786
  · exact context_12_77590_631899
  · exact context_12_77591_632007

theorem selected_cut_24996 : selected 8 ⟨632071, by decide⟩
    (prefixPartial 13 310368) = some ⟨13, 2, 0, 632071, 310368, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_310368_632071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310368 ⟨632071, by decide⟩ :=
  accepted_of_selected 13 310368 ⟨632071, by decide⟩ ⟨13, 2, 0, 632071, 310368, 1273, 16384⟩
    (by decide) selected_cut_24996

theorem selected_cut_24997 : selected 8 ⟨632162, by decide⟩
    (prefixPartial 13 310369) = some ⟨13, 2, 0, 632162, 310369, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_310369_632162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310369 ⟨632162, by decide⟩ :=
  accepted_of_selected 13 310369 ⟨632162, by decide⟩ ⟨13, 2, 0, 632162, 310369, 2425, 16384⟩
    (by decide) selected_cut_24997

theorem selected_cut_24998 : selected 8 ⟨632250, by decide⟩
    (prefixPartial 13 310370) = some ⟨13, 2, 0, 632250, 310370, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_310370_632250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310370 ⟨632250, by decide⟩ :=
  accepted_of_selected 13 310370 ⟨632250, by decide⟩ ⟨13, 2, 0, 632250, 310370, 1817, 16384⟩
    (by decide) selected_cut_24998

theorem selected_cut_24999 : selected 8 ⟨632284, by decide⟩
    (prefixPartial 13 310371) = some ⟨13, 2, 0, 632284, 310371, 725, 16384⟩ := by
  decide +kernel

theorem context_13_310371_632284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310371 ⟨632284, by decide⟩ :=
  accepted_of_selected 13 310371 ⟨632284, by decide⟩ ⟨13, 2, 0, 632284, 310371, 725, 16384⟩
    (by decide) selected_cut_24999

theorem unmarked_context_12_77592_632285 : frontier 9 ⟨632285, by decide⟩
    (prefixCache 12 77592) (prefixPartial 12 77592) = false := by
  decide +kernel

theorem node_context_12_77592_632285 : EJMOriginalGlobalDAGData.nodes 9 ⟨632285, by decide⟩ =
    .split (coordinate 12) (![⟨632071, by decide⟩,⟨632162, by decide⟩,⟨632250, by decide⟩,⟨632284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77592_632285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77592 ⟨632285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77592
    ⟨632285, by decide⟩ (by decide) (![⟨632071, by decide⟩,⟨632162, by decide⟩,⟨632250, by decide⟩,⟨632284, by decide⟩]) unmarked_context_12_77592_632285 node_context_12_77592_632285
  intro a
  fin_cases a
  · exact context_13_310368_632071
  · exact context_13_310369_632162
  · exact context_13_310370_632250
  · exact context_13_310371_632284

theorem selected_cut_25000 : selected 8 ⟨632318, by decide⟩
    (prefixPartial 13 310372) = some ⟨13, 2, 0, 632318, 310372, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_310372_632318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310372 ⟨632318, by decide⟩ :=
  accepted_of_selected 13 310372 ⟨632318, by decide⟩ ⟨13, 2, 0, 632318, 310372, 1769, 16384⟩
    (by decide) selected_cut_25000

theorem selected_cut_25001 : selected 8 ⟨632362, by decide⟩
    (prefixPartial 13 310373) = some ⟨13, 2, 0, 632362, 310373, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_310373_632362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310373 ⟨632362, by decide⟩ :=
  accepted_of_selected 13 310373 ⟨632362, by decide⟩ ⟨13, 2, 0, 632362, 310373, 2385, 16384⟩
    (by decide) selected_cut_25001

theorem selected_cut_25002 : selected 8 ⟨632407, by decide⟩
    (prefixPartial 13 310374) = some ⟨13, 2, 0, 632407, 310374, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_310374_632407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310374 ⟨632407, by decide⟩ :=
  accepted_of_selected 13 310374 ⟨632407, by decide⟩ ⟨13, 2, 0, 632407, 310374, 2257, 16384⟩
    (by decide) selected_cut_25002

theorem selected_cut_25003 : selected 8 ⟨632425, by decide⟩
    (prefixPartial 13 310375) = some ⟨13, 2, 0, 632425, 310375, 877, 16384⟩ := by
  decide +kernel

theorem context_13_310375_632425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310375 ⟨632425, by decide⟩ :=
  accepted_of_selected 13 310375 ⟨632425, by decide⟩ ⟨13, 2, 0, 632425, 310375, 877, 16384⟩
    (by decide) selected_cut_25003

theorem unmarked_context_12_77593_632426 : frontier 9 ⟨632426, by decide⟩
    (prefixCache 12 77593) (prefixPartial 12 77593) = false := by
  decide +kernel

theorem node_context_12_77593_632426 : EJMOriginalGlobalDAGData.nodes 9 ⟨632426, by decide⟩ =
    .split (coordinate 12) (![⟨632318, by decide⟩,⟨632362, by decide⟩,⟨632407, by decide⟩,⟨632425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77593_632426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77593 ⟨632426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77593
    ⟨632426, by decide⟩ (by decide) (![⟨632318, by decide⟩,⟨632362, by decide⟩,⟨632407, by decide⟩,⟨632425, by decide⟩]) unmarked_context_12_77593_632426 node_context_12_77593_632426
  intro a
  fin_cases a
  · exact context_13_310372_632318
  · exact context_13_310373_632362
  · exact context_13_310374_632407
  · exact context_13_310375_632425

theorem selected_cut_25004 : selected 8 ⟨632454, by decide⟩
    (prefixPartial 13 310376) = some ⟨13, 2, 0, 632454, 310376, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_310376_632454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310376 ⟨632454, by decide⟩ :=
  accepted_of_selected 13 310376 ⟨632454, by decide⟩ ⟨13, 2, 0, 632454, 310376, 1309, 16384⟩
    (by decide) selected_cut_25004

theorem selected_cut_25005 : selected 8 ⟨632506, by decide⟩
    (prefixPartial 13 310377) = some ⟨13, 2, 0, 632506, 310377, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_310377_632506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310377 ⟨632506, by decide⟩ :=
  accepted_of_selected 13 310377 ⟨632506, by decide⟩ ⟨13, 2, 0, 632506, 310377, 2369, 16384⟩
    (by decide) selected_cut_25005

theorem selected_cut_25006 : selected 8 ⟨632538, by decide⟩
    (prefixPartial 13 310378) = some ⟨13, 2, 0, 632538, 310378, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_310378_632538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310378 ⟨632538, by decide⟩ :=
  accepted_of_selected 13 310378 ⟨632538, by decide⟩ ⟨13, 2, 0, 632538, 310378, 1885, 16384⟩
    (by decide) selected_cut_25006

theorem selected_cut_25007 : selected 8 ⟨632549, by decide⟩
    (prefixPartial 13 310379) = some ⟨13, 2, 0, 632549, 310379, 809, 16384⟩ := by
  decide +kernel

theorem context_13_310379_632549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310379 ⟨632549, by decide⟩ :=
  accepted_of_selected 13 310379 ⟨632549, by decide⟩ ⟨13, 2, 0, 632549, 310379, 809, 16384⟩
    (by decide) selected_cut_25007

theorem unmarked_context_12_77594_632550 : frontier 9 ⟨632550, by decide⟩
    (prefixCache 12 77594) (prefixPartial 12 77594) = false := by
  decide +kernel

theorem node_context_12_77594_632550 : EJMOriginalGlobalDAGData.nodes 9 ⟨632550, by decide⟩ =
    .split (coordinate 12) (![⟨632454, by decide⟩,⟨632506, by decide⟩,⟨632538, by decide⟩,⟨632549, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77594_632550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77594 ⟨632550, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77594
    ⟨632550, by decide⟩ (by decide) (![⟨632454, by decide⟩,⟨632506, by decide⟩,⟨632538, by decide⟩,⟨632549, by decide⟩]) unmarked_context_12_77594_632550 node_context_12_77594_632550
  intro a
  fin_cases a
  · exact context_13_310376_632454
  · exact context_13_310377_632506
  · exact context_13_310378_632538
  · exact context_13_310379_632549

theorem selected_cut_25008 : selected 8 ⟨632577, by decide⟩
    (prefixPartial 13 310380) = some ⟨13, 2, 0, 632577, 310380, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_310380_632577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310380 ⟨632577, by decide⟩ :=
  accepted_of_selected 13 310380 ⟨632577, by decide⟩ ⟨13, 2, 0, 632577, 310380, 1425, 16384⟩
    (by decide) selected_cut_25008

theorem selected_cut_25009 : selected 8 ⟨632617, by decide⟩
    (prefixPartial 13 310381) = some ⟨13, 2, 0, 632617, 310381, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_310381_632617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310381 ⟨632617, by decide⟩ :=
  accepted_of_selected 13 310381 ⟨632617, by decide⟩ ⟨13, 2, 0, 632617, 310381, 2509, 16384⟩
    (by decide) selected_cut_25009

theorem selected_cut_25010 : selected 8 ⟨632643, by decide⟩
    (prefixPartial 13 310382) = some ⟨13, 2, 0, 632643, 310382, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_310382_632643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310382 ⟨632643, by decide⟩ :=
  accepted_of_selected 13 310382 ⟨632643, by decide⟩ ⟨13, 2, 0, 632643, 310382, 2013, 16384⟩
    (by decide) selected_cut_25010

theorem selected_cut_25011 : selected 8 ⟨632657, by decide⟩
    (prefixPartial 13 310383) = some ⟨13, 2, 0, 632657, 310383, 801, 16384⟩ := by
  decide +kernel

theorem context_13_310383_632657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310383 ⟨632657, by decide⟩ :=
  accepted_of_selected 13 310383 ⟨632657, by decide⟩ ⟨13, 2, 0, 632657, 310383, 801, 16384⟩
    (by decide) selected_cut_25011

theorem unmarked_context_12_77595_632658 : frontier 9 ⟨632658, by decide⟩
    (prefixCache 12 77595) (prefixPartial 12 77595) = false := by
  decide +kernel

theorem node_context_12_77595_632658 : EJMOriginalGlobalDAGData.nodes 9 ⟨632658, by decide⟩ =
    .split (coordinate 12) (![⟨632577, by decide⟩,⟨632617, by decide⟩,⟨632643, by decide⟩,⟨632657, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77595_632658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77595 ⟨632658, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77595
    ⟨632658, by decide⟩ (by decide) (![⟨632577, by decide⟩,⟨632617, by decide⟩,⟨632643, by decide⟩,⟨632657, by decide⟩]) unmarked_context_12_77595_632658 node_context_12_77595_632658
  intro a
  fin_cases a
  · exact context_13_310380_632577
  · exact context_13_310381_632617
  · exact context_13_310382_632643
  · exact context_13_310383_632657

theorem unmarked_context_11_19398_632659 : frontier 10 ⟨632659, by decide⟩
    (prefixCache 11 19398) (prefixPartial 11 19398) = false := by
  decide +kernel

theorem node_context_11_19398_632659 : EJMOriginalGlobalDAGData.nodes 10 ⟨632659, by decide⟩ =
    .split (coordinate 11) (![⟨632285, by decide⟩,⟨632426, by decide⟩,⟨632550, by decide⟩,⟨632658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19398_632659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19398 ⟨632659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19398
    ⟨632659, by decide⟩ (by decide) (![⟨632285, by decide⟩,⟨632426, by decide⟩,⟨632550, by decide⟩,⟨632658, by decide⟩]) unmarked_context_11_19398_632659 node_context_11_19398_632659
  intro a
  fin_cases a
  · exact context_12_77592_632285
  · exact context_12_77593_632426
  · exact context_12_77594_632550
  · exact context_12_77595_632658

theorem selected_cut_25012 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 77596) = some ⟨12, 1, 0, 539296, 77596, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77596_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77596 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 77596 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 77596, 1, 65536⟩
    (by decide) selected_cut_25012

theorem selected_cut_25013 : selected 8 ⟨632680, by decide⟩
    (prefixPartial 13 310388) = some ⟨13, 2, 0, 632680, 310388, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_310388_632680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310388 ⟨632680, by decide⟩ :=
  accepted_of_selected 13 310388 ⟨632680, by decide⟩ ⟨13, 2, 0, 632680, 310388, 1253, 16384⟩
    (by decide) selected_cut_25013

theorem selected_cut_25014 : selected 8 ⟨632719, by decide⟩
    (prefixPartial 13 310389) = some ⟨13, 2, 0, 632719, 310389, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_310389_632719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310389 ⟨632719, by decide⟩ :=
  accepted_of_selected 13 310389 ⟨632719, by decide⟩ ⟨13, 2, 0, 632719, 310389, 2249, 16384⟩
    (by decide) selected_cut_25014

theorem selected_cut_25015 : selected 8 ⟨632772, by decide⟩
    (prefixPartial 13 310390) = some ⟨13, 2, 0, 632772, 310390, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_310390_632772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310390 ⟨632772, by decide⟩ :=
  accepted_of_selected 13 310390 ⟨632772, by decide⟩ ⟨13, 2, 0, 632772, 310390, 2053, 16384⟩
    (by decide) selected_cut_25015

theorem selected_cut_25016 : selected 8 ⟨632781, by decide⟩
    (prefixPartial 13 310391) = some ⟨13, 2, 0, 632781, 310391, 693, 16384⟩ := by
  decide +kernel

theorem context_13_310391_632781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310391 ⟨632781, by decide⟩ :=
  accepted_of_selected 13 310391 ⟨632781, by decide⟩ ⟨13, 2, 0, 632781, 310391, 693, 16384⟩
    (by decide) selected_cut_25016

theorem unmarked_context_12_77597_632782 : frontier 9 ⟨632782, by decide⟩
    (prefixCache 12 77597) (prefixPartial 12 77597) = false := by
  decide +kernel

theorem node_context_12_77597_632782 : EJMOriginalGlobalDAGData.nodes 9 ⟨632782, by decide⟩ =
    .split (coordinate 12) (![⟨632680, by decide⟩,⟨632719, by decide⟩,⟨632772, by decide⟩,⟨632781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77597_632782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77597 ⟨632782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77597
    ⟨632782, by decide⟩ (by decide) (![⟨632680, by decide⟩,⟨632719, by decide⟩,⟨632772, by decide⟩,⟨632781, by decide⟩]) unmarked_context_12_77597_632782 node_context_12_77597_632782
  intro a
  fin_cases a
  · exact context_13_310388_632680
  · exact context_13_310389_632719
  · exact context_13_310390_632772
  · exact context_13_310391_632781

theorem selected_cut_25017 : selected 8 ⟨632811, by decide⟩
    (prefixPartial 13 310392) = some ⟨13, 2, 0, 632811, 310392, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_310392_632811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310392 ⟨632811, by decide⟩ :=
  accepted_of_selected 13 310392 ⟨632811, by decide⟩ ⟨13, 2, 0, 632811, 310392, 1093, 16384⟩
    (by decide) selected_cut_25017

theorem selected_cut_25018 : selected 8 ⟨632860, by decide⟩
    (prefixPartial 13 310393) = some ⟨13, 2, 0, 632860, 310393, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_310393_632860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310393 ⟨632860, by decide⟩ :=
  accepted_of_selected 13 310393 ⟨632860, by decide⟩ ⟨13, 2, 0, 632860, 310393, 2301, 16384⟩
    (by decide) selected_cut_25018

theorem selected_cut_25019 : selected 8 ⟨632886, by decide⟩
    (prefixPartial 13 310394) = some ⟨13, 2, 0, 632886, 310394, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_310394_632886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310394 ⟨632886, by decide⟩ :=
  accepted_of_selected 13 310394 ⟨632886, by decide⟩ ⟨13, 2, 0, 632886, 310394, 1581, 16384⟩
    (by decide) selected_cut_25019

theorem selected_cut_25020 : selected 8 ⟨632895, by decide⟩
    (prefixPartial 13 310395) = some ⟨13, 2, 0, 632895, 310395, 681, 16384⟩ := by
  decide +kernel

theorem context_13_310395_632895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310395 ⟨632895, by decide⟩ :=
  accepted_of_selected 13 310395 ⟨632895, by decide⟩ ⟨13, 2, 0, 632895, 310395, 681, 16384⟩
    (by decide) selected_cut_25020

theorem unmarked_context_12_77598_632896 : frontier 9 ⟨632896, by decide⟩
    (prefixCache 12 77598) (prefixPartial 12 77598) = false := by
  decide +kernel

theorem node_context_12_77598_632896 : EJMOriginalGlobalDAGData.nodes 9 ⟨632896, by decide⟩ =
    .split (coordinate 12) (![⟨632811, by decide⟩,⟨632860, by decide⟩,⟨632886, by decide⟩,⟨632895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77598_632896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77598 ⟨632896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77598
    ⟨632896, by decide⟩ (by decide) (![⟨632811, by decide⟩,⟨632860, by decide⟩,⟨632886, by decide⟩,⟨632895, by decide⟩]) unmarked_context_12_77598_632896 node_context_12_77598_632896
  intro a
  fin_cases a
  · exact context_13_310392_632811
  · exact context_13_310393_632860
  · exact context_13_310394_632886
  · exact context_13_310395_632895

theorem selected_cut_25021 : selected 9 ⟨632897, by decide⟩
    (prefixPartial 12 77599) = some ⟨12, 1, 0, 632897, 77599, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77599_632897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77599 ⟨632897, by decide⟩ :=
  accepted_of_selected 12 77599 ⟨632897, by decide⟩ ⟨12, 1, 0, 632897, 77599, 1, 65536⟩
    (by decide) selected_cut_25021

theorem unmarked_context_11_19399_632898 : frontier 10 ⟨632898, by decide⟩
    (prefixCache 11 19399) (prefixPartial 11 19399) = false := by
  decide +kernel

theorem node_context_11_19399_632898 : EJMOriginalGlobalDAGData.nodes 10 ⟨632898, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨632782, by decide⟩,⟨632896, by decide⟩,⟨632897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19399_632898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19399 ⟨632898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19399
    ⟨632898, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨632782, by decide⟩,⟨632896, by decide⟩,⟨632897, by decide⟩]) unmarked_context_11_19399_632898 node_context_11_19399_632898
  intro a
  fin_cases a
  · exact context_12_77596_539296
  · exact context_12_77597_632782
  · exact context_12_77598_632896
  · exact context_12_77599_632897

theorem unmarked_context_10_4849_632899 : frontier 11 ⟨632899, by decide⟩
    (prefixCache 10 4849) (prefixPartial 10 4849) = false := by
  decide +kernel

theorem node_context_10_4849_632899 : EJMOriginalGlobalDAGData.nodes 11 ⟨632899, by decide⟩ =
    .split (coordinate 10) (![⟨631645, by decide⟩,⟨632008, by decide⟩,⟨632659, by decide⟩,⟨632898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4849_632899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4849 ⟨632899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4849
    ⟨632899, by decide⟩ (by decide) (![⟨631645, by decide⟩,⟨632008, by decide⟩,⟨632659, by decide⟩,⟨632898, by decide⟩]) unmarked_context_10_4849_632899 node_context_10_4849_632899
  intro a
  fin_cases a
  · exact context_11_19396_631645
  · exact context_11_19397_632008
  · exact context_11_19398_632659
  · exact context_11_19399_632898

theorem selected_cut_25022 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 77600) = some ⟨12, 1, 0, 435790, 77600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77600_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77600 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 77600 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 77600, 1, 65536⟩
    (by decide) selected_cut_25022

theorem selected_cut_25023 : selected 8 ⟨632926, by decide⟩
    (prefixPartial 13 310404) = some ⟨13, 2, 0, 632926, 310404, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_310404_632926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310404 ⟨632926, by decide⟩ :=
  accepted_of_selected 13 310404 ⟨632926, by decide⟩ ⟨13, 2, 0, 632926, 310404, 1257, 16384⟩
    (by decide) selected_cut_25023

theorem selected_cut_25024 : selected 8 ⟨632978, by decide⟩
    (prefixPartial 13 310405) = some ⟨13, 2, 0, 632978, 310405, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_310405_632978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310405 ⟨632978, by decide⟩ :=
  accepted_of_selected 13 310405 ⟨632978, by decide⟩ ⟨13, 2, 0, 632978, 310405, 2301, 16384⟩
    (by decide) selected_cut_25024

theorem selected_cut_25025 : selected 8 ⟨633018, by decide⟩
    (prefixPartial 13 310406) = some ⟨13, 2, 0, 633018, 310406, 1849, 16384⟩ := by
  decide +kernel

theorem context_13_310406_633018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310406 ⟨633018, by decide⟩ :=
  accepted_of_selected 13 310406 ⟨633018, by decide⟩ ⟨13, 2, 0, 633018, 310406, 1849, 16384⟩
    (by decide) selected_cut_25025

theorem selected_cut_25026 : selected 8 ⟨633024, by decide⟩
    (prefixPartial 13 310407) = some ⟨13, 2, 0, 633024, 310407, 533, 16384⟩ := by
  decide +kernel

theorem context_13_310407_633024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310407 ⟨633024, by decide⟩ :=
  accepted_of_selected 13 310407 ⟨633024, by decide⟩ ⟨13, 2, 0, 633024, 310407, 533, 16384⟩
    (by decide) selected_cut_25026

theorem unmarked_context_12_77601_633025 : frontier 9 ⟨633025, by decide⟩
    (prefixCache 12 77601) (prefixPartial 12 77601) = false := by
  decide +kernel

theorem node_context_12_77601_633025 : EJMOriginalGlobalDAGData.nodes 9 ⟨633025, by decide⟩ =
    .split (coordinate 12) (![⟨632926, by decide⟩,⟨632978, by decide⟩,⟨633018, by decide⟩,⟨633024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77601_633025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77601 ⟨633025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77601
    ⟨633025, by decide⟩ (by decide) (![⟨632926, by decide⟩,⟨632978, by decide⟩,⟨633018, by decide⟩,⟨633024, by decide⟩]) unmarked_context_12_77601_633025 node_context_12_77601_633025
  intro a
  fin_cases a
  · exact context_13_310404_632926
  · exact context_13_310405_632978
  · exact context_13_310406_633018
  · exact context_13_310407_633024

theorem selected_cut_25027 : selected 8 ⟨633045, by decide⟩
    (prefixPartial 13 310408) = some ⟨13, 2, 0, 633045, 310408, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_310408_633045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310408 ⟨633045, by decide⟩ :=
  accepted_of_selected 13 310408 ⟨633045, by decide⟩ ⟨13, 2, 0, 633045, 310408, 1045, 16384⟩
    (by decide) selected_cut_25027

theorem selected_cut_25028 : selected 8 ⟨633083, by decide⟩
    (prefixPartial 13 310409) = some ⟨13, 2, 0, 633083, 310409, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_310409_633083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310409 ⟨633083, by decide⟩ :=
  accepted_of_selected 13 310409 ⟨633083, by decide⟩ ⟨13, 2, 0, 633083, 310409, 2009, 16384⟩
    (by decide) selected_cut_25028

theorem selected_cut_25029 : selected 8 ⟨633108, by decide⟩
    (prefixPartial 13 310410) = some ⟨13, 2, 0, 633108, 310410, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_310410_633108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310410 ⟨633108, by decide⟩ :=
  accepted_of_selected 13 310410 ⟨633108, by decide⟩ ⟨13, 2, 0, 633108, 310410, 1481, 16384⟩
    (by decide) selected_cut_25029

theorem selected_cut_25030 : selected 8 ⟨633114, by decide⟩
    (prefixPartial 13 310411) = some ⟨13, 2, 0, 633114, 310411, 597, 16384⟩ := by
  decide +kernel

theorem context_13_310411_633114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310411 ⟨633114, by decide⟩ :=
  accepted_of_selected 13 310411 ⟨633114, by decide⟩ ⟨13, 2, 0, 633114, 310411, 597, 16384⟩
    (by decide) selected_cut_25030

theorem unmarked_context_12_77602_633115 : frontier 9 ⟨633115, by decide⟩
    (prefixCache 12 77602) (prefixPartial 12 77602) = false := by
  decide +kernel

theorem node_context_12_77602_633115 : EJMOriginalGlobalDAGData.nodes 9 ⟨633115, by decide⟩ =
    .split (coordinate 12) (![⟨633045, by decide⟩,⟨633083, by decide⟩,⟨633108, by decide⟩,⟨633114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77602_633115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77602 ⟨633115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77602
    ⟨633115, by decide⟩ (by decide) (![⟨633045, by decide⟩,⟨633083, by decide⟩,⟨633108, by decide⟩,⟨633114, by decide⟩]) unmarked_context_12_77602_633115 node_context_12_77602_633115
  intro a
  fin_cases a
  · exact context_13_310408_633045
  · exact context_13_310409_633083
  · exact context_13_310410_633108
  · exact context_13_310411_633114

theorem selected_cut_25031 : selected 8 ⟨633136, by decide⟩
    (prefixPartial 13 310412) = some ⟨13, 2, 0, 633136, 310412, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_310412_633136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310412 ⟨633136, by decide⟩ :=
  accepted_of_selected 13 310412 ⟨633136, by decide⟩ ⟨13, 2, 0, 633136, 310412, 1121, 16384⟩
    (by decide) selected_cut_25031

theorem selected_cut_25032 : selected 8 ⟨633169, by decide⟩
    (prefixPartial 13 310413) = some ⟨13, 2, 0, 633169, 310413, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_310413_633169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310413 ⟨633169, by decide⟩ :=
  accepted_of_selected 13 310413 ⟨633169, by decide⟩ ⟨13, 2, 0, 633169, 310413, 2205, 16384⟩
    (by decide) selected_cut_25032

theorem selected_cut_25033 : selected 8 ⟨633192, by decide⟩
    (prefixPartial 13 310414) = some ⟨13, 2, 0, 633192, 310414, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_310414_633192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310414 ⟨633192, by decide⟩ :=
  accepted_of_selected 13 310414 ⟨633192, by decide⟩ ⟨13, 2, 0, 633192, 310414, 1693, 16384⟩
    (by decide) selected_cut_25033

theorem selected_cut_25034 : selected 8 ⟨633198, by decide⟩
    (prefixPartial 13 310415) = some ⟨13, 2, 0, 633198, 310415, 645, 16384⟩ := by
  decide +kernel

theorem context_13_310415_633198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310415 ⟨633198, by decide⟩ :=
  accepted_of_selected 13 310415 ⟨633198, by decide⟩ ⟨13, 2, 0, 633198, 310415, 645, 16384⟩
    (by decide) selected_cut_25034

theorem unmarked_context_12_77603_633199 : frontier 9 ⟨633199, by decide⟩
    (prefixCache 12 77603) (prefixPartial 12 77603) = false := by
  decide +kernel

theorem node_context_12_77603_633199 : EJMOriginalGlobalDAGData.nodes 9 ⟨633199, by decide⟩ =
    .split (coordinate 12) (![⟨633136, by decide⟩,⟨633169, by decide⟩,⟨633192, by decide⟩,⟨633198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77603_633199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77603 ⟨633199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77603
    ⟨633199, by decide⟩ (by decide) (![⟨633136, by decide⟩,⟨633169, by decide⟩,⟨633192, by decide⟩,⟨633198, by decide⟩]) unmarked_context_12_77603_633199 node_context_12_77603_633199
  intro a
  fin_cases a
  · exact context_13_310412_633136
  · exact context_13_310413_633169
  · exact context_13_310414_633192
  · exact context_13_310415_633198

theorem unmarked_context_11_19400_633200 : frontier 10 ⟨633200, by decide⟩
    (prefixCache 11 19400) (prefixPartial 11 19400) = false := by
  decide +kernel

theorem node_context_11_19400_633200 : EJMOriginalGlobalDAGData.nodes 10 ⟨633200, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨633025, by decide⟩,⟨633115, by decide⟩,⟨633199, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19400_633200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19400 ⟨633200, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19400
    ⟨633200, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨633025, by decide⟩,⟨633115, by decide⟩,⟨633199, by decide⟩]) unmarked_context_11_19400_633200 node_context_11_19400_633200
  intro a
  fin_cases a
  · exact context_12_77600_435790
  · exact context_12_77601_633025
  · exact context_12_77602_633115
  · exact context_12_77603_633199

theorem selected_cut_25035 : selected 8 ⟨633233, by decide⟩
    (prefixPartial 13 310416) = some ⟨13, 2, 0, 633233, 310416, 457, 16384⟩ := by
  decide +kernel

theorem context_13_310416_633233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310416 ⟨633233, by decide⟩ :=
  accepted_of_selected 13 310416 ⟨633233, by decide⟩ ⟨13, 2, 0, 633233, 310416, 457, 16384⟩
    (by decide) selected_cut_25035

theorem selected_cut_25036 : selected 8 ⟨633342, by decide⟩
    (prefixPartial 13 310417) = some ⟨13, 2, 0, 633342, 310417, 3461, 16384⟩ := by
  decide +kernel

theorem context_13_310417_633342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310417 ⟨633342, by decide⟩ :=
  accepted_of_selected 13 310417 ⟨633342, by decide⟩ ⟨13, 2, 0, 633342, 310417, 3461, 16384⟩
    (by decide) selected_cut_25036

theorem selected_cut_25037 : selected 8 ⟨72292, by decide⟩
    (prefixPartial 13 310418) = some ⟨13, 1, 0, 72292, 310418, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310418_72292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310418 ⟨72292, by decide⟩ :=
  accepted_of_selected 13 310418 ⟨72292, by decide⟩ ⟨13, 1, 0, 72292, 310418, 1, 16384⟩
    (by decide) selected_cut_25037

theorem selected_cut_25038 : selected 8 ⟨633363, by decide⟩
    (prefixPartial 13 310419) = some ⟨13, 2, 0, 633363, 310419, 621, 16384⟩ := by
  decide +kernel

theorem context_13_310419_633363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310419 ⟨633363, by decide⟩ :=
  accepted_of_selected 13 310419 ⟨633363, by decide⟩ ⟨13, 2, 0, 633363, 310419, 621, 16384⟩
    (by decide) selected_cut_25038

theorem unmarked_context_12_77604_633364 : frontier 9 ⟨633364, by decide⟩
    (prefixCache 12 77604) (prefixPartial 12 77604) = false := by
  decide +kernel

theorem node_context_12_77604_633364 : EJMOriginalGlobalDAGData.nodes 9 ⟨633364, by decide⟩ =
    .split (coordinate 12) (![⟨633233, by decide⟩,⟨633342, by decide⟩,⟨72292, by decide⟩,⟨633363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77604_633364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77604 ⟨633364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77604
    ⟨633364, by decide⟩ (by decide) (![⟨633233, by decide⟩,⟨633342, by decide⟩,⟨72292, by decide⟩,⟨633363, by decide⟩]) unmarked_context_12_77604_633364 node_context_12_77604_633364
  intro a
  fin_cases a
  · exact context_13_310416_633233
  · exact context_13_310417_633342
  · exact context_13_310418_72292
  · exact context_13_310419_633363

theorem selected_cut_25039 : selected 8 ⟨633384, by decide⟩
    (prefixPartial 13 310420) = some ⟨13, 2, 0, 633384, 310420, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_310420_633384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310420 ⟨633384, by decide⟩ :=
  accepted_of_selected 13 310420 ⟨633384, by decide⟩ ⟨13, 2, 0, 633384, 310420, 1025, 16384⟩
    (by decide) selected_cut_25039

theorem selected_cut_25040 : selected 8 ⟨633417, by decide⟩
    (prefixPartial 13 310421) = some ⟨13, 2, 0, 633417, 310421, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_310421_633417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310421 ⟨633417, by decide⟩ :=
  accepted_of_selected 13 310421 ⟨633417, by decide⟩ ⟨13, 2, 0, 633417, 310421, 2333, 16384⟩
    (by decide) selected_cut_25040

theorem selected_cut_25041 : selected 8 ⟨633447, by decide⟩
    (prefixPartial 13 310422) = some ⟨13, 2, 0, 633447, 310422, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_310422_633447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310422 ⟨633447, by decide⟩ :=
  accepted_of_selected 13 310422 ⟨633447, by decide⟩ ⟨13, 2, 0, 633447, 310422, 1873, 16384⟩
    (by decide) selected_cut_25041

theorem selected_cut_25042 : selected 8 ⟨633453, by decide⟩
    (prefixPartial 13 310423) = some ⟨13, 2, 0, 633453, 310423, 629, 16384⟩ := by
  decide +kernel

theorem context_13_310423_633453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310423 ⟨633453, by decide⟩ :=
  accepted_of_selected 13 310423 ⟨633453, by decide⟩ ⟨13, 2, 0, 633453, 310423, 629, 16384⟩
    (by decide) selected_cut_25042

theorem unmarked_context_12_77605_633454 : frontier 9 ⟨633454, by decide⟩
    (prefixCache 12 77605) (prefixPartial 12 77605) = false := by
  decide +kernel

theorem node_context_12_77605_633454 : EJMOriginalGlobalDAGData.nodes 9 ⟨633454, by decide⟩ =
    .split (coordinate 12) (![⟨633384, by decide⟩,⟨633417, by decide⟩,⟨633447, by decide⟩,⟨633453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77605_633454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77605 ⟨633454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77605
    ⟨633454, by decide⟩ (by decide) (![⟨633384, by decide⟩,⟨633417, by decide⟩,⟨633447, by decide⟩,⟨633453, by decide⟩]) unmarked_context_12_77605_633454 node_context_12_77605_633454
  intro a
  fin_cases a
  · exact context_13_310420_633384
  · exact context_13_310421_633417
  · exact context_13_310422_633447
  · exact context_13_310423_633453

theorem selected_cut_25043 : selected 8 ⟨633476, by decide⟩
    (prefixPartial 13 310424) = some ⟨13, 2, 0, 633476, 310424, 953, 16384⟩ := by
  decide +kernel

theorem context_13_310424_633476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310424 ⟨633476, by decide⟩ :=
  accepted_of_selected 13 310424 ⟨633476, by decide⟩ ⟨13, 2, 0, 633476, 310424, 953, 16384⟩
    (by decide) selected_cut_25043

theorem selected_cut_25044 : selected 8 ⟨633508, by decide⟩
    (prefixPartial 13 310425) = some ⟨13, 2, 0, 633508, 310425, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_310425_633508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310425 ⟨633508, by decide⟩ :=
  accepted_of_selected 13 310425 ⟨633508, by decide⟩ ⟨13, 2, 0, 633508, 310425, 2165, 16384⟩
    (by decide) selected_cut_25044

theorem selected_cut_25045 : selected 8 ⟨633533, by decide⟩
    (prefixPartial 13 310426) = some ⟨13, 2, 0, 633533, 310426, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_310426_633533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310426 ⟨633533, by decide⟩ :=
  accepted_of_selected 13 310426 ⟨633533, by decide⟩ ⟨13, 2, 0, 633533, 310426, 1617, 16384⟩
    (by decide) selected_cut_25045

theorem selected_cut_25046 : selected 8 ⟨633540, by decide⟩
    (prefixPartial 13 310427) = some ⟨13, 2, 0, 633540, 310427, 769, 16384⟩ := by
  decide +kernel

theorem context_13_310427_633540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310427 ⟨633540, by decide⟩ :=
  accepted_of_selected 13 310427 ⟨633540, by decide⟩ ⟨13, 2, 0, 633540, 310427, 769, 16384⟩
    (by decide) selected_cut_25046

theorem unmarked_context_12_77606_633541 : frontier 9 ⟨633541, by decide⟩
    (prefixCache 12 77606) (prefixPartial 12 77606) = false := by
  decide +kernel

theorem node_context_12_77606_633541 : EJMOriginalGlobalDAGData.nodes 9 ⟨633541, by decide⟩ =
    .split (coordinate 12) (![⟨633476, by decide⟩,⟨633508, by decide⟩,⟨633533, by decide⟩,⟨633540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77606_633541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77606 ⟨633541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77606
    ⟨633541, by decide⟩ (by decide) (![⟨633476, by decide⟩,⟨633508, by decide⟩,⟨633533, by decide⟩,⟨633540, by decide⟩]) unmarked_context_12_77606_633541 node_context_12_77606_633541
  intro a
  fin_cases a
  · exact context_13_310424_633476
  · exact context_13_310425_633508
  · exact context_13_310426_633533
  · exact context_13_310427_633540

theorem selected_cut_25047 : selected 8 ⟨633556, by decide⟩
    (prefixPartial 13 310428) = some ⟨13, 2, 0, 633556, 310428, 929, 16384⟩ := by
  decide +kernel

theorem context_13_310428_633556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310428 ⟨633556, by decide⟩ :=
  accepted_of_selected 13 310428 ⟨633556, by decide⟩ ⟨13, 2, 0, 633556, 310428, 929, 16384⟩
    (by decide) selected_cut_25047

theorem selected_cut_25048 : selected 8 ⟨633590, by decide⟩
    (prefixPartial 13 310429) = some ⟨13, 2, 0, 633590, 310429, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_310429_633590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310429 ⟨633590, by decide⟩ :=
  accepted_of_selected 13 310429 ⟨633590, by decide⟩ ⟨13, 2, 0, 633590, 310429, 2321, 16384⟩
    (by decide) selected_cut_25048

theorem selected_cut_25049 : selected 8 ⟨633613, by decide⟩
    (prefixPartial 13 310430) = some ⟨13, 2, 0, 633613, 310430, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_310430_633613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310430 ⟨633613, by decide⟩ :=
  accepted_of_selected 13 310430 ⟨633613, by decide⟩ ⟨13, 2, 0, 633613, 310430, 1897, 16384⟩
    (by decide) selected_cut_25049

theorem selected_cut_25050 : selected 8 ⟨633622, by decide⟩
    (prefixPartial 13 310431) = some ⟨13, 2, 0, 633622, 310431, 793, 16384⟩ := by
  decide +kernel

theorem context_13_310431_633622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310431 ⟨633622, by decide⟩ :=
  accepted_of_selected 13 310431 ⟨633622, by decide⟩ ⟨13, 2, 0, 633622, 310431, 793, 16384⟩
    (by decide) selected_cut_25050

theorem unmarked_context_12_77607_633623 : frontier 9 ⟨633623, by decide⟩
    (prefixCache 12 77607) (prefixPartial 12 77607) = false := by
  decide +kernel

theorem node_context_12_77607_633623 : EJMOriginalGlobalDAGData.nodes 9 ⟨633623, by decide⟩ =
    .split (coordinate 12) (![⟨633556, by decide⟩,⟨633590, by decide⟩,⟨633613, by decide⟩,⟨633622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77607_633623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77607 ⟨633623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77607
    ⟨633623, by decide⟩ (by decide) (![⟨633556, by decide⟩,⟨633590, by decide⟩,⟨633613, by decide⟩,⟨633622, by decide⟩]) unmarked_context_12_77607_633623 node_context_12_77607_633623
  intro a
  fin_cases a
  · exact context_13_310428_633556
  · exact context_13_310429_633590
  · exact context_13_310430_633613
  · exact context_13_310431_633622

theorem unmarked_context_11_19401_633624 : frontier 10 ⟨633624, by decide⟩
    (prefixCache 11 19401) (prefixPartial 11 19401) = false := by
  decide +kernel

theorem node_context_11_19401_633624 : EJMOriginalGlobalDAGData.nodes 10 ⟨633624, by decide⟩ =
    .split (coordinate 11) (![⟨633364, by decide⟩,⟨633454, by decide⟩,⟨633541, by decide⟩,⟨633623, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19401_633624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19401 ⟨633624, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19401
    ⟨633624, by decide⟩ (by decide) (![⟨633364, by decide⟩,⟨633454, by decide⟩,⟨633541, by decide⟩,⟨633623, by decide⟩]) unmarked_context_11_19401_633624 node_context_11_19401_633624
  intro a
  fin_cases a
  · exact context_12_77604_633364
  · exact context_12_77605_633454
  · exact context_12_77606_633541
  · exact context_12_77607_633623

theorem selected_cut_25051 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 77608) = some ⟨12, 1, 0, 435790, 77608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77608_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77608 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 77608 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 77608, 1, 65536⟩
    (by decide) selected_cut_25051

theorem selected_cut_25052 : selected 8 ⟨633642, by decide⟩
    (prefixPartial 13 310436) = some ⟨13, 2, 0, 633642, 310436, 889, 16384⟩ := by
  decide +kernel

theorem context_13_310436_633642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310436 ⟨633642, by decide⟩ :=
  accepted_of_selected 13 310436 ⟨633642, by decide⟩ ⟨13, 2, 0, 633642, 310436, 889, 16384⟩
    (by decide) selected_cut_25052

theorem selected_cut_25053 : selected 8 ⟨633690, by decide⟩
    (prefixPartial 13 310437) = some ⟨13, 2, 0, 633690, 310437, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_310437_633690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310437 ⟨633690, by decide⟩ :=
  accepted_of_selected 13 310437 ⟨633690, by decide⟩ ⟨13, 2, 0, 633690, 310437, 2461, 16384⟩
    (by decide) selected_cut_25053

theorem selected_cut_25054 : selected 8 ⟨633727, by decide⟩
    (prefixPartial 13 310438) = some ⟨13, 2, 0, 633727, 310438, 2065, 16384⟩ := by
  decide +kernel

theorem context_13_310438_633727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310438 ⟨633727, by decide⟩ :=
  accepted_of_selected 13 310438 ⟨633727, by decide⟩ ⟨13, 2, 0, 633727, 310438, 2065, 16384⟩
    (by decide) selected_cut_25054

theorem selected_cut_25055 : selected 8 ⟨633737, by decide⟩
    (prefixPartial 13 310439) = some ⟨13, 2, 0, 633737, 310439, 729, 16384⟩ := by
  decide +kernel

theorem context_13_310439_633737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310439 ⟨633737, by decide⟩ :=
  accepted_of_selected 13 310439 ⟨633737, by decide⟩ ⟨13, 2, 0, 633737, 310439, 729, 16384⟩
    (by decide) selected_cut_25055

theorem unmarked_context_12_77609_633738 : frontier 9 ⟨633738, by decide⟩
    (prefixCache 12 77609) (prefixPartial 12 77609) = false := by
  decide +kernel

theorem node_context_12_77609_633738 : EJMOriginalGlobalDAGData.nodes 9 ⟨633738, by decide⟩ =
    .split (coordinate 12) (![⟨633642, by decide⟩,⟨633690, by decide⟩,⟨633727, by decide⟩,⟨633737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77609_633738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77609 ⟨633738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77609
    ⟨633738, by decide⟩ (by decide) (![⟨633642, by decide⟩,⟨633690, by decide⟩,⟨633727, by decide⟩,⟨633737, by decide⟩]) unmarked_context_12_77609_633738 node_context_12_77609_633738
  intro a
  fin_cases a
  · exact context_13_310436_633642
  · exact context_13_310437_633690
  · exact context_13_310438_633727
  · exact context_13_310439_633737

theorem selected_cut_25056 : selected 8 ⟨633753, by decide⟩
    (prefixPartial 13 310440) = some ⟨13, 2, 0, 633753, 310440, 621, 16384⟩ := by
  decide +kernel

theorem context_13_310440_633753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310440 ⟨633753, by decide⟩ :=
  accepted_of_selected 13 310440 ⟨633753, by decide⟩ ⟨13, 2, 0, 633753, 310440, 621, 16384⟩
    (by decide) selected_cut_25056

theorem selected_cut_25057 : selected 8 ⟨633793, by decide⟩
    (prefixPartial 13 310441) = some ⟨13, 2, 0, 633793, 310441, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_310441_633793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310441 ⟨633793, by decide⟩ :=
  accepted_of_selected 13 310441 ⟨633793, by decide⟩ ⟨13, 2, 0, 633793, 310441, 2285, 16384⟩
    (by decide) selected_cut_25057

theorem selected_cut_25058 : selected 8 ⟨633818, by decide⟩
    (prefixPartial 13 310442) = some ⟨13, 2, 0, 633818, 310442, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_310442_633818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310442 ⟨633818, by decide⟩ :=
  accepted_of_selected 13 310442 ⟨633818, by decide⟩ ⟨13, 2, 0, 633818, 310442, 1665, 16384⟩
    (by decide) selected_cut_25058

theorem selected_cut_25059 : selected 8 ⟨633824, by decide⟩
    (prefixPartial 13 310443) = some ⟨13, 2, 0, 633824, 310443, 749, 16384⟩ := by
  decide +kernel

theorem context_13_310443_633824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310443 ⟨633824, by decide⟩ :=
  accepted_of_selected 13 310443 ⟨633824, by decide⟩ ⟨13, 2, 0, 633824, 310443, 749, 16384⟩
    (by decide) selected_cut_25059

theorem unmarked_context_12_77610_633825 : frontier 9 ⟨633825, by decide⟩
    (prefixCache 12 77610) (prefixPartial 12 77610) = false := by
  decide +kernel

theorem node_context_12_77610_633825 : EJMOriginalGlobalDAGData.nodes 9 ⟨633825, by decide⟩ =
    .split (coordinate 12) (![⟨633753, by decide⟩,⟨633793, by decide⟩,⟨633818, by decide⟩,⟨633824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77610_633825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77610 ⟨633825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77610
    ⟨633825, by decide⟩ (by decide) (![⟨633753, by decide⟩,⟨633793, by decide⟩,⟨633818, by decide⟩,⟨633824, by decide⟩]) unmarked_context_12_77610_633825 node_context_12_77610_633825
  intro a
  fin_cases a
  · exact context_13_310440_633753
  · exact context_13_310441_633793
  · exact context_13_310442_633818
  · exact context_13_310443_633824

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
