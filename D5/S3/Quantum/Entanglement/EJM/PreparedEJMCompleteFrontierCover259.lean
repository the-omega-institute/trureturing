/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover258
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_19356_628205 : frontier 10 ⟨628205, by decide⟩
    (prefixCache 11 19356) (prefixPartial 11 19356) = false := by
  decide +kernel

theorem node_context_11_19356_628205 : EJMOriginalGlobalDAGData.nodes 10 ⟨628205, by decide⟩ =
    .split (coordinate 11) (![⟨628086, by decide⟩,⟨628123, by decide⟩,⟨628164, by decide⟩,⟨628204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19356_628205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19356 ⟨628205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19356
    ⟨628205, by decide⟩ (by decide) (![⟨628086, by decide⟩,⟨628123, by decide⟩,⟨628164, by decide⟩,⟨628204, by decide⟩]) unmarked_context_11_19356_628205 node_context_11_19356_628205
  intro a
  fin_cases a
  · exact context_12_77424_628086
  · exact context_12_77425_628123
  · exact context_12_77426_628164
  · exact context_12_77427_628204

theorem selected_cut_24868 : selected 9 ⟨628241, by decide⟩
    (prefixPartial 12 77428) = some ⟨12, 2, 0, 628241, 77428, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_77428_628241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77428 ⟨628241, by decide⟩ :=
  accepted_of_selected 12 77428 ⟨628241, by decide⟩ ⟨12, 2, 0, 628241, 77428, 2653, 65536⟩
    (by decide) selected_cut_24868

theorem selected_cut_24869 : selected 9 ⟨628275, by decide⟩
    (prefixPartial 12 77429) = some ⟨12, 2, 0, 628275, 77429, 2849, 65536⟩ := by
  decide +kernel

theorem context_12_77429_628275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77429 ⟨628275, by decide⟩ :=
  accepted_of_selected 12 77429 ⟨628275, by decide⟩ ⟨12, 2, 0, 628275, 77429, 2849, 65536⟩
    (by decide) selected_cut_24869

theorem selected_cut_24870 : selected 9 ⟨628316, by decide⟩
    (prefixPartial 12 77430) = some ⟨12, 2, 0, 628316, 77430, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_77430_628316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77430 ⟨628316, by decide⟩ :=
  accepted_of_selected 12 77430 ⟨628316, by decide⟩ ⟨12, 2, 0, 628316, 77430, 2933, 65536⟩
    (by decide) selected_cut_24870

theorem selected_cut_24871 : selected 9 ⟨628359, by decide⟩
    (prefixPartial 12 77431) = some ⟨12, 2, 0, 628359, 77431, 3145, 65536⟩ := by
  decide +kernel

theorem context_12_77431_628359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77431 ⟨628359, by decide⟩ :=
  accepted_of_selected 12 77431 ⟨628359, by decide⟩ ⟨12, 2, 0, 628359, 77431, 3145, 65536⟩
    (by decide) selected_cut_24871

theorem unmarked_context_11_19357_628360 : frontier 10 ⟨628360, by decide⟩
    (prefixCache 11 19357) (prefixPartial 11 19357) = false := by
  decide +kernel

theorem node_context_11_19357_628360 : EJMOriginalGlobalDAGData.nodes 10 ⟨628360, by decide⟩ =
    .split (coordinate 11) (![⟨628241, by decide⟩,⟨628275, by decide⟩,⟨628316, by decide⟩,⟨628359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19357_628360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19357 ⟨628360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19357
    ⟨628360, by decide⟩ (by decide) (![⟨628241, by decide⟩,⟨628275, by decide⟩,⟨628316, by decide⟩,⟨628359, by decide⟩]) unmarked_context_11_19357_628360 node_context_11_19357_628360
  intro a
  fin_cases a
  · exact context_12_77428_628241
  · exact context_12_77429_628275
  · exact context_12_77430_628316
  · exact context_12_77431_628359

theorem selected_cut_24872 : selected 9 ⟨628393, by decide⟩
    (prefixPartial 12 77432) = some ⟨12, 2, 0, 628393, 77432, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_77432_628393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77432 ⟨628393, by decide⟩ :=
  accepted_of_selected 12 77432 ⟨628393, by decide⟩ ⟨12, 2, 0, 628393, 77432, 2245, 65536⟩
    (by decide) selected_cut_24872

theorem selected_cut_24873 : selected 9 ⟨628426, by decide⟩
    (prefixPartial 12 77433) = some ⟨12, 2, 0, 628426, 77433, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_77433_628426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77433 ⟨628426, by decide⟩ :=
  accepted_of_selected 12 77433 ⟨628426, by decide⟩ ⟨12, 2, 0, 628426, 77433, 2597, 65536⟩
    (by decide) selected_cut_24873

theorem selected_cut_24874 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 309736) = some ⟨13, 1, 0, 3444, 309736, 1, 16384⟩ := by
  decide +kernel

theorem context_13_309736_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309736 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 309736 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 309736, 1, 16384⟩
    (by decide) selected_cut_24874

theorem selected_cut_24875 : selected 8 ⟨628436, by decide⟩
    (prefixPartial 13 309737) = some ⟨13, 2, 0, 628436, 309737, 361, 16384⟩ := by
  decide +kernel

theorem context_13_309737_628436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309737 ⟨628436, by decide⟩ :=
  accepted_of_selected 13 309737 ⟨628436, by decide⟩ ⟨13, 2, 0, 628436, 309737, 361, 16384⟩
    (by decide) selected_cut_24875

theorem selected_cut_24876 : selected 8 ⟨628479, by decide⟩
    (prefixPartial 13 309738) = some ⟨13, 2, 0, 628479, 309738, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_309738_628479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309738 ⟨628479, by decide⟩ :=
  accepted_of_selected 13 309738 ⟨628479, by decide⟩ ⟨13, 2, 0, 628479, 309738, 2569, 16384⟩
    (by decide) selected_cut_24876

theorem selected_cut_24877 : selected 8 ⟨628494, by decide⟩
    (prefixPartial 13 309739) = some ⟨13, 2, 0, 628494, 309739, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_309739_628494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 309739 ⟨628494, by decide⟩ :=
  accepted_of_selected 13 309739 ⟨628494, by decide⟩ ⟨13, 2, 0, 628494, 309739, 1173, 16384⟩
    (by decide) selected_cut_24877

theorem unmarked_context_12_77434_628495 : frontier 9 ⟨628495, by decide⟩
    (prefixCache 12 77434) (prefixPartial 12 77434) = false := by
  decide +kernel

theorem node_context_12_77434_628495 : EJMOriginalGlobalDAGData.nodes 9 ⟨628495, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨628436, by decide⟩,⟨628479, by decide⟩,⟨628494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77434_628495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77434 ⟨628495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77434
    ⟨628495, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨628436, by decide⟩,⟨628479, by decide⟩,⟨628494, by decide⟩]) unmarked_context_12_77434_628495 node_context_12_77434_628495
  intro a
  fin_cases a
  · exact context_13_309736_3444
  · exact context_13_309737_628436
  · exact context_13_309738_628479
  · exact context_13_309739_628494

theorem selected_cut_24878 : selected 9 ⟨628530, by decide⟩
    (prefixPartial 12 77435) = some ⟨12, 2, 0, 628530, 77435, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_77435_628530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77435 ⟨628530, by decide⟩ :=
  accepted_of_selected 12 77435 ⟨628530, by decide⟩ ⟨12, 2, 0, 628530, 77435, 2433, 65536⟩
    (by decide) selected_cut_24878

theorem unmarked_context_11_19358_628531 : frontier 10 ⟨628531, by decide⟩
    (prefixCache 11 19358) (prefixPartial 11 19358) = false := by
  decide +kernel

theorem node_context_11_19358_628531 : EJMOriginalGlobalDAGData.nodes 10 ⟨628531, by decide⟩ =
    .split (coordinate 11) (![⟨628393, by decide⟩,⟨628426, by decide⟩,⟨628495, by decide⟩,⟨628530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19358_628531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19358 ⟨628531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19358
    ⟨628531, by decide⟩ (by decide) (![⟨628393, by decide⟩,⟨628426, by decide⟩,⟨628495, by decide⟩,⟨628530, by decide⟩]) unmarked_context_11_19358_628531 node_context_11_19358_628531
  intro a
  fin_cases a
  · exact context_12_77432_628393
  · exact context_12_77433_628426
  · exact context_12_77434_628495
  · exact context_12_77435_628530

theorem selected_cut_24879 : selected 9 ⟨628584, by decide⟩
    (prefixPartial 12 77436) = some ⟨12, 2, 0, 628584, 77436, 3085, 65536⟩ := by
  decide +kernel

theorem context_12_77436_628584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77436 ⟨628584, by decide⟩ :=
  accepted_of_selected 12 77436 ⟨628584, by decide⟩ ⟨12, 2, 0, 628584, 77436, 3085, 65536⟩
    (by decide) selected_cut_24879

theorem selected_cut_24880 : selected 9 ⟨628634, by decide⟩
    (prefixPartial 12 77437) = some ⟨12, 2, 0, 628634, 77437, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_77437_628634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77437 ⟨628634, by decide⟩ :=
  accepted_of_selected 12 77437 ⟨628634, by decide⟩ ⟨12, 2, 0, 628634, 77437, 3333, 65536⟩
    (by decide) selected_cut_24880

theorem selected_cut_24881 : selected 9 ⟨628684, by decide⟩
    (prefixPartial 12 77438) = some ⟨12, 2, 0, 628684, 77438, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_77438_628684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77438 ⟨628684, by decide⟩ :=
  accepted_of_selected 12 77438 ⟨628684, by decide⟩ ⟨12, 2, 0, 628684, 77438, 3349, 65536⟩
    (by decide) selected_cut_24881

theorem selected_cut_24882 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 77439) = some ⟨12, 1, 0, 607719, 77439, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77439_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77439 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 77439 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 77439, 1, 65536⟩
    (by decide) selected_cut_24882

theorem unmarked_context_11_19359_628685 : frontier 10 ⟨628685, by decide⟩
    (prefixCache 11 19359) (prefixPartial 11 19359) = false := by
  decide +kernel

theorem node_context_11_19359_628685 : EJMOriginalGlobalDAGData.nodes 10 ⟨628685, by decide⟩ =
    .split (coordinate 11) (![⟨628584, by decide⟩,⟨628634, by decide⟩,⟨628684, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19359_628685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19359 ⟨628685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19359
    ⟨628685, by decide⟩ (by decide) (![⟨628584, by decide⟩,⟨628634, by decide⟩,⟨628684, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_19359_628685 node_context_11_19359_628685
  intro a
  fin_cases a
  · exact context_12_77436_628584
  · exact context_12_77437_628634
  · exact context_12_77438_628684
  · exact context_12_77439_607719

theorem unmarked_context_10_4839_628686 : frontier 11 ⟨628686, by decide⟩
    (prefixCache 10 4839) (prefixPartial 10 4839) = false := by
  decide +kernel

theorem node_context_10_4839_628686 : EJMOriginalGlobalDAGData.nodes 11 ⟨628686, by decide⟩ =
    .split (coordinate 10) (![⟨628205, by decide⟩,⟨628360, by decide⟩,⟨628531, by decide⟩,⟨628685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4839_628686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4839 ⟨628686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4839
    ⟨628686, by decide⟩ (by decide) (![⟨628205, by decide⟩,⟨628360, by decide⟩,⟨628531, by decide⟩,⟨628685, by decide⟩]) unmarked_context_10_4839_628686 node_context_10_4839_628686
  intro a
  fin_cases a
  · exact context_11_19356_628205
  · exact context_11_19357_628360
  · exact context_11_19358_628531
  · exact context_11_19359_628685

theorem unmarked_context_9_1209_628687 : frontier 12 ⟨628687, by decide⟩
    (prefixCache 9 1209) (prefixPartial 9 1209) = false := by
  decide +kernel

theorem node_context_9_1209_628687 : EJMOriginalGlobalDAGData.nodes 12 ⟨628687, by decide⟩ =
    .split (coordinate 9) (![⟨626280, by decide⟩,⟨627283, by decide⟩,⟨628042, by decide⟩,⟨628686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1209_628687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1209 ⟨628687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1209
    ⟨628687, by decide⟩ (by decide) (![⟨626280, by decide⟩,⟨627283, by decide⟩,⟨628042, by decide⟩,⟨628686, by decide⟩]) unmarked_context_9_1209_628687 node_context_9_1209_628687
  intro a
  fin_cases a
  · exact context_10_4836_626280
  · exact context_10_4837_627283
  · exact context_10_4838_628042
  · exact context_10_4839_628686

theorem selected_cut_24883 : selected 9 ⟨628715, by decide⟩
    (prefixPartial 12 77440) = some ⟨12, 2, 0, 628715, 77440, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_77440_628715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77440 ⟨628715, by decide⟩ :=
  accepted_of_selected 12 77440 ⟨628715, by decide⟩ ⟨12, 2, 0, 628715, 77440, 1957, 65536⟩
    (by decide) selected_cut_24883

theorem selected_cut_24884 : selected 9 ⟨628747, by decide⟩
    (prefixPartial 12 77441) = some ⟨12, 2, 0, 628747, 77441, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_77441_628747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77441 ⟨628747, by decide⟩ :=
  accepted_of_selected 12 77441 ⟨628747, by decide⟩ ⟨12, 2, 0, 628747, 77441, 2345, 65536⟩
    (by decide) selected_cut_24884

theorem selected_cut_24885 : selected 9 ⟨628779, by decide⟩
    (prefixPartial 12 77442) = some ⟨12, 2, 0, 628779, 77442, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_77442_628779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77442 ⟨628779, by decide⟩ :=
  accepted_of_selected 12 77442 ⟨628779, by decide⟩ ⟨12, 2, 0, 628779, 77442, 2141, 65536⟩
    (by decide) selected_cut_24885

theorem selected_cut_24886 : selected 9 ⟨628811, by decide⟩
    (prefixPartial 12 77443) = some ⟨12, 2, 0, 628811, 77443, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_77443_628811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77443 ⟨628811, by decide⟩ :=
  accepted_of_selected 12 77443 ⟨628811, by decide⟩ ⟨12, 2, 0, 628811, 77443, 2437, 65536⟩
    (by decide) selected_cut_24886

theorem unmarked_context_11_19360_628812 : frontier 10 ⟨628812, by decide⟩
    (prefixCache 11 19360) (prefixPartial 11 19360) = false := by
  decide +kernel

theorem node_context_11_19360_628812 : EJMOriginalGlobalDAGData.nodes 10 ⟨628812, by decide⟩ =
    .split (coordinate 11) (![⟨628715, by decide⟩,⟨628747, by decide⟩,⟨628779, by decide⟩,⟨628811, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19360_628812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19360 ⟨628812, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19360
    ⟨628812, by decide⟩ (by decide) (![⟨628715, by decide⟩,⟨628747, by decide⟩,⟨628779, by decide⟩,⟨628811, by decide⟩]) unmarked_context_11_19360_628812 node_context_11_19360_628812
  intro a
  fin_cases a
  · exact context_12_77440_628715
  · exact context_12_77441_628747
  · exact context_12_77442_628779
  · exact context_12_77443_628811

theorem selected_cut_24887 : selected 9 ⟨628836, by decide⟩
    (prefixPartial 12 77444) = some ⟨12, 2, 0, 628836, 77444, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_77444_628836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77444 ⟨628836, by decide⟩ :=
  accepted_of_selected 12 77444 ⟨628836, by decide⟩ ⟨12, 2, 0, 628836, 77444, 2025, 65536⟩
    (by decide) selected_cut_24887

theorem selected_cut_24888 : selected 9 ⟨628865, by decide⟩
    (prefixPartial 12 77445) = some ⟨12, 2, 0, 628865, 77445, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_77445_628865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77445 ⟨628865, by decide⟩ :=
  accepted_of_selected 12 77445 ⟨628865, by decide⟩ ⟨12, 2, 0, 628865, 77445, 2229, 65536⟩
    (by decide) selected_cut_24888

theorem selected_cut_24889 : selected 9 ⟨628892, by decide⟩
    (prefixPartial 12 77446) = some ⟨12, 2, 0, 628892, 77446, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_77446_628892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77446 ⟨628892, by decide⟩ :=
  accepted_of_selected 12 77446 ⟨628892, by decide⟩ ⟨12, 2, 0, 628892, 77446, 2141, 65536⟩
    (by decide) selected_cut_24889

theorem selected_cut_24890 : selected 9 ⟨628930, by decide⟩
    (prefixPartial 12 77447) = some ⟨12, 2, 0, 628930, 77447, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_77447_628930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77447 ⟨628930, by decide⟩ :=
  accepted_of_selected 12 77447 ⟨628930, by decide⟩ ⟨12, 2, 0, 628930, 77447, 2473, 65536⟩
    (by decide) selected_cut_24890

theorem unmarked_context_11_19361_628931 : frontier 10 ⟨628931, by decide⟩
    (prefixCache 11 19361) (prefixPartial 11 19361) = false := by
  decide +kernel

theorem node_context_11_19361_628931 : EJMOriginalGlobalDAGData.nodes 10 ⟨628931, by decide⟩ =
    .split (coordinate 11) (![⟨628836, by decide⟩,⟨628865, by decide⟩,⟨628892, by decide⟩,⟨628930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19361_628931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19361 ⟨628931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19361
    ⟨628931, by decide⟩ (by decide) (![⟨628836, by decide⟩,⟨628865, by decide⟩,⟨628892, by decide⟩,⟨628930, by decide⟩]) unmarked_context_11_19361_628931 node_context_11_19361_628931
  intro a
  fin_cases a
  · exact context_12_77444_628836
  · exact context_12_77445_628865
  · exact context_12_77446_628892
  · exact context_12_77447_628930

theorem selected_cut_24891 : selected 9 ⟨628960, by decide⟩
    (prefixPartial 12 77448) = some ⟨12, 2, 0, 628960, 77448, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_77448_628960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77448 ⟨628960, by decide⟩ :=
  accepted_of_selected 12 77448 ⟨628960, by decide⟩ ⟨12, 2, 0, 628960, 77448, 2029, 65536⟩
    (by decide) selected_cut_24891

theorem selected_cut_24892 : selected 9 ⟨628994, by decide⟩
    (prefixPartial 12 77449) = some ⟨12, 2, 0, 628994, 77449, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_77449_628994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77449 ⟨628994, by decide⟩ :=
  accepted_of_selected 12 77449 ⟨628994, by decide⟩ ⟨12, 2, 0, 628994, 77449, 2393, 65536⟩
    (by decide) selected_cut_24892

theorem selected_cut_24893 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 77450) = some ⟨12, 1, 0, 448662, 77450, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77450_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77450 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 77450 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 77450, 1, 65536⟩
    (by decide) selected_cut_24893

theorem selected_cut_24894 : selected 9 ⟨629027, by decide⟩
    (prefixPartial 12 77451) = some ⟨12, 2, 0, 629027, 77451, 2329, 65536⟩ := by
  decide +kernel

theorem context_12_77451_629027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77451 ⟨629027, by decide⟩ :=
  accepted_of_selected 12 77451 ⟨629027, by decide⟩ ⟨12, 2, 0, 629027, 77451, 2329, 65536⟩
    (by decide) selected_cut_24894

theorem unmarked_context_11_19362_629028 : frontier 10 ⟨629028, by decide⟩
    (prefixCache 11 19362) (prefixPartial 11 19362) = false := by
  decide +kernel

theorem node_context_11_19362_629028 : EJMOriginalGlobalDAGData.nodes 10 ⟨629028, by decide⟩ =
    .split (coordinate 11) (![⟨628960, by decide⟩,⟨628994, by decide⟩,⟨448662, by decide⟩,⟨629027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19362_629028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19362 ⟨629028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19362
    ⟨629028, by decide⟩ (by decide) (![⟨628960, by decide⟩,⟨628994, by decide⟩,⟨448662, by decide⟩,⟨629027, by decide⟩]) unmarked_context_11_19362_629028 node_context_11_19362_629028
  intro a
  fin_cases a
  · exact context_12_77448_628960
  · exact context_12_77449_628994
  · exact context_12_77450_448662
  · exact context_12_77451_629027

theorem selected_cut_24895 : selected 9 ⟨629051, by decide⟩
    (prefixPartial 12 77452) = some ⟨12, 2, 0, 629051, 77452, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_77452_629051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77452 ⟨629051, by decide⟩ :=
  accepted_of_selected 12 77452 ⟨629051, by decide⟩ ⟨12, 2, 0, 629051, 77452, 1837, 65536⟩
    (by decide) selected_cut_24895

theorem selected_cut_24896 : selected 9 ⟨629074, by decide⟩
    (prefixPartial 12 77453) = some ⟨12, 2, 0, 629074, 77453, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_77453_629074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77453 ⟨629074, by decide⟩ :=
  accepted_of_selected 12 77453 ⟨629074, by decide⟩ ⟨12, 2, 0, 629074, 77453, 2097, 65536⟩
    (by decide) selected_cut_24896

theorem selected_cut_24897 : selected 9 ⟨629098, by decide⟩
    (prefixPartial 12 77454) = some ⟨12, 2, 0, 629098, 77454, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_77454_629098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77454 ⟨629098, by decide⟩ :=
  accepted_of_selected 12 77454 ⟨629098, by decide⟩ ⟨12, 2, 0, 629098, 77454, 2025, 65536⟩
    (by decide) selected_cut_24897

theorem selected_cut_24898 : selected 9 ⟨629130, by decide⟩
    (prefixPartial 12 77455) = some ⟨12, 2, 0, 629130, 77455, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_77455_629130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77455 ⟨629130, by decide⟩ :=
  accepted_of_selected 12 77455 ⟨629130, by decide⟩ ⟨12, 2, 0, 629130, 77455, 2261, 65536⟩
    (by decide) selected_cut_24898

theorem unmarked_context_11_19363_629131 : frontier 10 ⟨629131, by decide⟩
    (prefixCache 11 19363) (prefixPartial 11 19363) = false := by
  decide +kernel

theorem node_context_11_19363_629131 : EJMOriginalGlobalDAGData.nodes 10 ⟨629131, by decide⟩ =
    .split (coordinate 11) (![⟨629051, by decide⟩,⟨629074, by decide⟩,⟨629098, by decide⟩,⟨629130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19363_629131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19363 ⟨629131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19363
    ⟨629131, by decide⟩ (by decide) (![⟨629051, by decide⟩,⟨629074, by decide⟩,⟨629098, by decide⟩,⟨629130, by decide⟩]) unmarked_context_11_19363_629131 node_context_11_19363_629131
  intro a
  fin_cases a
  · exact context_12_77452_629051
  · exact context_12_77453_629074
  · exact context_12_77454_629098
  · exact context_12_77455_629130

theorem unmarked_context_10_4840_629132 : frontier 11 ⟨629132, by decide⟩
    (prefixCache 10 4840) (prefixPartial 10 4840) = false := by
  decide +kernel

theorem node_context_10_4840_629132 : EJMOriginalGlobalDAGData.nodes 11 ⟨629132, by decide⟩ =
    .split (coordinate 10) (![⟨628812, by decide⟩,⟨628931, by decide⟩,⟨629028, by decide⟩,⟨629131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4840_629132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4840 ⟨629132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4840
    ⟨629132, by decide⟩ (by decide) (![⟨628812, by decide⟩,⟨628931, by decide⟩,⟨629028, by decide⟩,⟨629131, by decide⟩]) unmarked_context_10_4840_629132 node_context_10_4840_629132
  intro a
  fin_cases a
  · exact context_11_19360_628812
  · exact context_11_19361_628931
  · exact context_11_19362_629028
  · exact context_11_19363_629131

theorem selected_cut_24899 : selected 9 ⟨629163, by decide⟩
    (prefixPartial 12 77456) = some ⟨12, 2, 0, 629163, 77456, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_77456_629163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77456 ⟨629163, by decide⟩ :=
  accepted_of_selected 12 77456 ⟨629163, by decide⟩ ⟨12, 2, 0, 629163, 77456, 2181, 65536⟩
    (by decide) selected_cut_24899

theorem selected_cut_24900 : selected 9 ⟨629205, by decide⟩
    (prefixPartial 12 77457) = some ⟨12, 2, 0, 629205, 77457, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_77457_629205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77457 ⟨629205, by decide⟩ :=
  accepted_of_selected 12 77457 ⟨629205, by decide⟩ ⟨12, 2, 0, 629205, 77457, 2585, 65536⟩
    (by decide) selected_cut_24900

theorem selected_cut_24901 : selected 9 ⟨629238, by decide⟩
    (prefixPartial 12 77458) = some ⟨12, 2, 0, 629238, 77458, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_77458_629238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77458 ⟨629238, by decide⟩ :=
  accepted_of_selected 12 77458 ⟨629238, by decide⟩ ⟨12, 2, 0, 629238, 77458, 2165, 65536⟩
    (by decide) selected_cut_24901

theorem selected_cut_24902 : selected 9 ⟨629279, by decide⟩
    (prefixPartial 12 77459) = some ⟨12, 2, 0, 629279, 77459, 2601, 65536⟩ := by
  decide +kernel

theorem context_12_77459_629279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77459 ⟨629279, by decide⟩ :=
  accepted_of_selected 12 77459 ⟨629279, by decide⟩ ⟨12, 2, 0, 629279, 77459, 2601, 65536⟩
    (by decide) selected_cut_24902

theorem unmarked_context_11_19364_629280 : frontier 10 ⟨629280, by decide⟩
    (prefixCache 11 19364) (prefixPartial 11 19364) = false := by
  decide +kernel

theorem node_context_11_19364_629280 : EJMOriginalGlobalDAGData.nodes 10 ⟨629280, by decide⟩ =
    .split (coordinate 11) (![⟨629163, by decide⟩,⟨629205, by decide⟩,⟨629238, by decide⟩,⟨629279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19364_629280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19364 ⟨629280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19364
    ⟨629280, by decide⟩ (by decide) (![⟨629163, by decide⟩,⟨629205, by decide⟩,⟨629238, by decide⟩,⟨629279, by decide⟩]) unmarked_context_11_19364_629280 node_context_11_19364_629280
  intro a
  fin_cases a
  · exact context_12_77456_629163
  · exact context_12_77457_629205
  · exact context_12_77458_629238
  · exact context_12_77459_629279

theorem selected_cut_24903 : selected 9 ⟨629308, by decide⟩
    (prefixPartial 12 77460) = some ⟨12, 2, 0, 629308, 77460, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_77460_629308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77460 ⟨629308, by decide⟩ :=
  accepted_of_selected 12 77460 ⟨629308, by decide⟩ ⟨12, 2, 0, 629308, 77460, 2213, 65536⟩
    (by decide) selected_cut_24903

theorem selected_cut_24904 : selected 9 ⟨629334, by decide⟩
    (prefixPartial 12 77461) = some ⟨12, 2, 0, 629334, 77461, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_77461_629334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77461 ⟨629334, by decide⟩ :=
  accepted_of_selected 12 77461 ⟨629334, by decide⟩ ⟨12, 2, 0, 629334, 77461, 2513, 65536⟩
    (by decide) selected_cut_24904

theorem selected_cut_24905 : selected 9 ⟨629360, by decide⟩
    (prefixPartial 12 77462) = some ⟨12, 2, 0, 629360, 77462, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_77462_629360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77462 ⟨629360, by decide⟩ :=
  accepted_of_selected 12 77462 ⟨629360, by decide⟩ ⟨12, 2, 0, 629360, 77462, 2209, 65536⟩
    (by decide) selected_cut_24905

theorem selected_cut_24906 : selected 9 ⟨629407, by decide⟩
    (prefixPartial 12 77463) = some ⟨12, 2, 0, 629407, 77463, 2637, 65536⟩ := by
  decide +kernel

theorem context_12_77463_629407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77463 ⟨629407, by decide⟩ :=
  accepted_of_selected 12 77463 ⟨629407, by decide⟩ ⟨12, 2, 0, 629407, 77463, 2637, 65536⟩
    (by decide) selected_cut_24906

theorem unmarked_context_11_19365_629408 : frontier 10 ⟨629408, by decide⟩
    (prefixCache 11 19365) (prefixPartial 11 19365) = false := by
  decide +kernel

theorem node_context_11_19365_629408 : EJMOriginalGlobalDAGData.nodes 10 ⟨629408, by decide⟩ =
    .split (coordinate 11) (![⟨629308, by decide⟩,⟨629334, by decide⟩,⟨629360, by decide⟩,⟨629407, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19365_629408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19365 ⟨629408, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19365
    ⟨629408, by decide⟩ (by decide) (![⟨629308, by decide⟩,⟨629334, by decide⟩,⟨629360, by decide⟩,⟨629407, by decide⟩]) unmarked_context_11_19365_629408 node_context_11_19365_629408
  intro a
  fin_cases a
  · exact context_12_77460_629308
  · exact context_12_77461_629334
  · exact context_12_77462_629360
  · exact context_12_77463_629407

theorem selected_cut_24907 : selected 9 ⟨629434, by decide⟩
    (prefixPartial 12 77464) = some ⟨12, 2, 0, 629434, 77464, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_77464_629434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77464 ⟨629434, by decide⟩ :=
  accepted_of_selected 12 77464 ⟨629434, by decide⟩ ⟨12, 2, 0, 629434, 77464, 2101, 65536⟩
    (by decide) selected_cut_24907

theorem selected_cut_24908 : selected 9 ⟨629472, by decide⟩
    (prefixPartial 12 77465) = some ⟨12, 2, 0, 629472, 77465, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_77465_629472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77465 ⟨629472, by decide⟩ :=
  accepted_of_selected 12 77465 ⟨629472, by decide⟩ ⟨12, 2, 0, 629472, 77465, 2545, 65536⟩
    (by decide) selected_cut_24908

theorem selected_cut_24909 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 77466) = some ⟨12, 1, 0, 448662, 77466, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77466_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77466 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 77466 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 77466, 1, 65536⟩
    (by decide) selected_cut_24909

theorem selected_cut_24910 : selected 9 ⟨629509, by decide⟩
    (prefixPartial 12 77467) = some ⟨12, 2, 0, 629509, 77467, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_77467_629509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77467 ⟨629509, by decide⟩ :=
  accepted_of_selected 12 77467 ⟨629509, by decide⟩ ⟨12, 2, 0, 629509, 77467, 2313, 65536⟩
    (by decide) selected_cut_24910

theorem unmarked_context_11_19366_629510 : frontier 10 ⟨629510, by decide⟩
    (prefixCache 11 19366) (prefixPartial 11 19366) = false := by
  decide +kernel

theorem node_context_11_19366_629510 : EJMOriginalGlobalDAGData.nodes 10 ⟨629510, by decide⟩ =
    .split (coordinate 11) (![⟨629434, by decide⟩,⟨629472, by decide⟩,⟨448662, by decide⟩,⟨629509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19366_629510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19366 ⟨629510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19366
    ⟨629510, by decide⟩ (by decide) (![⟨629434, by decide⟩,⟨629472, by decide⟩,⟨448662, by decide⟩,⟨629509, by decide⟩]) unmarked_context_11_19366_629510 node_context_11_19366_629510
  intro a
  fin_cases a
  · exact context_12_77464_629434
  · exact context_12_77465_629472
  · exact context_12_77466_448662
  · exact context_12_77467_629509

theorem selected_cut_24911 : selected 9 ⟨629532, by decide⟩
    (prefixPartial 12 77468) = some ⟨12, 2, 0, 629532, 77468, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_77468_629532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77468 ⟨629532, by decide⟩ :=
  accepted_of_selected 12 77468 ⟨629532, by decide⟩ ⟨12, 2, 0, 629532, 77468, 1941, 65536⟩
    (by decide) selected_cut_24911

theorem selected_cut_24912 : selected 9 ⟨629567, by decide⟩
    (prefixPartial 12 77469) = some ⟨12, 2, 0, 629567, 77469, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_77469_629567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77469 ⟨629567, by decide⟩ :=
  accepted_of_selected 12 77469 ⟨629567, by decide⟩ ⟨12, 2, 0, 629567, 77469, 2229, 65536⟩
    (by decide) selected_cut_24912

theorem selected_cut_24913 : selected 9 ⟨629595, by decide⟩
    (prefixPartial 12 77470) = some ⟨12, 2, 0, 629595, 77470, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_77470_629595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77470 ⟨629595, by decide⟩ :=
  accepted_of_selected 12 77470 ⟨629595, by decide⟩ ⟨12, 2, 0, 629595, 77470, 1981, 65536⟩
    (by decide) selected_cut_24913

theorem selected_cut_24914 : selected 9 ⟨629631, by decide⟩
    (prefixPartial 12 77471) = some ⟨12, 2, 0, 629631, 77471, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_77471_629631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77471 ⟨629631, by decide⟩ :=
  accepted_of_selected 12 77471 ⟨629631, by decide⟩ ⟨12, 2, 0, 629631, 77471, 2289, 65536⟩
    (by decide) selected_cut_24914

theorem unmarked_context_11_19367_629632 : frontier 10 ⟨629632, by decide⟩
    (prefixCache 11 19367) (prefixPartial 11 19367) = false := by
  decide +kernel

theorem node_context_11_19367_629632 : EJMOriginalGlobalDAGData.nodes 10 ⟨629632, by decide⟩ =
    .split (coordinate 11) (![⟨629532, by decide⟩,⟨629567, by decide⟩,⟨629595, by decide⟩,⟨629631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19367_629632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19367 ⟨629632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19367
    ⟨629632, by decide⟩ (by decide) (![⟨629532, by decide⟩,⟨629567, by decide⟩,⟨629595, by decide⟩,⟨629631, by decide⟩]) unmarked_context_11_19367_629632 node_context_11_19367_629632
  intro a
  fin_cases a
  · exact context_12_77468_629532
  · exact context_12_77469_629567
  · exact context_12_77470_629595
  · exact context_12_77471_629631

theorem unmarked_context_10_4841_629633 : frontier 11 ⟨629633, by decide⟩
    (prefixCache 10 4841) (prefixPartial 10 4841) = false := by
  decide +kernel

theorem node_context_10_4841_629633 : EJMOriginalGlobalDAGData.nodes 11 ⟨629633, by decide⟩ =
    .split (coordinate 10) (![⟨629280, by decide⟩,⟨629408, by decide⟩,⟨629510, by decide⟩,⟨629632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4841_629633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4841 ⟨629633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4841
    ⟨629633, by decide⟩ (by decide) (![⟨629280, by decide⟩,⟨629408, by decide⟩,⟨629510, by decide⟩,⟨629632, by decide⟩]) unmarked_context_10_4841_629633 node_context_10_4841_629633
  intro a
  fin_cases a
  · exact context_11_19364_629280
  · exact context_11_19365_629408
  · exact context_11_19366_629510
  · exact context_11_19367_629632

theorem selected_cut_24915 : selected 9 ⟨629656, by decide⟩
    (prefixPartial 12 77472) = some ⟨12, 2, 0, 629656, 77472, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_77472_629656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77472 ⟨629656, by decide⟩ :=
  accepted_of_selected 12 77472 ⟨629656, by decide⟩ ⟨12, 2, 0, 629656, 77472, 1485, 65536⟩
    (by decide) selected_cut_24915

theorem selected_cut_24916 : selected 9 ⟨629682, by decide⟩
    (prefixPartial 12 77473) = some ⟨12, 2, 0, 629682, 77473, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_77473_629682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77473 ⟨629682, by decide⟩ :=
  accepted_of_selected 12 77473 ⟨629682, by decide⟩ ⟨12, 2, 0, 629682, 77473, 1785, 65536⟩
    (by decide) selected_cut_24916

theorem selected_cut_24917 : selected 9 ⟨629702, by decide⟩
    (prefixPartial 12 77474) = some ⟨12, 2, 0, 629702, 77474, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_77474_629702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77474 ⟨629702, by decide⟩ :=
  accepted_of_selected 12 77474 ⟨629702, by decide⟩ ⟨12, 2, 0, 629702, 77474, 1485, 65536⟩
    (by decide) selected_cut_24917

theorem selected_cut_24918 : selected 9 ⟨629724, by decide⟩
    (prefixPartial 12 77475) = some ⟨12, 2, 0, 629724, 77475, 1889, 65536⟩ := by
  decide +kernel

theorem context_12_77475_629724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77475 ⟨629724, by decide⟩ :=
  accepted_of_selected 12 77475 ⟨629724, by decide⟩ ⟨12, 2, 0, 629724, 77475, 1889, 65536⟩
    (by decide) selected_cut_24918

theorem unmarked_context_11_19368_629725 : frontier 10 ⟨629725, by decide⟩
    (prefixCache 11 19368) (prefixPartial 11 19368) = false := by
  decide +kernel

theorem node_context_11_19368_629725 : EJMOriginalGlobalDAGData.nodes 10 ⟨629725, by decide⟩ =
    .split (coordinate 11) (![⟨629656, by decide⟩,⟨629682, by decide⟩,⟨629702, by decide⟩,⟨629724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19368_629725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19368 ⟨629725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19368
    ⟨629725, by decide⟩ (by decide) (![⟨629656, by decide⟩,⟨629682, by decide⟩,⟨629702, by decide⟩,⟨629724, by decide⟩]) unmarked_context_11_19368_629725 node_context_11_19368_629725
  intro a
  fin_cases a
  · exact context_12_77472_629656
  · exact context_12_77473_629682
  · exact context_12_77474_629702
  · exact context_12_77475_629724

theorem selected_cut_24919 : selected 9 ⟨629749, by decide⟩
    (prefixPartial 12 77476) = some ⟨12, 2, 0, 629749, 77476, 1713, 65536⟩ := by
  decide +kernel

theorem context_12_77476_629749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77476 ⟨629749, by decide⟩ :=
  accepted_of_selected 12 77476 ⟨629749, by decide⟩ ⟨12, 2, 0, 629749, 77476, 1713, 65536⟩
    (by decide) selected_cut_24919

theorem selected_cut_24920 : selected 9 ⟨629772, by decide⟩
    (prefixPartial 12 77477) = some ⟨12, 2, 0, 629772, 77477, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_77477_629772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77477 ⟨629772, by decide⟩ :=
  accepted_of_selected 12 77477 ⟨629772, by decide⟩ ⟨12, 2, 0, 629772, 77477, 1873, 65536⟩
    (by decide) selected_cut_24920

theorem selected_cut_24921 : selected 9 ⟨629795, by decide⟩
    (prefixPartial 12 77478) = some ⟨12, 2, 0, 629795, 77478, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_77478_629795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77478 ⟨629795, by decide⟩ :=
  accepted_of_selected 12 77478 ⟨629795, by decide⟩ ⟨12, 2, 0, 629795, 77478, 1705, 65536⟩
    (by decide) selected_cut_24921

theorem selected_cut_24922 : selected 9 ⟨629832, by decide⟩
    (prefixPartial 12 77479) = some ⟨12, 2, 0, 629832, 77479, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_77479_629832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77479 ⟨629832, by decide⟩ :=
  accepted_of_selected 12 77479 ⟨629832, by decide⟩ ⟨12, 2, 0, 629832, 77479, 1993, 65536⟩
    (by decide) selected_cut_24922

theorem unmarked_context_11_19369_629833 : frontier 10 ⟨629833, by decide⟩
    (prefixCache 11 19369) (prefixPartial 11 19369) = false := by
  decide +kernel

theorem node_context_11_19369_629833 : EJMOriginalGlobalDAGData.nodes 10 ⟨629833, by decide⟩ =
    .split (coordinate 11) (![⟨629749, by decide⟩,⟨629772, by decide⟩,⟨629795, by decide⟩,⟨629832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19369_629833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19369 ⟨629833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19369
    ⟨629833, by decide⟩ (by decide) (![⟨629749, by decide⟩,⟨629772, by decide⟩,⟨629795, by decide⟩,⟨629832, by decide⟩]) unmarked_context_11_19369_629833 node_context_11_19369_629833
  intro a
  fin_cases a
  · exact context_12_77476_629749
  · exact context_12_77477_629772
  · exact context_12_77478_629795
  · exact context_12_77479_629832

theorem selected_cut_24923 : selected 9 ⟨629852, by decide⟩
    (prefixPartial 12 77480) = some ⟨12, 2, 0, 629852, 77480, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_77480_629852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77480 ⟨629852, by decide⟩ :=
  accepted_of_selected 12 77480 ⟨629852, by decide⟩ ⟨12, 2, 0, 629852, 77480, 1517, 65536⟩
    (by decide) selected_cut_24923

theorem selected_cut_24924 : selected 9 ⟨629870, by decide⟩
    (prefixPartial 12 77481) = some ⟨12, 2, 0, 629870, 77481, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_77481_629870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77481 ⟨629870, by decide⟩ :=
  accepted_of_selected 12 77481 ⟨629870, by decide⟩ ⟨12, 2, 0, 629870, 77481, 1769, 65536⟩
    (by decide) selected_cut_24924

theorem selected_cut_24925 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 77482) = some ⟨12, 1, 0, 445248, 77482, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77482_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77482 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 77482 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 77482, 1, 65536⟩
    (by decide) selected_cut_24925

theorem selected_cut_24926 : selected 9 ⟨629888, by decide⟩
    (prefixPartial 12 77483) = some ⟨12, 2, 0, 629888, 77483, 1717, 65536⟩ := by
  decide +kernel

theorem context_12_77483_629888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77483 ⟨629888, by decide⟩ :=
  accepted_of_selected 12 77483 ⟨629888, by decide⟩ ⟨12, 2, 0, 629888, 77483, 1717, 65536⟩
    (by decide) selected_cut_24926

theorem unmarked_context_11_19370_629889 : frontier 10 ⟨629889, by decide⟩
    (prefixCache 11 19370) (prefixPartial 11 19370) = false := by
  decide +kernel

theorem node_context_11_19370_629889 : EJMOriginalGlobalDAGData.nodes 10 ⟨629889, by decide⟩ =
    .split (coordinate 11) (![⟨629852, by decide⟩,⟨629870, by decide⟩,⟨445248, by decide⟩,⟨629888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19370_629889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19370 ⟨629889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19370
    ⟨629889, by decide⟩ (by decide) (![⟨629852, by decide⟩,⟨629870, by decide⟩,⟨445248, by decide⟩,⟨629888, by decide⟩]) unmarked_context_11_19370_629889 node_context_11_19370_629889
  intro a
  fin_cases a
  · exact context_12_77480_629852
  · exact context_12_77481_629870
  · exact context_12_77482_445248
  · exact context_12_77483_629888

theorem selected_cut_24927 : selected 9 ⟨629906, by decide⟩
    (prefixPartial 12 77484) = some ⟨12, 2, 0, 629906, 77484, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_77484_629906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77484 ⟨629906, by decide⟩ :=
  accepted_of_selected 12 77484 ⟨629906, by decide⟩ ⟨12, 2, 0, 629906, 77484, 1465, 65536⟩
    (by decide) selected_cut_24927

theorem selected_cut_24928 : selected 9 ⟨629927, by decide⟩
    (prefixPartial 12 77485) = some ⟨12, 2, 0, 629927, 77485, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_77485_629927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77485 ⟨629927, by decide⟩ :=
  accepted_of_selected 12 77485 ⟨629927, by decide⟩ ⟨12, 2, 0, 629927, 77485, 1573, 65536⟩
    (by decide) selected_cut_24928

theorem selected_cut_24929 : selected 9 ⟨629943, by decide⟩
    (prefixPartial 12 77486) = some ⟨12, 2, 0, 629943, 77486, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_77486_629943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77486 ⟨629943, by decide⟩ :=
  accepted_of_selected 12 77486 ⟨629943, by decide⟩ ⟨12, 2, 0, 629943, 77486, 1357, 65536⟩
    (by decide) selected_cut_24929

theorem selected_cut_24930 : selected 9 ⟨629961, by decide⟩
    (prefixPartial 12 77487) = some ⟨12, 2, 0, 629961, 77487, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_77487_629961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77487 ⟨629961, by decide⟩ :=
  accepted_of_selected 12 77487 ⟨629961, by decide⟩ ⟨12, 2, 0, 629961, 77487, 1653, 65536⟩
    (by decide) selected_cut_24930

theorem unmarked_context_11_19371_629962 : frontier 10 ⟨629962, by decide⟩
    (prefixCache 11 19371) (prefixPartial 11 19371) = false := by
  decide +kernel

theorem node_context_11_19371_629962 : EJMOriginalGlobalDAGData.nodes 10 ⟨629962, by decide⟩ =
    .split (coordinate 11) (![⟨629906, by decide⟩,⟨629927, by decide⟩,⟨629943, by decide⟩,⟨629961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19371_629962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19371 ⟨629962, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19371
    ⟨629962, by decide⟩ (by decide) (![⟨629906, by decide⟩,⟨629927, by decide⟩,⟨629943, by decide⟩,⟨629961, by decide⟩]) unmarked_context_11_19371_629962 node_context_11_19371_629962
  intro a
  fin_cases a
  · exact context_12_77484_629906
  · exact context_12_77485_629927
  · exact context_12_77486_629943
  · exact context_12_77487_629961

theorem unmarked_context_10_4842_629963 : frontier 11 ⟨629963, by decide⟩
    (prefixCache 10 4842) (prefixPartial 10 4842) = false := by
  decide +kernel

theorem node_context_10_4842_629963 : EJMOriginalGlobalDAGData.nodes 11 ⟨629963, by decide⟩ =
    .split (coordinate 10) (![⟨629725, by decide⟩,⟨629833, by decide⟩,⟨629889, by decide⟩,⟨629962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4842_629963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4842 ⟨629963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4842
    ⟨629963, by decide⟩ (by decide) (![⟨629725, by decide⟩,⟨629833, by decide⟩,⟨629889, by decide⟩,⟨629962, by decide⟩]) unmarked_context_10_4842_629963 node_context_10_4842_629963
  intro a
  fin_cases a
  · exact context_11_19368_629725
  · exact context_11_19369_629833
  · exact context_11_19370_629889
  · exact context_11_19371_629962

theorem selected_cut_24931 : selected 9 ⟨629980, by decide⟩
    (prefixPartial 12 77488) = some ⟨12, 2, 0, 629980, 77488, 1109, 65536⟩ := by
  decide +kernel

theorem context_12_77488_629980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77488 ⟨629980, by decide⟩ :=
  accepted_of_selected 12 77488 ⟨629980, by decide⟩ ⟨12, 2, 0, 629980, 77488, 1109, 65536⟩
    (by decide) selected_cut_24931

theorem selected_cut_24932 : selected 9 ⟨629998, by decide⟩
    (prefixPartial 12 77489) = some ⟨12, 2, 0, 629998, 77489, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_77489_629998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77489 ⟨629998, by decide⟩ :=
  accepted_of_selected 12 77489 ⟨629998, by decide⟩ ⟨12, 2, 0, 629998, 77489, 1485, 65536⟩
    (by decide) selected_cut_24932

theorem selected_cut_24933 : selected 9 ⟨630014, by decide⟩
    (prefixPartial 12 77490) = some ⟨12, 2, 0, 630014, 77490, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_77490_630014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77490 ⟨630014, by decide⟩ :=
  accepted_of_selected 12 77490 ⟨630014, by decide⟩ ⟨12, 2, 0, 630014, 77490, 1233, 65536⟩
    (by decide) selected_cut_24933

theorem selected_cut_24934 : selected 9 ⟨630030, by decide⟩
    (prefixPartial 12 77491) = some ⟨12, 2, 0, 630030, 77491, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_77491_630030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77491 ⟨630030, by decide⟩ :=
  accepted_of_selected 12 77491 ⟨630030, by decide⟩ ⟨12, 2, 0, 630030, 77491, 1397, 65536⟩
    (by decide) selected_cut_24934

theorem unmarked_context_11_19372_630031 : frontier 10 ⟨630031, by decide⟩
    (prefixCache 11 19372) (prefixPartial 11 19372) = false := by
  decide +kernel

theorem node_context_11_19372_630031 : EJMOriginalGlobalDAGData.nodes 10 ⟨630031, by decide⟩ =
    .split (coordinate 11) (![⟨629980, by decide⟩,⟨629998, by decide⟩,⟨630014, by decide⟩,⟨630030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19372_630031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19372 ⟨630031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19372
    ⟨630031, by decide⟩ (by decide) (![⟨629980, by decide⟩,⟨629998, by decide⟩,⟨630014, by decide⟩,⟨630030, by decide⟩]) unmarked_context_11_19372_630031 node_context_11_19372_630031
  intro a
  fin_cases a
  · exact context_12_77488_629980
  · exact context_12_77489_629998
  · exact context_12_77490_630014
  · exact context_12_77491_630030

theorem selected_cut_24935 : selected 9 ⟨630049, by decide⟩
    (prefixPartial 12 77492) = some ⟨12, 2, 0, 630049, 77492, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_77492_630049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77492 ⟨630049, by decide⟩ :=
  accepted_of_selected 12 77492 ⟨630049, by decide⟩ ⟨12, 2, 0, 630049, 77492, 1101, 65536⟩
    (by decide) selected_cut_24935

theorem selected_cut_24936 : selected 9 ⟨630064, by decide⟩
    (prefixPartial 12 77493) = some ⟨12, 2, 0, 630064, 77493, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_77493_630064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77493 ⟨630064, by decide⟩ :=
  accepted_of_selected 12 77493 ⟨630064, by decide⟩ ⟨12, 2, 0, 630064, 77493, 1361, 65536⟩
    (by decide) selected_cut_24936

theorem selected_cut_24937 : selected 9 ⟨630080, by decide⟩
    (prefixPartial 12 77494) = some ⟨12, 2, 0, 630080, 77494, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_77494_630080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77494 ⟨630080, by decide⟩ :=
  accepted_of_selected 12 77494 ⟨630080, by decide⟩ ⟨12, 2, 0, 630080, 77494, 1197, 65536⟩
    (by decide) selected_cut_24937

theorem selected_cut_24938 : selected 9 ⟨630097, by decide⟩
    (prefixPartial 12 77495) = some ⟨12, 2, 0, 630097, 77495, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_77495_630097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77495 ⟨630097, by decide⟩ :=
  accepted_of_selected 12 77495 ⟨630097, by decide⟩ ⟨12, 2, 0, 630097, 77495, 1301, 65536⟩
    (by decide) selected_cut_24938

theorem unmarked_context_11_19373_630098 : frontier 10 ⟨630098, by decide⟩
    (prefixCache 11 19373) (prefixPartial 11 19373) = false := by
  decide +kernel

theorem node_context_11_19373_630098 : EJMOriginalGlobalDAGData.nodes 10 ⟨630098, by decide⟩ =
    .split (coordinate 11) (![⟨630049, by decide⟩,⟨630064, by decide⟩,⟨630080, by decide⟩,⟨630097, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19373_630098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19373 ⟨630098, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19373
    ⟨630098, by decide⟩ (by decide) (![⟨630049, by decide⟩,⟨630064, by decide⟩,⟨630080, by decide⟩,⟨630097, by decide⟩]) unmarked_context_11_19373_630098 node_context_11_19373_630098
  intro a
  fin_cases a
  · exact context_12_77492_630049
  · exact context_12_77493_630064
  · exact context_12_77494_630080
  · exact context_12_77495_630097

theorem selected_cut_24939 : selected 10 ⟨630144, by decide⟩
    (prefixPartial 11 19374) = some ⟨11, 2, 0, 630144, 19374, 3469, 262144⟩ := by
  decide +kernel

theorem context_11_19374_630144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19374 ⟨630144, by decide⟩ :=
  accepted_of_selected 11 19374 ⟨630144, by decide⟩ ⟨11, 2, 0, 630144, 19374, 3469, 262144⟩
    (by decide) selected_cut_24939

theorem selected_cut_24940 : selected 10 ⟨630210, by decide⟩
    (prefixPartial 11 19375) = some ⟨11, 2, 0, 630210, 19375, 4037, 262144⟩ := by
  decide +kernel

theorem context_11_19375_630210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19375 ⟨630210, by decide⟩ :=
  accepted_of_selected 11 19375 ⟨630210, by decide⟩ ⟨11, 2, 0, 630210, 19375, 4037, 262144⟩
    (by decide) selected_cut_24940

theorem unmarked_context_10_4843_630211 : frontier 11 ⟨630211, by decide⟩
    (prefixCache 10 4843) (prefixPartial 10 4843) = false := by
  decide +kernel

theorem node_context_10_4843_630211 : EJMOriginalGlobalDAGData.nodes 11 ⟨630211, by decide⟩ =
    .split (coordinate 10) (![⟨630031, by decide⟩,⟨630098, by decide⟩,⟨630144, by decide⟩,⟨630210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4843_630211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4843 ⟨630211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4843
    ⟨630211, by decide⟩ (by decide) (![⟨630031, by decide⟩,⟨630098, by decide⟩,⟨630144, by decide⟩,⟨630210, by decide⟩]) unmarked_context_10_4843_630211 node_context_10_4843_630211
  intro a
  fin_cases a
  · exact context_11_19372_630031
  · exact context_11_19373_630098
  · exact context_11_19374_630144
  · exact context_11_19375_630210

theorem unmarked_context_9_1210_630212 : frontier 12 ⟨630212, by decide⟩
    (prefixCache 9 1210) (prefixPartial 9 1210) = false := by
  decide +kernel

theorem node_context_9_1210_630212 : EJMOriginalGlobalDAGData.nodes 12 ⟨630212, by decide⟩ =
    .split (coordinate 9) (![⟨629132, by decide⟩,⟨629633, by decide⟩,⟨629963, by decide⟩,⟨630211, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1210_630212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1210 ⟨630212, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1210
    ⟨630212, by decide⟩ (by decide) (![⟨629132, by decide⟩,⟨629633, by decide⟩,⟨629963, by decide⟩,⟨630211, by decide⟩]) unmarked_context_9_1210_630212 node_context_9_1210_630212
  intro a
  fin_cases a
  · exact context_10_4840_629132
  · exact context_10_4841_629633
  · exact context_10_4842_629963
  · exact context_10_4843_630211

theorem selected_cut_24941 : selected 10 ⟨630262, by decide⟩
    (prefixPartial 11 19376) = some ⟨11, 2, 0, 630262, 19376, 4085, 262144⟩ := by
  decide +kernel

theorem context_11_19376_630262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19376 ⟨630262, by decide⟩ :=
  accepted_of_selected 11 19376 ⟨630262, by decide⟩ ⟨11, 2, 0, 630262, 19376, 4085, 262144⟩
    (by decide) selected_cut_24941

theorem selected_cut_24942 : selected 10 ⟨630306, by decide⟩
    (prefixPartial 11 19377) = some ⟨11, 2, 0, 630306, 19377, 3477, 262144⟩ := by
  decide +kernel

theorem context_11_19377_630306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19377 ⟨630306, by decide⟩ :=
  accepted_of_selected 11 19377 ⟨630306, by decide⟩ ⟨11, 2, 0, 630306, 19377, 3477, 262144⟩
    (by decide) selected_cut_24942

theorem selected_cut_24943 : selected 10 ⟨630362, by decide⟩
    (prefixPartial 11 19378) = some ⟨11, 2, 0, 630362, 19378, 3617, 262144⟩ := by
  decide +kernel

theorem context_11_19378_630362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19378 ⟨630362, by decide⟩ :=
  accepted_of_selected 11 19378 ⟨630362, by decide⟩ ⟨11, 2, 0, 630362, 19378, 3617, 262144⟩
    (by decide) selected_cut_24943

theorem selected_cut_24944 : selected 10 ⟨630390, by decide⟩
    (prefixPartial 11 19379) = some ⟨11, 2, 0, 630390, 19379, 2973, 262144⟩ := by
  decide +kernel

theorem context_11_19379_630390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19379 ⟨630390, by decide⟩ :=
  accepted_of_selected 11 19379 ⟨630390, by decide⟩ ⟨11, 2, 0, 630390, 19379, 2973, 262144⟩
    (by decide) selected_cut_24944

theorem unmarked_context_10_4844_630391 : frontier 11 ⟨630391, by decide⟩
    (prefixCache 10 4844) (prefixPartial 10 4844) = false := by
  decide +kernel

theorem node_context_10_4844_630391 : EJMOriginalGlobalDAGData.nodes 11 ⟨630391, by decide⟩ =
    .split (coordinate 10) (![⟨630262, by decide⟩,⟨630306, by decide⟩,⟨630362, by decide⟩,⟨630390, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4844_630391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4844 ⟨630391, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4844
    ⟨630391, by decide⟩ (by decide) (![⟨630262, by decide⟩,⟨630306, by decide⟩,⟨630362, by decide⟩,⟨630390, by decide⟩]) unmarked_context_10_4844_630391 node_context_10_4844_630391
  intro a
  fin_cases a
  · exact context_11_19376_630262
  · exact context_11_19377_630306
  · exact context_11_19378_630362
  · exact context_11_19379_630390

theorem selected_cut_24945 : selected 10 ⟨630425, by decide⟩
    (prefixPartial 11 19380) = some ⟨11, 2, 0, 630425, 19380, 2873, 262144⟩ := by
  decide +kernel

theorem context_11_19380_630425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19380 ⟨630425, by decide⟩ :=
  accepted_of_selected 11 19380 ⟨630425, by decide⟩ ⟨11, 2, 0, 630425, 19380, 2873, 262144⟩
    (by decide) selected_cut_24945

theorem selected_cut_24946 : selected 10 ⟨630455, by decide⟩
    (prefixPartial 11 19381) = some ⟨11, 2, 0, 630455, 19381, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_19381_630455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19381 ⟨630455, by decide⟩ :=
  accepted_of_selected 11 19381 ⟨630455, by decide⟩ ⟨11, 2, 0, 630455, 19381, 2433, 262144⟩
    (by decide) selected_cut_24946

theorem selected_cut_24947 : selected 10 ⟨630490, by decide⟩
    (prefixPartial 11 19382) = some ⟨11, 2, 0, 630490, 19382, 2381, 262144⟩ := by
  decide +kernel

theorem context_11_19382_630490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19382 ⟨630490, by decide⟩ :=
  accepted_of_selected 11 19382 ⟨630490, by decide⟩ ⟨11, 2, 0, 630490, 19382, 2381, 262144⟩
    (by decide) selected_cut_24947

theorem selected_cut_24948 : selected 10 ⟨630515, by decide⟩
    (prefixPartial 11 19383) = some ⟨11, 2, 0, 630515, 19383, 1845, 262144⟩ := by
  decide +kernel

theorem context_11_19383_630515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19383 ⟨630515, by decide⟩ :=
  accepted_of_selected 11 19383 ⟨630515, by decide⟩ ⟨11, 2, 0, 630515, 19383, 1845, 262144⟩
    (by decide) selected_cut_24948

theorem unmarked_context_10_4845_630516 : frontier 11 ⟨630516, by decide⟩
    (prefixCache 10 4845) (prefixPartial 10 4845) = false := by
  decide +kernel

theorem node_context_10_4845_630516 : EJMOriginalGlobalDAGData.nodes 11 ⟨630516, by decide⟩ =
    .split (coordinate 10) (![⟨630425, by decide⟩,⟨630455, by decide⟩,⟨630490, by decide⟩,⟨630515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4845_630516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4845 ⟨630516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4845
    ⟨630516, by decide⟩ (by decide) (![⟨630425, by decide⟩,⟨630455, by decide⟩,⟨630490, by decide⟩,⟨630515, by decide⟩]) unmarked_context_10_4845_630516 node_context_10_4845_630516
  intro a
  fin_cases a
  · exact context_11_19380_630425
  · exact context_11_19381_630455
  · exact context_11_19382_630490
  · exact context_11_19383_630515

theorem selected_cut_24949 : selected 10 ⟨630532, by decide⟩
    (prefixPartial 11 19384) = some ⟨11, 2, 0, 630532, 19384, 1477, 262144⟩ := by
  decide +kernel

theorem context_11_19384_630532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19384 ⟨630532, by decide⟩ :=
  accepted_of_selected 11 19384 ⟨630532, by decide⟩ ⟨11, 2, 0, 630532, 19384, 1477, 262144⟩
    (by decide) selected_cut_24949

theorem selected_cut_24950 : selected 10 ⟨630560, by decide⟩
    (prefixPartial 11 19385) = some ⟨11, 2, 0, 630560, 19385, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_19385_630560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19385 ⟨630560, by decide⟩ :=
  accepted_of_selected 11 19385 ⟨630560, by decide⟩ ⟨11, 2, 0, 630560, 19385, 1313, 262144⟩
    (by decide) selected_cut_24950

theorem selected_cut_24951 : selected 10 ⟨630573, by decide⟩
    (prefixPartial 11 19386) = some ⟨11, 2, 0, 630573, 19386, 785, 262144⟩ := by
  decide +kernel

theorem context_11_19386_630573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19386 ⟨630573, by decide⟩ :=
  accepted_of_selected 11 19386 ⟨630573, by decide⟩ ⟨11, 2, 0, 630573, 19386, 785, 262144⟩
    (by decide) selected_cut_24951

theorem selected_cut_24952 : selected 10 ⟨630585, by decide⟩
    (prefixPartial 11 19387) = some ⟨11, 2, 0, 630585, 19387, 825, 262144⟩ := by
  decide +kernel

theorem context_11_19387_630585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19387 ⟨630585, by decide⟩ :=
  accepted_of_selected 11 19387 ⟨630585, by decide⟩ ⟨11, 2, 0, 630585, 19387, 825, 262144⟩
    (by decide) selected_cut_24952

theorem unmarked_context_10_4846_630586 : frontier 11 ⟨630586, by decide⟩
    (prefixCache 10 4846) (prefixPartial 10 4846) = false := by
  decide +kernel

theorem node_context_10_4846_630586 : EJMOriginalGlobalDAGData.nodes 11 ⟨630586, by decide⟩ =
    .split (coordinate 10) (![⟨630532, by decide⟩,⟨630560, by decide⟩,⟨630573, by decide⟩,⟨630585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4846_630586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4846 ⟨630586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4846
    ⟨630586, by decide⟩ (by decide) (![⟨630532, by decide⟩,⟨630560, by decide⟩,⟨630573, by decide⟩,⟨630585, by decide⟩]) unmarked_context_10_4846_630586 node_context_10_4846_630586
  intro a
  fin_cases a
  · exact context_11_19384_630532
  · exact context_11_19385_630560
  · exact context_11_19386_630573
  · exact context_11_19387_630585

theorem selected_cut_24953 : selected 11 ⟨630622, by decide⟩
    (prefixPartial 10 4847) = some ⟨10, 2, 0, 630622, 4847, 1177, 1048576⟩ := by
  decide +kernel

theorem context_10_4847_630622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4847 ⟨630622, by decide⟩ :=
  accepted_of_selected 10 4847 ⟨630622, by decide⟩ ⟨10, 2, 0, 630622, 4847, 1177, 1048576⟩
    (by decide) selected_cut_24953

theorem unmarked_context_9_1211_630623 : frontier 12 ⟨630623, by decide⟩
    (prefixCache 9 1211) (prefixPartial 9 1211) = false := by
  decide +kernel

theorem node_context_9_1211_630623 : EJMOriginalGlobalDAGData.nodes 12 ⟨630623, by decide⟩ =
    .split (coordinate 9) (![⟨630391, by decide⟩,⟨630516, by decide⟩,⟨630586, by decide⟩,⟨630622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1211_630623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1211 ⟨630623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1211
    ⟨630623, by decide⟩ (by decide) (![⟨630391, by decide⟩,⟨630516, by decide⟩,⟨630586, by decide⟩,⟨630622, by decide⟩]) unmarked_context_9_1211_630623 node_context_9_1211_630623
  intro a
  fin_cases a
  · exact context_10_4844_630391
  · exact context_10_4845_630516
  · exact context_10_4846_630586
  · exact context_10_4847_630622

theorem unmarked_context_8_302_630624 : frontier 13 ⟨630624, by decide⟩
    (prefixCache 8 302) (prefixPartial 8 302) = false := by
  decide +kernel

theorem node_context_8_302_630624 : EJMOriginalGlobalDAGData.nodes 13 ⟨630624, by decide⟩ =
    .split (coordinate 8) (![⟨625266, by decide⟩,⟨628687, by decide⟩,⟨630212, by decide⟩,⟨630623, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_302_630624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 302 ⟨630624, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 302
    ⟨630624, by decide⟩ (by decide) (![⟨625266, by decide⟩,⟨628687, by decide⟩,⟨630212, by decide⟩,⟨630623, by decide⟩]) unmarked_context_8_302_630624 node_context_8_302_630624
  intro a
  fin_cases a
  · exact context_9_1208_625266
  · exact context_9_1209_628687
  · exact context_9_1210_630212
  · exact context_9_1211_630623

theorem selected_cut_24954 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 19392) = some ⟨11, 1, 0, 434745, 19392, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19392_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19392 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 19392 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 19392, 1, 262144⟩
    (by decide) selected_cut_24954

theorem selected_cut_24955 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 77572) = some ⟨12, 1, 0, 448748, 77572, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77572_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77572 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 77572 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 77572, 1, 65536⟩
    (by decide) selected_cut_24955

theorem selected_cut_24956 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 77573) = some ⟨12, 1, 0, 34034, 77573, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77573_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77573 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 77573 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 77573, 1, 65536⟩
    (by decide) selected_cut_24956

theorem selected_cut_24957 : selected 8 ⟨630713, by decide⟩
    (prefixPartial 13 310296) = some ⟨13, 2, 0, 630713, 310296, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_310296_630713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310296 ⟨630713, by decide⟩ :=
  accepted_of_selected 13 310296 ⟨630713, by decide⟩ ⟨13, 2, 0, 630713, 310296, 1469, 16384⟩
    (by decide) selected_cut_24957

theorem selected_cut_24958 : selected 8 ⟨630809, by decide⟩
    (prefixPartial 13 310297) = some ⟨13, 2, 0, 630809, 310297, 2781, 16384⟩ := by
  decide +kernel

theorem context_13_310297_630809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310297 ⟨630809, by decide⟩ :=
  accepted_of_selected 13 310297 ⟨630809, by decide⟩ ⟨13, 2, 0, 630809, 310297, 2781, 16384⟩
    (by decide) selected_cut_24958

theorem selected_cut_24959 : selected 8 ⟨34831, by decide⟩
    (prefixPartial 13 310298) = some ⟨13, 1, 0, 34831, 310298, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310298_34831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310298 ⟨34831, by decide⟩ :=
  accepted_of_selected 13 310298 ⟨34831, by decide⟩ ⟨13, 1, 0, 34831, 310298, 1, 16384⟩
    (by decide) selected_cut_24959

theorem selected_cut_24960 : selected 8 ⟨630819, by decide⟩
    (prefixPartial 13 310299) = some ⟨13, 2, 0, 630819, 310299, 473, 16384⟩ := by
  decide +kernel

theorem context_13_310299_630819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310299 ⟨630819, by decide⟩ :=
  accepted_of_selected 13 310299 ⟨630819, by decide⟩ ⟨13, 2, 0, 630819, 310299, 473, 16384⟩
    (by decide) selected_cut_24960

theorem unmarked_context_12_77574_630820 : frontier 9 ⟨630820, by decide⟩
    (prefixCache 12 77574) (prefixPartial 12 77574) = false := by
  decide +kernel

theorem node_context_12_77574_630820 : EJMOriginalGlobalDAGData.nodes 9 ⟨630820, by decide⟩ =
    .split (coordinate 12) (![⟨630713, by decide⟩,⟨630809, by decide⟩,⟨34831, by decide⟩,⟨630819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77574_630820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77574 ⟨630820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77574
    ⟨630820, by decide⟩ (by decide) (![⟨630713, by decide⟩,⟨630809, by decide⟩,⟨34831, by decide⟩,⟨630819, by decide⟩]) unmarked_context_12_77574_630820 node_context_12_77574_630820
  intro a
  fin_cases a
  · exact context_13_310296_630713
  · exact context_13_310297_630809
  · exact context_13_310298_34831
  · exact context_13_310299_630819

theorem selected_cut_24961 : selected 9 ⟨603785, by decide⟩
    (prefixPartial 12 77575) = some ⟨12, 1, 0, 603785, 77575, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77575_603785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77575 ⟨603785, by decide⟩ :=
  accepted_of_selected 12 77575 ⟨603785, by decide⟩ ⟨12, 1, 0, 603785, 77575, 1, 65536⟩
    (by decide) selected_cut_24961

theorem unmarked_context_11_19393_630821 : frontier 10 ⟨630821, by decide⟩
    (prefixCache 11 19393) (prefixPartial 11 19393) = false := by
  decide +kernel

theorem node_context_11_19393_630821 : EJMOriginalGlobalDAGData.nodes 10 ⟨630821, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨630820, by decide⟩,⟨603785, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19393_630821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19393 ⟨630821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19393
    ⟨630821, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨630820, by decide⟩,⟨603785, by decide⟩]) unmarked_context_11_19393_630821 node_context_11_19393_630821
  intro a
  fin_cases a
  · exact context_12_77572_448748
  · exact context_12_77573_34034
  · exact context_12_77574_630820
  · exact context_12_77575_603785

theorem selected_cut_24962 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 77576) = some ⟨12, 1, 0, 448748, 77576, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77576_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77576 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 77576 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 77576, 1, 65536⟩
    (by decide) selected_cut_24962

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
