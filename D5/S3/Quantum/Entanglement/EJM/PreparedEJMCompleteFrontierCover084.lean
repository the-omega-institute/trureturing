/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover083
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_5705_229385 : frontier 10 ⟨229385, by decide⟩
    (prefixCache 11 5705) (prefixPartial 11 5705) = false := by
  decide +kernel

theorem node_context_11_5705_229385 : EJMOriginalGlobalDAGData.nodes 10 ⟨229385, by decide⟩ =
    .split (coordinate 11) (![⟨229167, by decide⟩,⟨229236, by decide⟩,⟨229305, by decide⟩,⟨229384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5705_229385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5705 ⟨229385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5705
    ⟨229385, by decide⟩ (by decide) (![⟨229167, by decide⟩,⟨229236, by decide⟩,⟨229305, by decide⟩,⟨229384, by decide⟩]) unmarked_context_11_5705_229385 node_context_11_5705_229385
  intro a
  fin_cases a
  · exact context_12_22820_229167
  · exact context_12_22821_229236
  · exact context_12_22822_229305
  · exact context_12_22823_229384

theorem selected_cut_08067 : selected 8 ⟨229413, by decide⟩
    (prefixPartial 13 91296) = some ⟨13, 2, 0, 229413, 91296, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_91296_229413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91296 ⟨229413, by decide⟩ :=
  accepted_of_selected 13 91296 ⟨229413, by decide⟩ ⟨13, 2, 0, 229413, 91296, 1541, 16384⟩
    (by decide) selected_cut_08067

theorem selected_cut_08068 : selected 8 ⟨229463, by decide⟩
    (prefixPartial 13 91297) = some ⟨13, 2, 0, 229463, 91297, 3161, 16384⟩ := by
  decide +kernel

theorem context_13_91297_229463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91297 ⟨229463, by decide⟩ :=
  accepted_of_selected 13 91297 ⟨229463, by decide⟩ ⟨13, 2, 0, 229463, 91297, 3161, 16384⟩
    (by decide) selected_cut_08068

theorem selected_cut_08069 : selected 8 ⟨229481, by decide⟩
    (prefixPartial 13 91298) = some ⟨13, 2, 0, 229481, 91298, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_91298_229481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91298 ⟨229481, by decide⟩ :=
  accepted_of_selected 13 91298 ⟨229481, by decide⟩ ⟨13, 2, 0, 229481, 91298, 1933, 16384⟩
    (by decide) selected_cut_08069

theorem selected_cut_08070 : selected 8 ⟨229489, by decide⟩
    (prefixPartial 13 91299) = some ⟨13, 2, 0, 229489, 91299, 1149, 16384⟩ := by
  decide +kernel

theorem context_13_91299_229489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91299 ⟨229489, by decide⟩ :=
  accepted_of_selected 13 91299 ⟨229489, by decide⟩ ⟨13, 2, 0, 229489, 91299, 1149, 16384⟩
    (by decide) selected_cut_08070

theorem unmarked_context_12_22824_229490 : frontier 9 ⟨229490, by decide⟩
    (prefixCache 12 22824) (prefixPartial 12 22824) = false := by
  decide +kernel

theorem node_context_12_22824_229490 : EJMOriginalGlobalDAGData.nodes 9 ⟨229490, by decide⟩ =
    .split (coordinate 12) (![⟨229413, by decide⟩,⟨229463, by decide⟩,⟨229481, by decide⟩,⟨229489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22824_229490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22824 ⟨229490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22824
    ⟨229490, by decide⟩ (by decide) (![⟨229413, by decide⟩,⟨229463, by decide⟩,⟨229481, by decide⟩,⟨229489, by decide⟩]) unmarked_context_12_22824_229490 node_context_12_22824_229490
  intro a
  fin_cases a
  · exact context_13_91296_229413
  · exact context_13_91297_229463
  · exact context_13_91298_229481
  · exact context_13_91299_229489

theorem selected_cut_08071 : selected 8 ⟨229506, by decide⟩
    (prefixPartial 13 91300) = some ⟨13, 2, 0, 229506, 91300, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_91300_229506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91300 ⟨229506, by decide⟩ :=
  accepted_of_selected 13 91300 ⟨229506, by decide⟩ ⟨13, 2, 0, 229506, 91300, 1449, 16384⟩
    (by decide) selected_cut_08071

theorem selected_cut_08072 : selected 8 ⟨229530, by decide⟩
    (prefixPartial 13 91301) = some ⟨13, 2, 0, 229530, 91301, 2513, 16384⟩ := by
  decide +kernel

theorem context_13_91301_229530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91301 ⟨229530, by decide⟩ :=
  accepted_of_selected 13 91301 ⟨229530, by decide⟩ ⟨13, 2, 0, 229530, 91301, 2513, 16384⟩
    (by decide) selected_cut_08072

theorem selected_cut_08073 : selected 8 ⟨229547, by decide⟩
    (prefixPartial 13 91302) = some ⟨13, 2, 0, 229547, 91302, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_91302_229547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91302 ⟨229547, by decide⟩ :=
  accepted_of_selected 13 91302 ⟨229547, by decide⟩ ⟨13, 2, 0, 229547, 91302, 1977, 16384⟩
    (by decide) selected_cut_08073

theorem selected_cut_08074 : selected 8 ⟨229556, by decide⟩
    (prefixPartial 13 91303) = some ⟨13, 2, 0, 229556, 91303, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_91303_229556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91303 ⟨229556, by decide⟩ :=
  accepted_of_selected 13 91303 ⟨229556, by decide⟩ ⟨13, 2, 0, 229556, 91303, 1125, 16384⟩
    (by decide) selected_cut_08074

theorem unmarked_context_12_22825_229557 : frontier 9 ⟨229557, by decide⟩
    (prefixCache 12 22825) (prefixPartial 12 22825) = false := by
  decide +kernel

theorem node_context_12_22825_229557 : EJMOriginalGlobalDAGData.nodes 9 ⟨229557, by decide⟩ =
    .split (coordinate 12) (![⟨229506, by decide⟩,⟨229530, by decide⟩,⟨229547, by decide⟩,⟨229556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22825_229557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22825 ⟨229557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22825
    ⟨229557, by decide⟩ (by decide) (![⟨229506, by decide⟩,⟨229530, by decide⟩,⟨229547, by decide⟩,⟨229556, by decide⟩]) unmarked_context_12_22825_229557 node_context_12_22825_229557
  intro a
  fin_cases a
  · exact context_13_91300_229506
  · exact context_13_91301_229530
  · exact context_13_91302_229547
  · exact context_13_91303_229556

theorem selected_cut_08075 : selected 8 ⟨229585, by decide⟩
    (prefixPartial 13 91304) = some ⟨13, 2, 0, 229585, 91304, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_91304_229585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91304 ⟨229585, by decide⟩ :=
  accepted_of_selected 13 91304 ⟨229585, by decide⟩ ⟨13, 2, 0, 229585, 91304, 2053, 16384⟩
    (by decide) selected_cut_08075

theorem selected_cut_08076 : selected 8 ⟨229640, by decide⟩
    (prefixPartial 13 91305) = some ⟨13, 2, 0, 229640, 91305, 3685, 16384⟩ := by
  decide +kernel

theorem context_13_91305_229640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91305 ⟨229640, by decide⟩ :=
  accepted_of_selected 13 91305 ⟨229640, by decide⟩ ⟨13, 2, 0, 229640, 91305, 3685, 16384⟩
    (by decide) selected_cut_08076

theorem selected_cut_08077 : selected 8 ⟨229661, by decide⟩
    (prefixPartial 13 91306) = some ⟨13, 2, 0, 229661, 91306, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_91306_229661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91306 ⟨229661, by decide⟩ :=
  accepted_of_selected 13 91306 ⟨229661, by decide⟩ ⟨13, 2, 0, 229661, 91306, 2221, 16384⟩
    (by decide) selected_cut_08077

theorem selected_cut_08078 : selected 8 ⟨229675, by decide⟩
    (prefixPartial 13 91307) = some ⟨13, 2, 0, 229675, 91307, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_91307_229675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91307 ⟨229675, by decide⟩ :=
  accepted_of_selected 13 91307 ⟨229675, by decide⟩ ⟨13, 2, 0, 229675, 91307, 1261, 16384⟩
    (by decide) selected_cut_08078

theorem unmarked_context_12_22826_229676 : frontier 9 ⟨229676, by decide⟩
    (prefixCache 12 22826) (prefixPartial 12 22826) = false := by
  decide +kernel

theorem node_context_12_22826_229676 : EJMOriginalGlobalDAGData.nodes 9 ⟨229676, by decide⟩ =
    .split (coordinate 12) (![⟨229585, by decide⟩,⟨229640, by decide⟩,⟨229661, by decide⟩,⟨229675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22826_229676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22826 ⟨229676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22826
    ⟨229676, by decide⟩ (by decide) (![⟨229585, by decide⟩,⟨229640, by decide⟩,⟨229661, by decide⟩,⟨229675, by decide⟩]) unmarked_context_12_22826_229676 node_context_12_22826_229676
  intro a
  fin_cases a
  · exact context_13_91304_229585
  · exact context_13_91305_229640
  · exact context_13_91306_229661
  · exact context_13_91307_229675

theorem selected_cut_08079 : selected 8 ⟨229707, by decide⟩
    (prefixPartial 13 91308) = some ⟨13, 2, 0, 229707, 91308, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_91308_229707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91308 ⟨229707, by decide⟩ :=
  accepted_of_selected 13 91308 ⟨229707, by decide⟩ ⟨13, 2, 0, 229707, 91308, 1957, 16384⟩
    (by decide) selected_cut_08079

theorem selected_cut_08080 : selected 8 ⟨229764, by decide⟩
    (prefixPartial 13 91309) = some ⟨13, 2, 0, 229764, 91309, 3777, 16384⟩ := by
  decide +kernel

theorem context_13_91309_229764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91309 ⟨229764, by decide⟩ :=
  accepted_of_selected 13 91309 ⟨229764, by decide⟩ ⟨13, 2, 0, 229764, 91309, 3777, 16384⟩
    (by decide) selected_cut_08080

theorem selected_cut_08081 : selected 8 ⟨229784, by decide⟩
    (prefixPartial 13 91310) = some ⟨13, 2, 0, 229784, 91310, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_91310_229784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91310 ⟨229784, by decide⟩ :=
  accepted_of_selected 13 91310 ⟨229784, by decide⟩ ⟨13, 2, 0, 229784, 91310, 2297, 16384⟩
    (by decide) selected_cut_08081

theorem selected_cut_08082 : selected 8 ⟨229796, by decide⟩
    (prefixPartial 13 91311) = some ⟨13, 2, 0, 229796, 91311, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_91311_229796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91311 ⟨229796, by decide⟩ :=
  accepted_of_selected 13 91311 ⟨229796, by decide⟩ ⟨13, 2, 0, 229796, 91311, 1257, 16384⟩
    (by decide) selected_cut_08082

theorem unmarked_context_12_22827_229797 : frontier 9 ⟨229797, by decide⟩
    (prefixCache 12 22827) (prefixPartial 12 22827) = false := by
  decide +kernel

theorem node_context_12_22827_229797 : EJMOriginalGlobalDAGData.nodes 9 ⟨229797, by decide⟩ =
    .split (coordinate 12) (![⟨229707, by decide⟩,⟨229764, by decide⟩,⟨229784, by decide⟩,⟨229796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22827_229797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22827 ⟨229797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22827
    ⟨229797, by decide⟩ (by decide) (![⟨229707, by decide⟩,⟨229764, by decide⟩,⟨229784, by decide⟩,⟨229796, by decide⟩]) unmarked_context_12_22827_229797 node_context_12_22827_229797
  intro a
  fin_cases a
  · exact context_13_91308_229707
  · exact context_13_91309_229764
  · exact context_13_91310_229784
  · exact context_13_91311_229796

theorem unmarked_context_11_5706_229798 : frontier 10 ⟨229798, by decide⟩
    (prefixCache 11 5706) (prefixPartial 11 5706) = false := by
  decide +kernel

theorem node_context_11_5706_229798 : EJMOriginalGlobalDAGData.nodes 10 ⟨229798, by decide⟩ =
    .split (coordinate 11) (![⟨229490, by decide⟩,⟨229557, by decide⟩,⟨229676, by decide⟩,⟨229797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5706_229798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5706 ⟨229798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5706
    ⟨229798, by decide⟩ (by decide) (![⟨229490, by decide⟩,⟨229557, by decide⟩,⟨229676, by decide⟩,⟨229797, by decide⟩]) unmarked_context_11_5706_229798 node_context_11_5706_229798
  intro a
  fin_cases a
  · exact context_12_22824_229490
  · exact context_12_22825_229557
  · exact context_12_22826_229676
  · exact context_12_22827_229797

theorem selected_cut_08083 : selected 8 ⟨229811, by decide⟩
    (prefixPartial 13 91312) = some ⟨13, 2, 0, 229811, 91312, 793, 16384⟩ := by
  decide +kernel

theorem context_13_91312_229811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91312 ⟨229811, by decide⟩ :=
  accepted_of_selected 13 91312 ⟨229811, by decide⟩ ⟨13, 2, 0, 229811, 91312, 793, 16384⟩
    (by decide) selected_cut_08083

theorem selected_cut_08084 : selected 8 ⟨229836, by decide⟩
    (prefixPartial 13 91313) = some ⟨13, 2, 0, 229836, 91313, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_91313_229836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91313 ⟨229836, by decide⟩ :=
  accepted_of_selected 13 91313 ⟨229836, by decide⟩ ⟨13, 2, 0, 229836, 91313, 2493, 16384⟩
    (by decide) selected_cut_08084

theorem selected_cut_08085 : selected 8 ⟨229855, by decide⟩
    (prefixPartial 13 91314) = some ⟨13, 2, 0, 229855, 91314, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_91314_229855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91314 ⟨229855, by decide⟩ :=
  accepted_of_selected 13 91314 ⟨229855, by decide⟩ ⟨13, 2, 0, 229855, 91314, 1437, 16384⟩
    (by decide) selected_cut_08085

theorem selected_cut_08086 : selected 8 ⟨229861, by decide⟩
    (prefixPartial 13 91315) = some ⟨13, 2, 0, 229861, 91315, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_91315_229861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91315 ⟨229861, by decide⟩ :=
  accepted_of_selected 13 91315 ⟨229861, by decide⟩ ⟨13, 2, 0, 229861, 91315, 1049, 16384⟩
    (by decide) selected_cut_08086

theorem unmarked_context_12_22828_229862 : frontier 9 ⟨229862, by decide⟩
    (prefixCache 12 22828) (prefixPartial 12 22828) = false := by
  decide +kernel

theorem node_context_12_22828_229862 : EJMOriginalGlobalDAGData.nodes 9 ⟨229862, by decide⟩ =
    .split (coordinate 12) (![⟨229811, by decide⟩,⟨229836, by decide⟩,⟨229855, by decide⟩,⟨229861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22828_229862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22828 ⟨229862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22828
    ⟨229862, by decide⟩ (by decide) (![⟨229811, by decide⟩,⟨229836, by decide⟩,⟨229855, by decide⟩,⟨229861, by decide⟩]) unmarked_context_12_22828_229862 node_context_12_22828_229862
  intro a
  fin_cases a
  · exact context_13_91312_229811
  · exact context_13_91313_229836
  · exact context_13_91314_229855
  · exact context_13_91315_229861

theorem selected_cut_08087 : selected 8 ⟨229871, by decide⟩
    (prefixPartial 13 91316) = some ⟨13, 2, 0, 229871, 91316, 729, 16384⟩ := by
  decide +kernel

theorem context_13_91316_229871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91316 ⟨229871, by decide⟩ :=
  accepted_of_selected 13 91316 ⟨229871, by decide⟩ ⟨13, 2, 0, 229871, 91316, 729, 16384⟩
    (by decide) selected_cut_08087

theorem selected_cut_08088 : selected 8 ⟨229895, by decide⟩
    (prefixPartial 13 91317) = some ⟨13, 2, 0, 229895, 91317, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_91317_229895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91317 ⟨229895, by decide⟩ :=
  accepted_of_selected 13 91317 ⟨229895, by decide⟩ ⟨13, 2, 0, 229895, 91317, 1957, 16384⟩
    (by decide) selected_cut_08088

theorem selected_cut_08089 : selected 8 ⟨229912, by decide⟩
    (prefixPartial 13 91318) = some ⟨13, 2, 0, 229912, 91318, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_91318_229912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91318 ⟨229912, by decide⟩ :=
  accepted_of_selected 13 91318 ⟨229912, by decide⟩ ⟨13, 2, 0, 229912, 91318, 1401, 16384⟩
    (by decide) selected_cut_08089

theorem selected_cut_08090 : selected 8 ⟨229921, by decide⟩
    (prefixPartial 13 91319) = some ⟨13, 2, 0, 229921, 91319, 873, 16384⟩ := by
  decide +kernel

theorem context_13_91319_229921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91319 ⟨229921, by decide⟩ :=
  accepted_of_selected 13 91319 ⟨229921, by decide⟩ ⟨13, 2, 0, 229921, 91319, 873, 16384⟩
    (by decide) selected_cut_08090

theorem unmarked_context_12_22829_229922 : frontier 9 ⟨229922, by decide⟩
    (prefixCache 12 22829) (prefixPartial 12 22829) = false := by
  decide +kernel

theorem node_context_12_22829_229922 : EJMOriginalGlobalDAGData.nodes 9 ⟨229922, by decide⟩ =
    .split (coordinate 12) (![⟨229871, by decide⟩,⟨229895, by decide⟩,⟨229912, by decide⟩,⟨229921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22829_229922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22829 ⟨229922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22829
    ⟨229922, by decide⟩ (by decide) (![⟨229871, by decide⟩,⟨229895, by decide⟩,⟨229912, by decide⟩,⟨229921, by decide⟩]) unmarked_context_12_22829_229922 node_context_12_22829_229922
  intro a
  fin_cases a
  · exact context_13_91316_229871
  · exact context_13_91317_229895
  · exact context_13_91318_229912
  · exact context_13_91319_229921

theorem selected_cut_08091 : selected 8 ⟨229936, by decide⟩
    (prefixPartial 13 91320) = some ⟨13, 2, 0, 229936, 91320, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_91320_229936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91320 ⟨229936, by decide⟩ :=
  accepted_of_selected 13 91320 ⟨229936, by decide⟩ ⟨13, 2, 0, 229936, 91320, 1101, 16384⟩
    (by decide) selected_cut_08091

theorem selected_cut_08092 : selected 8 ⟨229962, by decide⟩
    (prefixPartial 13 91321) = some ⟨13, 2, 0, 229962, 91321, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_91321_229962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91321 ⟨229962, by decide⟩ :=
  accepted_of_selected 13 91321 ⟨229962, by decide⟩ ⟨13, 2, 0, 229962, 91321, 2757, 16384⟩
    (by decide) selected_cut_08092

theorem selected_cut_08093 : selected 8 ⟨229979, by decide⟩
    (prefixPartial 13 91322) = some ⟨13, 2, 0, 229979, 91322, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_91322_229979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91322 ⟨229979, by decide⟩ :=
  accepted_of_selected 13 91322 ⟨229979, by decide⟩ ⟨13, 2, 0, 229979, 91322, 1769, 16384⟩
    (by decide) selected_cut_08093

theorem selected_cut_08094 : selected 8 ⟨229985, by decide⟩
    (prefixPartial 13 91323) = some ⟨13, 2, 0, 229985, 91323, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_91323_229985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91323 ⟨229985, by decide⟩ :=
  accepted_of_selected 13 91323 ⟨229985, by decide⟩ ⟨13, 2, 0, 229985, 91323, 1021, 16384⟩
    (by decide) selected_cut_08094

theorem unmarked_context_12_22830_229986 : frontier 9 ⟨229986, by decide⟩
    (prefixCache 12 22830) (prefixPartial 12 22830) = false := by
  decide +kernel

theorem node_context_12_22830_229986 : EJMOriginalGlobalDAGData.nodes 9 ⟨229986, by decide⟩ =
    .split (coordinate 12) (![⟨229936, by decide⟩,⟨229962, by decide⟩,⟨229979, by decide⟩,⟨229985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22830_229986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22830 ⟨229986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22830
    ⟨229986, by decide⟩ (by decide) (![⟨229936, by decide⟩,⟨229962, by decide⟩,⟨229979, by decide⟩,⟨229985, by decide⟩]) unmarked_context_12_22830_229986 node_context_12_22830_229986
  intro a
  fin_cases a
  · exact context_13_91320_229936
  · exact context_13_91321_229962
  · exact context_13_91322_229979
  · exact context_13_91323_229985

theorem selected_cut_08095 : selected 8 ⟨230003, by decide⟩
    (prefixPartial 13 91324) = some ⟨13, 2, 0, 230003, 91324, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_91324_230003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91324 ⟨230003, by decide⟩ :=
  accepted_of_selected 13 91324 ⟨230003, by decide⟩ ⟨13, 2, 0, 230003, 91324, 1005, 16384⟩
    (by decide) selected_cut_08095

theorem selected_cut_08096 : selected 8 ⟨230031, by decide⟩
    (prefixPartial 13 91325) = some ⟨13, 2, 0, 230031, 91325, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_91325_230031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91325 ⟨230031, by decide⟩ :=
  accepted_of_selected 13 91325 ⟨230031, by decide⟩ ⟨13, 2, 0, 230031, 91325, 2873, 16384⟩
    (by decide) selected_cut_08096

theorem selected_cut_08097 : selected 8 ⟨230050, by decide⟩
    (prefixPartial 13 91326) = some ⟨13, 2, 0, 230050, 91326, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_91326_230050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91326 ⟨230050, by decide⟩ :=
  accepted_of_selected 13 91326 ⟨230050, by decide⟩ ⟨13, 2, 0, 230050, 91326, 1601, 16384⟩
    (by decide) selected_cut_08097

theorem selected_cut_08098 : selected 8 ⟨230059, by decide⟩
    (prefixPartial 13 91327) = some ⟨13, 2, 0, 230059, 91327, 997, 16384⟩ := by
  decide +kernel

theorem context_13_91327_230059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91327 ⟨230059, by decide⟩ :=
  accepted_of_selected 13 91327 ⟨230059, by decide⟩ ⟨13, 2, 0, 230059, 91327, 997, 16384⟩
    (by decide) selected_cut_08098

theorem unmarked_context_12_22831_230060 : frontier 9 ⟨230060, by decide⟩
    (prefixCache 12 22831) (prefixPartial 12 22831) = false := by
  decide +kernel

theorem node_context_12_22831_230060 : EJMOriginalGlobalDAGData.nodes 9 ⟨230060, by decide⟩ =
    .split (coordinate 12) (![⟨230003, by decide⟩,⟨230031, by decide⟩,⟨230050, by decide⟩,⟨230059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22831_230060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22831 ⟨230060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22831
    ⟨230060, by decide⟩ (by decide) (![⟨230003, by decide⟩,⟨230031, by decide⟩,⟨230050, by decide⟩,⟨230059, by decide⟩]) unmarked_context_12_22831_230060 node_context_12_22831_230060
  intro a
  fin_cases a
  · exact context_13_91324_230003
  · exact context_13_91325_230031
  · exact context_13_91326_230050
  · exact context_13_91327_230059

theorem unmarked_context_11_5707_230061 : frontier 10 ⟨230061, by decide⟩
    (prefixCache 11 5707) (prefixPartial 11 5707) = false := by
  decide +kernel

theorem node_context_11_5707_230061 : EJMOriginalGlobalDAGData.nodes 10 ⟨230061, by decide⟩ =
    .split (coordinate 11) (![⟨229862, by decide⟩,⟨229922, by decide⟩,⟨229986, by decide⟩,⟨230060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5707_230061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5707 ⟨230061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5707
    ⟨230061, by decide⟩ (by decide) (![⟨229862, by decide⟩,⟨229922, by decide⟩,⟨229986, by decide⟩,⟨230060, by decide⟩]) unmarked_context_11_5707_230061 node_context_11_5707_230061
  intro a
  fin_cases a
  · exact context_12_22828_229862
  · exact context_12_22829_229922
  · exact context_12_22830_229986
  · exact context_12_22831_230060

theorem unmarked_context_10_1426_230062 : frontier 11 ⟨230062, by decide⟩
    (prefixCache 10 1426) (prefixPartial 10 1426) = false := by
  decide +kernel

theorem node_context_10_1426_230062 : EJMOriginalGlobalDAGData.nodes 11 ⟨230062, by decide⟩ =
    .split (coordinate 10) (![⟨229104, by decide⟩,⟨229385, by decide⟩,⟨229798, by decide⟩,⟨230061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1426_230062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1426 ⟨230062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1426
    ⟨230062, by decide⟩ (by decide) (![⟨229104, by decide⟩,⟨229385, by decide⟩,⟨229798, by decide⟩,⟨230061, by decide⟩]) unmarked_context_10_1426_230062 node_context_10_1426_230062
  intro a
  fin_cases a
  · exact context_11_5704_229104
  · exact context_11_5705_229385
  · exact context_11_5706_229798
  · exact context_11_5707_230061

theorem selected_cut_08099 : selected 8 ⟨230070, by decide⟩
    (prefixPartial 13 91328) = some ⟨13, 2, 0, 230070, 91328, 701, 16384⟩ := by
  decide +kernel

theorem context_13_91328_230070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91328 ⟨230070, by decide⟩ :=
  accepted_of_selected 13 91328 ⟨230070, by decide⟩ ⟨13, 2, 0, 230070, 91328, 701, 16384⟩
    (by decide) selected_cut_08099

theorem selected_cut_08100 : selected 8 ⟨230096, by decide⟩
    (prefixPartial 13 91329) = some ⟨13, 2, 0, 230096, 91329, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_91329_230096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91329 ⟨230096, by decide⟩ :=
  accepted_of_selected 13 91329 ⟨230096, by decide⟩ ⟨13, 2, 0, 230096, 91329, 2229, 16384⟩
    (by decide) selected_cut_08100

theorem selected_cut_08101 : selected 8 ⟨230115, by decide⟩
    (prefixPartial 13 91330) = some ⟨13, 2, 0, 230115, 91330, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_91330_230115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91330 ⟨230115, by decide⟩ :=
  accepted_of_selected 13 91330 ⟨230115, by decide⟩ ⟨13, 2, 0, 230115, 91330, 1513, 16384⟩
    (by decide) selected_cut_08101

theorem selected_cut_08102 : selected 8 ⟨230119, by decide⟩
    (prefixPartial 13 91331) = some ⟨13, 2, 0, 230119, 91331, 857, 16384⟩ := by
  decide +kernel

theorem context_13_91331_230119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91331 ⟨230119, by decide⟩ :=
  accepted_of_selected 13 91331 ⟨230119, by decide⟩ ⟨13, 2, 0, 230119, 91331, 857, 16384⟩
    (by decide) selected_cut_08102

theorem unmarked_context_12_22832_230120 : frontier 9 ⟨230120, by decide⟩
    (prefixCache 12 22832) (prefixPartial 12 22832) = false := by
  decide +kernel

theorem node_context_12_22832_230120 : EJMOriginalGlobalDAGData.nodes 9 ⟨230120, by decide⟩ =
    .split (coordinate 12) (![⟨230070, by decide⟩,⟨230096, by decide⟩,⟨230115, by decide⟩,⟨230119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22832_230120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22832 ⟨230120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22832
    ⟨230120, by decide⟩ (by decide) (![⟨230070, by decide⟩,⟨230096, by decide⟩,⟨230115, by decide⟩,⟨230119, by decide⟩]) unmarked_context_12_22832_230120 node_context_12_22832_230120
  intro a
  fin_cases a
  · exact context_13_91328_230070
  · exact context_13_91329_230096
  · exact context_13_91330_230115
  · exact context_13_91331_230119

theorem selected_cut_08103 : selected 8 ⟨230127, by decide⟩
    (prefixPartial 13 91332) = some ⟨13, 2, 0, 230127, 91332, 665, 16384⟩ := by
  decide +kernel

theorem context_13_91332_230127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91332 ⟨230127, by decide⟩ :=
  accepted_of_selected 13 91332 ⟨230127, by decide⟩ ⟨13, 2, 0, 230127, 91332, 665, 16384⟩
    (by decide) selected_cut_08103

theorem selected_cut_08104 : selected 8 ⟨230150, by decide⟩
    (prefixPartial 13 91333) = some ⟨13, 2, 0, 230150, 91333, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_91333_230150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91333 ⟨230150, by decide⟩ :=
  accepted_of_selected 13 91333 ⟨230150, by decide⟩ ⟨13, 2, 0, 230150, 91333, 1873, 16384⟩
    (by decide) selected_cut_08104

theorem selected_cut_08105 : selected 8 ⟨230170, by decide⟩
    (prefixPartial 13 91334) = some ⟨13, 2, 0, 230170, 91334, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_91334_230170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91334 ⟨230170, by decide⟩ :=
  accepted_of_selected 13 91334 ⟨230170, by decide⟩ ⟨13, 2, 0, 230170, 91334, 1581, 16384⟩
    (by decide) selected_cut_08105

theorem selected_cut_08106 : selected 8 ⟨230176, by decide⟩
    (prefixPartial 13 91335) = some ⟨13, 2, 0, 230176, 91335, 881, 16384⟩ := by
  decide +kernel

theorem context_13_91335_230176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91335 ⟨230176, by decide⟩ :=
  accepted_of_selected 13 91335 ⟨230176, by decide⟩ ⟨13, 2, 0, 230176, 91335, 881, 16384⟩
    (by decide) selected_cut_08106

theorem unmarked_context_12_22833_230177 : frontier 9 ⟨230177, by decide⟩
    (prefixCache 12 22833) (prefixPartial 12 22833) = false := by
  decide +kernel

theorem node_context_12_22833_230177 : EJMOriginalGlobalDAGData.nodes 9 ⟨230177, by decide⟩ =
    .split (coordinate 12) (![⟨230127, by decide⟩,⟨230150, by decide⟩,⟨230170, by decide⟩,⟨230176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22833_230177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22833 ⟨230177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22833
    ⟨230177, by decide⟩ (by decide) (![⟨230127, by decide⟩,⟨230150, by decide⟩,⟨230170, by decide⟩,⟨230176, by decide⟩]) unmarked_context_12_22833_230177 node_context_12_22833_230177
  intro a
  fin_cases a
  · exact context_13_91332_230127
  · exact context_13_91333_230150
  · exact context_13_91334_230170
  · exact context_13_91335_230176

theorem selected_cut_08107 : selected 8 ⟨230187, by decide⟩
    (prefixPartial 13 91336) = some ⟨13, 2, 0, 230187, 91336, 829, 16384⟩ := by
  decide +kernel

theorem context_13_91336_230187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91336 ⟨230187, by decide⟩ :=
  accepted_of_selected 13 91336 ⟨230187, by decide⟩ ⟨13, 2, 0, 230187, 91336, 829, 16384⟩
    (by decide) selected_cut_08107

theorem selected_cut_08108 : selected 8 ⟨230229, by decide⟩
    (prefixPartial 13 91337) = some ⟨13, 2, 0, 230229, 91337, 2845, 16384⟩ := by
  decide +kernel

theorem context_13_91337_230229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91337 ⟨230229, by decide⟩ :=
  accepted_of_selected 13 91337 ⟨230229, by decide⟩ ⟨13, 2, 0, 230229, 91337, 2845, 16384⟩
    (by decide) selected_cut_08108

theorem selected_cut_08109 : selected 8 ⟨230257, by decide⟩
    (prefixPartial 13 91338) = some ⟨13, 2, 0, 230257, 91338, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_91338_230257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91338 ⟨230257, by decide⟩ :=
  accepted_of_selected 13 91338 ⟨230257, by decide⟩ ⟨13, 2, 0, 230257, 91338, 2105, 16384⟩
    (by decide) selected_cut_08109

theorem selected_cut_08110 : selected 8 ⟨230267, by decide⟩
    (prefixPartial 13 91339) = some ⟨13, 2, 0, 230267, 91339, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_91339_230267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91339 ⟨230267, by decide⟩ :=
  accepted_of_selected 13 91339 ⟨230267, by decide⟩ ⟨13, 2, 0, 230267, 91339, 1017, 16384⟩
    (by decide) selected_cut_08110

theorem unmarked_context_12_22834_230268 : frontier 9 ⟨230268, by decide⟩
    (prefixCache 12 22834) (prefixPartial 12 22834) = false := by
  decide +kernel

theorem node_context_12_22834_230268 : EJMOriginalGlobalDAGData.nodes 9 ⟨230268, by decide⟩ =
    .split (coordinate 12) (![⟨230187, by decide⟩,⟨230229, by decide⟩,⟨230257, by decide⟩,⟨230267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22834_230268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22834 ⟨230268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22834
    ⟨230268, by decide⟩ (by decide) (![⟨230187, by decide⟩,⟨230229, by decide⟩,⟨230257, by decide⟩,⟨230267, by decide⟩]) unmarked_context_12_22834_230268 node_context_12_22834_230268
  intro a
  fin_cases a
  · exact context_13_91336_230187
  · exact context_13_91337_230229
  · exact context_13_91338_230257
  · exact context_13_91339_230267

theorem selected_cut_08111 : selected 8 ⟨230286, by decide⟩
    (prefixPartial 13 91340) = some ⟨13, 2, 0, 230286, 91340, 949, 16384⟩ := by
  decide +kernel

theorem context_13_91340_230286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91340 ⟨230286, by decide⟩ :=
  accepted_of_selected 13 91340 ⟨230286, by decide⟩ ⟨13, 2, 0, 230286, 91340, 949, 16384⟩
    (by decide) selected_cut_08111

theorem selected_cut_08112 : selected 8 ⟨230324, by decide⟩
    (prefixPartial 13 91341) = some ⟨13, 2, 0, 230324, 91341, 3037, 16384⟩ := by
  decide +kernel

theorem context_13_91341_230324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91341 ⟨230324, by decide⟩ :=
  accepted_of_selected 13 91341 ⟨230324, by decide⟩ ⟨13, 2, 0, 230324, 91341, 3037, 16384⟩
    (by decide) selected_cut_08112

theorem selected_cut_08113 : selected 8 ⟨230347, by decide⟩
    (prefixPartial 13 91342) = some ⟨13, 2, 0, 230347, 91342, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_91342_230347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91342 ⟨230347, by decide⟩ :=
  accepted_of_selected 13 91342 ⟨230347, by decide⟩ ⟨13, 2, 0, 230347, 91342, 2073, 16384⟩
    (by decide) selected_cut_08113

theorem selected_cut_08114 : selected 8 ⟨230354, by decide⟩
    (prefixPartial 13 91343) = some ⟨13, 2, 0, 230354, 91343, 981, 16384⟩ := by
  decide +kernel

theorem context_13_91343_230354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91343 ⟨230354, by decide⟩ :=
  accepted_of_selected 13 91343 ⟨230354, by decide⟩ ⟨13, 2, 0, 230354, 91343, 981, 16384⟩
    (by decide) selected_cut_08114

theorem unmarked_context_12_22835_230355 : frontier 9 ⟨230355, by decide⟩
    (prefixCache 12 22835) (prefixPartial 12 22835) = false := by
  decide +kernel

theorem node_context_12_22835_230355 : EJMOriginalGlobalDAGData.nodes 9 ⟨230355, by decide⟩ =
    .split (coordinate 12) (![⟨230286, by decide⟩,⟨230324, by decide⟩,⟨230347, by decide⟩,⟨230354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22835_230355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22835 ⟨230355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22835
    ⟨230355, by decide⟩ (by decide) (![⟨230286, by decide⟩,⟨230324, by decide⟩,⟨230347, by decide⟩,⟨230354, by decide⟩]) unmarked_context_12_22835_230355 node_context_12_22835_230355
  intro a
  fin_cases a
  · exact context_13_91340_230286
  · exact context_13_91341_230324
  · exact context_13_91342_230347
  · exact context_13_91343_230354

theorem unmarked_context_11_5708_230356 : frontier 10 ⟨230356, by decide⟩
    (prefixCache 11 5708) (prefixPartial 11 5708) = false := by
  decide +kernel

theorem node_context_11_5708_230356 : EJMOriginalGlobalDAGData.nodes 10 ⟨230356, by decide⟩ =
    .split (coordinate 11) (![⟨230120, by decide⟩,⟨230177, by decide⟩,⟨230268, by decide⟩,⟨230355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5708_230356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5708 ⟨230356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5708
    ⟨230356, by decide⟩ (by decide) (![⟨230120, by decide⟩,⟨230177, by decide⟩,⟨230268, by decide⟩,⟨230355, by decide⟩]) unmarked_context_11_5708_230356 node_context_11_5708_230356
  intro a
  fin_cases a
  · exact context_12_22832_230120
  · exact context_12_22833_230177
  · exact context_12_22834_230268
  · exact context_12_22835_230355

theorem selected_cut_08115 : selected 8 ⟨230364, by decide⟩
    (prefixPartial 13 91344) = some ⟨13, 2, 0, 230364, 91344, 409, 16384⟩ := by
  decide +kernel

theorem context_13_91344_230364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91344 ⟨230364, by decide⟩ :=
  accepted_of_selected 13 91344 ⟨230364, by decide⟩ ⟨13, 2, 0, 230364, 91344, 409, 16384⟩
    (by decide) selected_cut_08115

theorem selected_cut_08116 : selected 8 ⟨230388, by decide⟩
    (prefixPartial 13 91345) = some ⟨13, 2, 0, 230388, 91345, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_91345_230388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91345 ⟨230388, by decide⟩ :=
  accepted_of_selected 13 91345 ⟨230388, by decide⟩ ⟨13, 2, 0, 230388, 91345, 2033, 16384⟩
    (by decide) selected_cut_08116

theorem selected_cut_08117 : selected 8 ⟨230406, by decide⟩
    (prefixPartial 13 91346) = some ⟨13, 2, 0, 230406, 91346, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_91346_230406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91346 ⟨230406, by decide⟩ :=
  accepted_of_selected 13 91346 ⟨230406, by decide⟩ ⟨13, 2, 0, 230406, 91346, 1241, 16384⟩
    (by decide) selected_cut_08117

theorem selected_cut_08118 : selected 8 ⟨230413, by decide⟩
    (prefixPartial 13 91347) = some ⟨13, 2, 0, 230413, 91347, 829, 16384⟩ := by
  decide +kernel

theorem context_13_91347_230413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91347 ⟨230413, by decide⟩ :=
  accepted_of_selected 13 91347 ⟨230413, by decide⟩ ⟨13, 2, 0, 230413, 91347, 829, 16384⟩
    (by decide) selected_cut_08118

theorem unmarked_context_12_22836_230414 : frontier 9 ⟨230414, by decide⟩
    (prefixCache 12 22836) (prefixPartial 12 22836) = false := by
  decide +kernel

theorem node_context_12_22836_230414 : EJMOriginalGlobalDAGData.nodes 9 ⟨230414, by decide⟩ =
    .split (coordinate 12) (![⟨230364, by decide⟩,⟨230388, by decide⟩,⟨230406, by decide⟩,⟨230413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22836_230414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22836 ⟨230414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22836
    ⟨230414, by decide⟩ (by decide) (![⟨230364, by decide⟩,⟨230388, by decide⟩,⟨230406, by decide⟩,⟨230413, by decide⟩]) unmarked_context_12_22836_230414 node_context_12_22836_230414
  intro a
  fin_cases a
  · exact context_13_91344_230364
  · exact context_13_91345_230388
  · exact context_13_91346_230406
  · exact context_13_91347_230413

theorem selected_cut_08119 : selected 8 ⟨230425, by decide⟩
    (prefixPartial 13 91348) = some ⟨13, 2, 0, 230425, 91348, 669, 16384⟩ := by
  decide +kernel

theorem context_13_91348_230425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91348 ⟨230425, by decide⟩ :=
  accepted_of_selected 13 91348 ⟨230425, by decide⟩ ⟨13, 2, 0, 230425, 91348, 669, 16384⟩
    (by decide) selected_cut_08119

theorem selected_cut_08120 : selected 8 ⟨230457, by decide⟩
    (prefixPartial 13 91349) = some ⟨13, 2, 0, 230457, 91349, 3013, 16384⟩ := by
  decide +kernel

theorem context_13_91349_230457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91349 ⟨230457, by decide⟩ :=
  accepted_of_selected 13 91349 ⟨230457, by decide⟩ ⟨13, 2, 0, 230457, 91349, 3013, 16384⟩
    (by decide) selected_cut_08120

theorem selected_cut_08121 : selected 8 ⟨230474, by decide⟩
    (prefixPartial 13 91350) = some ⟨13, 2, 0, 230474, 91350, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_91350_230474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91350 ⟨230474, by decide⟩ :=
  accepted_of_selected 13 91350 ⟨230474, by decide⟩ ⟨13, 2, 0, 230474, 91350, 1901, 16384⟩
    (by decide) selected_cut_08121

theorem selected_cut_08122 : selected 8 ⟨230482, by decide⟩
    (prefixPartial 13 91351) = some ⟨13, 2, 0, 230482, 91351, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_91351_230482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91351 ⟨230482, by decide⟩ :=
  accepted_of_selected 13 91351 ⟨230482, by decide⟩ ⟨13, 2, 0, 230482, 91351, 1113, 16384⟩
    (by decide) selected_cut_08122

theorem unmarked_context_12_22837_230483 : frontier 9 ⟨230483, by decide⟩
    (prefixCache 12 22837) (prefixPartial 12 22837) = false := by
  decide +kernel

theorem node_context_12_22837_230483 : EJMOriginalGlobalDAGData.nodes 9 ⟨230483, by decide⟩ =
    .split (coordinate 12) (![⟨230425, by decide⟩,⟨230457, by decide⟩,⟨230474, by decide⟩,⟨230482, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22837_230483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22837 ⟨230483, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22837
    ⟨230483, by decide⟩ (by decide) (![⟨230425, by decide⟩,⟨230457, by decide⟩,⟨230474, by decide⟩,⟨230482, by decide⟩]) unmarked_context_12_22837_230483 node_context_12_22837_230483
  intro a
  fin_cases a
  · exact context_13_91348_230425
  · exact context_13_91349_230457
  · exact context_13_91350_230474
  · exact context_13_91351_230482

theorem selected_cut_08123 : selected 8 ⟨230489, by decide⟩
    (prefixPartial 13 91352) = some ⟨13, 2, 0, 230489, 91352, 445, 16384⟩ := by
  decide +kernel

theorem context_13_91352_230489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91352 ⟨230489, by decide⟩ :=
  accepted_of_selected 13 91352 ⟨230489, by decide⟩ ⟨13, 2, 0, 230489, 91352, 445, 16384⟩
    (by decide) selected_cut_08123

theorem selected_cut_08124 : selected 8 ⟨230513, by decide⟩
    (prefixPartial 13 91353) = some ⟨13, 2, 0, 230513, 91353, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_91353_230513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91353 ⟨230513, by decide⟩ :=
  accepted_of_selected 13 91353 ⟨230513, by decide⟩ ⟨13, 2, 0, 230513, 91353, 2365, 16384⟩
    (by decide) selected_cut_08124

theorem selected_cut_08125 : selected 8 ⟨230533, by decide⟩
    (prefixPartial 13 91354) = some ⟨13, 2, 0, 230533, 91354, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_91354_230533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91354 ⟨230533, by decide⟩ :=
  accepted_of_selected 13 91354 ⟨230533, by decide⟩ ⟨13, 2, 0, 230533, 91354, 1573, 16384⟩
    (by decide) selected_cut_08125

theorem selected_cut_08126 : selected 8 ⟨230540, by decide⟩
    (prefixPartial 13 91355) = some ⟨13, 2, 0, 230540, 91355, 873, 16384⟩ := by
  decide +kernel

theorem context_13_91355_230540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91355 ⟨230540, by decide⟩ :=
  accepted_of_selected 13 91355 ⟨230540, by decide⟩ ⟨13, 2, 0, 230540, 91355, 873, 16384⟩
    (by decide) selected_cut_08126

theorem unmarked_context_12_22838_230541 : frontier 9 ⟨230541, by decide⟩
    (prefixCache 12 22838) (prefixPartial 12 22838) = false := by
  decide +kernel

theorem node_context_12_22838_230541 : EJMOriginalGlobalDAGData.nodes 9 ⟨230541, by decide⟩ =
    .split (coordinate 12) (![⟨230489, by decide⟩,⟨230513, by decide⟩,⟨230533, by decide⟩,⟨230540, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22838_230541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22838 ⟨230541, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22838
    ⟨230541, by decide⟩ (by decide) (![⟨230489, by decide⟩,⟨230513, by decide⟩,⟨230533, by decide⟩,⟨230540, by decide⟩]) unmarked_context_12_22838_230541 node_context_12_22838_230541
  intro a
  fin_cases a
  · exact context_13_91352_230489
  · exact context_13_91353_230513
  · exact context_13_91354_230533
  · exact context_13_91355_230540

theorem selected_cut_08127 : selected 8 ⟨230549, by decide⟩
    (prefixPartial 13 91356) = some ⟨13, 2, 0, 230549, 91356, 497, 16384⟩ := by
  decide +kernel

theorem context_13_91356_230549 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91356 ⟨230549, by decide⟩ :=
  accepted_of_selected 13 91356 ⟨230549, by decide⟩ ⟨13, 2, 0, 230549, 91356, 497, 16384⟩
    (by decide) selected_cut_08127

theorem selected_cut_08128 : selected 8 ⟨230580, by decide⟩
    (prefixPartial 13 91357) = some ⟨13, 2, 0, 230580, 91357, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_91357_230580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91357 ⟨230580, by decide⟩ :=
  accepted_of_selected 13 91357 ⟨230580, by decide⟩ ⟨13, 2, 0, 230580, 91357, 2429, 16384⟩
    (by decide) selected_cut_08128

theorem selected_cut_08129 : selected 8 ⟨230599, by decide⟩
    (prefixPartial 13 91358) = some ⟨13, 2, 0, 230599, 91358, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_91358_230599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91358 ⟨230599, by decide⟩ :=
  accepted_of_selected 13 91358 ⟨230599, by decide⟩ ⟨13, 2, 0, 230599, 91358, 1561, 16384⟩
    (by decide) selected_cut_08129

theorem selected_cut_08130 : selected 8 ⟨230607, by decide⟩
    (prefixPartial 13 91359) = some ⟨13, 2, 0, 230607, 91359, 853, 16384⟩ := by
  decide +kernel

theorem context_13_91359_230607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91359 ⟨230607, by decide⟩ :=
  accepted_of_selected 13 91359 ⟨230607, by decide⟩ ⟨13, 2, 0, 230607, 91359, 853, 16384⟩
    (by decide) selected_cut_08130

theorem unmarked_context_12_22839_230608 : frontier 9 ⟨230608, by decide⟩
    (prefixCache 12 22839) (prefixPartial 12 22839) = false := by
  decide +kernel

theorem node_context_12_22839_230608 : EJMOriginalGlobalDAGData.nodes 9 ⟨230608, by decide⟩ =
    .split (coordinate 12) (![⟨230549, by decide⟩,⟨230580, by decide⟩,⟨230599, by decide⟩,⟨230607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22839_230608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22839 ⟨230608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22839
    ⟨230608, by decide⟩ (by decide) (![⟨230549, by decide⟩,⟨230580, by decide⟩,⟨230599, by decide⟩,⟨230607, by decide⟩]) unmarked_context_12_22839_230608 node_context_12_22839_230608
  intro a
  fin_cases a
  · exact context_13_91356_230549
  · exact context_13_91357_230580
  · exact context_13_91358_230599
  · exact context_13_91359_230607

theorem unmarked_context_11_5709_230609 : frontier 10 ⟨230609, by decide⟩
    (prefixCache 11 5709) (prefixPartial 11 5709) = false := by
  decide +kernel

theorem node_context_11_5709_230609 : EJMOriginalGlobalDAGData.nodes 10 ⟨230609, by decide⟩ =
    .split (coordinate 11) (![⟨230414, by decide⟩,⟨230483, by decide⟩,⟨230541, by decide⟩,⟨230608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5709_230609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5709 ⟨230609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5709
    ⟨230609, by decide⟩ (by decide) (![⟨230414, by decide⟩,⟨230483, by decide⟩,⟨230541, by decide⟩,⟨230608, by decide⟩]) unmarked_context_11_5709_230609 node_context_11_5709_230609
  intro a
  fin_cases a
  · exact context_12_22836_230414
  · exact context_12_22837_230483
  · exact context_12_22838_230541
  · exact context_12_22839_230608

theorem selected_cut_08131 : selected 8 ⟨230614, by decide⟩
    (prefixPartial 13 91360) = some ⟨13, 2, 0, 230614, 91360, 349, 16384⟩ := by
  decide +kernel

theorem context_13_91360_230614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91360 ⟨230614, by decide⟩ :=
  accepted_of_selected 13 91360 ⟨230614, by decide⟩ ⟨13, 2, 0, 230614, 91360, 349, 16384⟩
    (by decide) selected_cut_08131

theorem selected_cut_08132 : selected 8 ⟨230640, by decide⟩
    (prefixPartial 13 91361) = some ⟨13, 2, 0, 230640, 91361, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_91361_230640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91361 ⟨230640, by decide⟩ :=
  accepted_of_selected 13 91361 ⟨230640, by decide⟩ ⟨13, 2, 0, 230640, 91361, 2501, 16384⟩
    (by decide) selected_cut_08132

theorem selected_cut_08133 : selected 8 ⟨230664, by decide⟩
    (prefixPartial 13 91362) = some ⟨13, 2, 0, 230664, 91362, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_91362_230664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91362 ⟨230664, by decide⟩ :=
  accepted_of_selected 13 91362 ⟨230664, by decide⟩ ⟨13, 2, 0, 230664, 91362, 1765, 16384⟩
    (by decide) selected_cut_08133

theorem selected_cut_08134 : selected 8 ⟨230672, by decide⟩
    (prefixPartial 13 91363) = some ⟨13, 2, 0, 230672, 91363, 921, 16384⟩ := by
  decide +kernel

theorem context_13_91363_230672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91363 ⟨230672, by decide⟩ :=
  accepted_of_selected 13 91363 ⟨230672, by decide⟩ ⟨13, 2, 0, 230672, 91363, 921, 16384⟩
    (by decide) selected_cut_08134

theorem unmarked_context_12_22840_230673 : frontier 9 ⟨230673, by decide⟩
    (prefixCache 12 22840) (prefixPartial 12 22840) = false := by
  decide +kernel

theorem node_context_12_22840_230673 : EJMOriginalGlobalDAGData.nodes 9 ⟨230673, by decide⟩ =
    .split (coordinate 12) (![⟨230614, by decide⟩,⟨230640, by decide⟩,⟨230664, by decide⟩,⟨230672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22840_230673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22840 ⟨230673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22840
    ⟨230673, by decide⟩ (by decide) (![⟨230614, by decide⟩,⟨230640, by decide⟩,⟨230664, by decide⟩,⟨230672, by decide⟩]) unmarked_context_12_22840_230673 node_context_12_22840_230673
  intro a
  fin_cases a
  · exact context_13_91360_230614
  · exact context_13_91361_230640
  · exact context_13_91362_230664
  · exact context_13_91363_230672

theorem selected_cut_08135 : selected 8 ⟨230678, by decide⟩
    (prefixPartial 13 91364) = some ⟨13, 2, 0, 230678, 91364, 361, 16384⟩ := by
  decide +kernel

theorem context_13_91364_230678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91364 ⟨230678, by decide⟩ :=
  accepted_of_selected 13 91364 ⟨230678, by decide⟩ ⟨13, 2, 0, 230678, 91364, 361, 16384⟩
    (by decide) selected_cut_08135

theorem selected_cut_08136 : selected 8 ⟨230703, by decide⟩
    (prefixPartial 13 91365) = some ⟨13, 2, 0, 230703, 91365, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_91365_230703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91365 ⟨230703, by decide⟩ :=
  accepted_of_selected 13 91365 ⟨230703, by decide⟩ ⟨13, 2, 0, 230703, 91365, 2045, 16384⟩
    (by decide) selected_cut_08136

theorem selected_cut_08137 : selected 8 ⟨230723, by decide⟩
    (prefixPartial 13 91366) = some ⟨13, 2, 0, 230723, 91366, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_91366_230723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91366 ⟨230723, by decide⟩ :=
  accepted_of_selected 13 91366 ⟨230723, by decide⟩ ⟨13, 2, 0, 230723, 91366, 1673, 16384⟩
    (by decide) selected_cut_08137

theorem selected_cut_08138 : selected 8 ⟨230729, by decide⟩
    (prefixPartial 13 91367) = some ⟨13, 2, 0, 230729, 91367, 897, 16384⟩ := by
  decide +kernel

theorem context_13_91367_230729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91367 ⟨230729, by decide⟩ :=
  accepted_of_selected 13 91367 ⟨230729, by decide⟩ ⟨13, 2, 0, 230729, 91367, 897, 16384⟩
    (by decide) selected_cut_08138

theorem unmarked_context_12_22841_230730 : frontier 9 ⟨230730, by decide⟩
    (prefixCache 12 22841) (prefixPartial 12 22841) = false := by
  decide +kernel

theorem node_context_12_22841_230730 : EJMOriginalGlobalDAGData.nodes 9 ⟨230730, by decide⟩ =
    .split (coordinate 12) (![⟨230678, by decide⟩,⟨230703, by decide⟩,⟨230723, by decide⟩,⟨230729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22841_230730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22841 ⟨230730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22841
    ⟨230730, by decide⟩ (by decide) (![⟨230678, by decide⟩,⟨230703, by decide⟩,⟨230723, by decide⟩,⟨230729, by decide⟩]) unmarked_context_12_22841_230730 node_context_12_22841_230730
  intro a
  fin_cases a
  · exact context_13_91364_230678
  · exact context_13_91365_230703
  · exact context_13_91366_230723
  · exact context_13_91367_230729

theorem selected_cut_08139 : selected 8 ⟨230735, by decide⟩
    (prefixPartial 13 91368) = some ⟨13, 2, 0, 230735, 91368, 337, 16384⟩ := by
  decide +kernel

theorem context_13_91368_230735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91368 ⟨230735, by decide⟩ :=
  accepted_of_selected 13 91368 ⟨230735, by decide⟩ ⟨13, 2, 0, 230735, 91368, 337, 16384⟩
    (by decide) selected_cut_08139

theorem selected_cut_08140 : selected 8 ⟨230769, by decide⟩
    (prefixPartial 13 91369) = some ⟨13, 2, 0, 230769, 91369, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_91369_230769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91369 ⟨230769, by decide⟩ :=
  accepted_of_selected 13 91369 ⟨230769, by decide⟩ ⟨13, 2, 0, 230769, 91369, 2849, 16384⟩
    (by decide) selected_cut_08140

theorem selected_cut_08141 : selected 8 ⟨230793, by decide⟩
    (prefixPartial 13 91370) = some ⟨13, 2, 0, 230793, 91370, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_91370_230793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91370 ⟨230793, by decide⟩ :=
  accepted_of_selected 13 91370 ⟨230793, by decide⟩ ⟨13, 2, 0, 230793, 91370, 2113, 16384⟩
    (by decide) selected_cut_08141

theorem selected_cut_08142 : selected 8 ⟨230801, by decide⟩
    (prefixPartial 13 91371) = some ⟨13, 2, 0, 230801, 91371, 969, 16384⟩ := by
  decide +kernel

theorem context_13_91371_230801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91371 ⟨230801, by decide⟩ :=
  accepted_of_selected 13 91371 ⟨230801, by decide⟩ ⟨13, 2, 0, 230801, 91371, 969, 16384⟩
    (by decide) selected_cut_08142

theorem unmarked_context_12_22842_230802 : frontier 9 ⟨230802, by decide⟩
    (prefixCache 12 22842) (prefixPartial 12 22842) = false := by
  decide +kernel

theorem node_context_12_22842_230802 : EJMOriginalGlobalDAGData.nodes 9 ⟨230802, by decide⟩ =
    .split (coordinate 12) (![⟨230735, by decide⟩,⟨230769, by decide⟩,⟨230793, by decide⟩,⟨230801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22842_230802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22842 ⟨230802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22842
    ⟨230802, by decide⟩ (by decide) (![⟨230735, by decide⟩,⟨230769, by decide⟩,⟨230793, by decide⟩,⟨230801, by decide⟩]) unmarked_context_12_22842_230802 node_context_12_22842_230802
  intro a
  fin_cases a
  · exact context_13_91368_230735
  · exact context_13_91369_230769
  · exact context_13_91370_230793
  · exact context_13_91371_230801

theorem selected_cut_08143 : selected 8 ⟨230809, by decide⟩
    (prefixPartial 13 91372) = some ⟨13, 2, 0, 230809, 91372, 349, 16384⟩ := by
  decide +kernel

theorem context_13_91372_230809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91372 ⟨230809, by decide⟩ :=
  accepted_of_selected 13 91372 ⟨230809, by decide⟩ ⟨13, 2, 0, 230809, 91372, 349, 16384⟩
    (by decide) selected_cut_08143

theorem selected_cut_08144 : selected 8 ⟨230845, by decide⟩
    (prefixPartial 13 91373) = some ⟨13, 2, 0, 230845, 91373, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_91373_230845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91373 ⟨230845, by decide⟩ :=
  accepted_of_selected 13 91373 ⟨230845, by decide⟩ ⟨13, 2, 0, 230845, 91373, 3021, 16384⟩
    (by decide) selected_cut_08144

theorem selected_cut_08145 : selected 8 ⟨230870, by decide⟩
    (prefixPartial 13 91374) = some ⟨13, 2, 0, 230870, 91374, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_91374_230870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91374 ⟨230870, by decide⟩ :=
  accepted_of_selected 13 91374 ⟨230870, by decide⟩ ⟨13, 2, 0, 230870, 91374, 2089, 16384⟩
    (by decide) selected_cut_08145

theorem selected_cut_08146 : selected 8 ⟨230877, by decide⟩
    (prefixPartial 13 91375) = some ⟨13, 2, 0, 230877, 91375, 997, 16384⟩ := by
  decide +kernel

theorem context_13_91375_230877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91375 ⟨230877, by decide⟩ :=
  accepted_of_selected 13 91375 ⟨230877, by decide⟩ ⟨13, 2, 0, 230877, 91375, 997, 16384⟩
    (by decide) selected_cut_08146

theorem unmarked_context_12_22843_230878 : frontier 9 ⟨230878, by decide⟩
    (prefixCache 12 22843) (prefixPartial 12 22843) = false := by
  decide +kernel

theorem node_context_12_22843_230878 : EJMOriginalGlobalDAGData.nodes 9 ⟨230878, by decide⟩ =
    .split (coordinate 12) (![⟨230809, by decide⟩,⟨230845, by decide⟩,⟨230870, by decide⟩,⟨230877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22843_230878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22843 ⟨230878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22843
    ⟨230878, by decide⟩ (by decide) (![⟨230809, by decide⟩,⟨230845, by decide⟩,⟨230870, by decide⟩,⟨230877, by decide⟩]) unmarked_context_12_22843_230878 node_context_12_22843_230878
  intro a
  fin_cases a
  · exact context_13_91372_230809
  · exact context_13_91373_230845
  · exact context_13_91374_230870
  · exact context_13_91375_230877

theorem unmarked_context_11_5710_230879 : frontier 10 ⟨230879, by decide⟩
    (prefixCache 11 5710) (prefixPartial 11 5710) = false := by
  decide +kernel

theorem node_context_11_5710_230879 : EJMOriginalGlobalDAGData.nodes 10 ⟨230879, by decide⟩ =
    .split (coordinate 11) (![⟨230673, by decide⟩,⟨230730, by decide⟩,⟨230802, by decide⟩,⟨230878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5710_230879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5710 ⟨230879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5710
    ⟨230879, by decide⟩ (by decide) (![⟨230673, by decide⟩,⟨230730, by decide⟩,⟨230802, by decide⟩,⟨230878, by decide⟩]) unmarked_context_11_5710_230879 node_context_11_5710_230879
  intro a
  fin_cases a
  · exact context_12_22840_230673
  · exact context_12_22841_230730
  · exact context_12_22842_230802
  · exact context_12_22843_230878

theorem selected_cut_08147 : selected 8 ⟨230882, by decide⟩
    (prefixPartial 13 91376) = some ⟨13, 2, 0, 230882, 91376, 129, 16384⟩ := by
  decide +kernel

theorem context_13_91376_230882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91376 ⟨230882, by decide⟩ :=
  accepted_of_selected 13 91376 ⟨230882, by decide⟩ ⟨13, 2, 0, 230882, 91376, 129, 16384⟩
    (by decide) selected_cut_08147

theorem selected_cut_08148 : selected 8 ⟨230907, by decide⟩
    (prefixPartial 13 91377) = some ⟨13, 2, 0, 230907, 91377, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_91377_230907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91377 ⟨230907, by decide⟩ :=
  accepted_of_selected 13 91377 ⟨230907, by decide⟩ ⟨13, 2, 0, 230907, 91377, 2297, 16384⟩
    (by decide) selected_cut_08148

theorem selected_cut_08149 : selected 8 ⟨230923, by decide⟩
    (prefixPartial 13 91378) = some ⟨13, 2, 0, 230923, 91378, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_91378_230923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91378 ⟨230923, by decide⟩ :=
  accepted_of_selected 13 91378 ⟨230923, by decide⟩ ⟨13, 2, 0, 230923, 91378, 1437, 16384⟩
    (by decide) selected_cut_08149

theorem selected_cut_08150 : selected 8 ⟨230930, by decide⟩
    (prefixPartial 13 91379) = some ⟨13, 2, 0, 230930, 91379, 913, 16384⟩ := by
  decide +kernel

theorem context_13_91379_230930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91379 ⟨230930, by decide⟩ :=
  accepted_of_selected 13 91379 ⟨230930, by decide⟩ ⟨13, 2, 0, 230930, 91379, 913, 16384⟩
    (by decide) selected_cut_08150

theorem unmarked_context_12_22844_230931 : frontier 9 ⟨230931, by decide⟩
    (prefixCache 12 22844) (prefixPartial 12 22844) = false := by
  decide +kernel

theorem node_context_12_22844_230931 : EJMOriginalGlobalDAGData.nodes 9 ⟨230931, by decide⟩ =
    .split (coordinate 12) (![⟨230882, by decide⟩,⟨230907, by decide⟩,⟨230923, by decide⟩,⟨230930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22844_230931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22844 ⟨230931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22844
    ⟨230931, by decide⟩ (by decide) (![⟨230882, by decide⟩,⟨230907, by decide⟩,⟨230923, by decide⟩,⟨230930, by decide⟩]) unmarked_context_12_22844_230931 node_context_12_22844_230931
  intro a
  fin_cases a
  · exact context_13_91376_230882
  · exact context_13_91377_230907
  · exact context_13_91378_230923
  · exact context_13_91379_230930

theorem selected_cut_08151 : selected 8 ⟨230934, by decide⟩
    (prefixPartial 13 91380) = some ⟨13, 2, 0, 230934, 91380, 113, 16384⟩ := by
  decide +kernel

theorem context_13_91380_230934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91380 ⟨230934, by decide⟩ :=
  accepted_of_selected 13 91380 ⟨230934, by decide⟩ ⟨13, 2, 0, 230934, 91380, 113, 16384⟩
    (by decide) selected_cut_08151

theorem selected_cut_08152 : selected 8 ⟨230954, by decide⟩
    (prefixPartial 13 91381) = some ⟨13, 2, 0, 230954, 91381, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_91381_230954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91381 ⟨230954, by decide⟩ :=
  accepted_of_selected 13 91381 ⟨230954, by decide⟩ ⟨13, 2, 0, 230954, 91381, 1917, 16384⟩
    (by decide) selected_cut_08152

theorem selected_cut_08153 : selected 8 ⟨230970, by decide⟩
    (prefixPartial 13 91382) = some ⟨13, 2, 0, 230970, 91382, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_91382_230970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91382 ⟨230970, by decide⟩ :=
  accepted_of_selected 13 91382 ⟨230970, by decide⟩ ⟨13, 2, 0, 230970, 91382, 1357, 16384⟩
    (by decide) selected_cut_08153

theorem selected_cut_08154 : selected 8 ⟨230979, by decide⟩
    (prefixPartial 13 91383) = some ⟨13, 2, 0, 230979, 91383, 793, 16384⟩ := by
  decide +kernel

theorem context_13_91383_230979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91383 ⟨230979, by decide⟩ :=
  accepted_of_selected 13 91383 ⟨230979, by decide⟩ ⟨13, 2, 0, 230979, 91383, 793, 16384⟩
    (by decide) selected_cut_08154

theorem unmarked_context_12_22845_230980 : frontier 9 ⟨230980, by decide⟩
    (prefixCache 12 22845) (prefixPartial 12 22845) = false := by
  decide +kernel

theorem node_context_12_22845_230980 : EJMOriginalGlobalDAGData.nodes 9 ⟨230980, by decide⟩ =
    .split (coordinate 12) (![⟨230934, by decide⟩,⟨230954, by decide⟩,⟨230970, by decide⟩,⟨230979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22845_230980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22845 ⟨230980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22845
    ⟨230980, by decide⟩ (by decide) (![⟨230934, by decide⟩,⟨230954, by decide⟩,⟨230970, by decide⟩,⟨230979, by decide⟩]) unmarked_context_12_22845_230980 node_context_12_22845_230980
  intro a
  fin_cases a
  · exact context_13_91380_230934
  · exact context_13_91381_230954
  · exact context_13_91382_230970
  · exact context_13_91383_230979

theorem selected_cut_08155 : selected 8 ⟨230983, by decide⟩
    (prefixPartial 13 91384) = some ⟨13, 2, 0, 230983, 91384, 93, 16384⟩ := by
  decide +kernel

theorem context_13_91384_230983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91384 ⟨230983, by decide⟩ :=
  accepted_of_selected 13 91384 ⟨230983, by decide⟩ ⟨13, 2, 0, 230983, 91384, 93, 16384⟩
    (by decide) selected_cut_08155

theorem selected_cut_08156 : selected 8 ⟨231016, by decide⟩
    (prefixPartial 13 91385) = some ⟨13, 2, 0, 231016, 91385, 2625, 16384⟩ := by
  decide +kernel

theorem context_13_91385_231016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91385 ⟨231016, by decide⟩ :=
  accepted_of_selected 13 91385 ⟨231016, by decide⟩ ⟨13, 2, 0, 231016, 91385, 2625, 16384⟩
    (by decide) selected_cut_08156

theorem selected_cut_08157 : selected 8 ⟨231036, by decide⟩
    (prefixPartial 13 91386) = some ⟨13, 2, 0, 231036, 91386, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_91386_231036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91386 ⟨231036, by decide⟩ :=
  accepted_of_selected 13 91386 ⟨231036, by decide⟩ ⟨13, 2, 0, 231036, 91386, 1741, 16384⟩
    (by decide) selected_cut_08157

theorem selected_cut_08158 : selected 8 ⟨231044, by decide⟩
    (prefixPartial 13 91387) = some ⟨13, 2, 0, 231044, 91387, 881, 16384⟩ := by
  decide +kernel

theorem context_13_91387_231044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91387 ⟨231044, by decide⟩ :=
  accepted_of_selected 13 91387 ⟨231044, by decide⟩ ⟨13, 2, 0, 231044, 91387, 881, 16384⟩
    (by decide) selected_cut_08158

theorem unmarked_context_12_22846_231045 : frontier 9 ⟨231045, by decide⟩
    (prefixCache 12 22846) (prefixPartial 12 22846) = false := by
  decide +kernel

theorem node_context_12_22846_231045 : EJMOriginalGlobalDAGData.nodes 9 ⟨231045, by decide⟩ =
    .split (coordinate 12) (![⟨230983, by decide⟩,⟨231016, by decide⟩,⟨231036, by decide⟩,⟨231044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22846_231045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22846 ⟨231045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22846
    ⟨231045, by decide⟩ (by decide) (![⟨230983, by decide⟩,⟨231016, by decide⟩,⟨231036, by decide⟩,⟨231044, by decide⟩]) unmarked_context_12_22846_231045 node_context_12_22846_231045
  intro a
  fin_cases a
  · exact context_13_91384_230983
  · exact context_13_91385_231016
  · exact context_13_91386_231036
  · exact context_13_91387_231044

theorem selected_cut_08159 : selected 8 ⟨231050, by decide⟩
    (prefixPartial 13 91388) = some ⟨13, 2, 0, 231050, 91388, 85, 16384⟩ := by
  decide +kernel

theorem context_13_91388_231050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91388 ⟨231050, by decide⟩ :=
  accepted_of_selected 13 91388 ⟨231050, by decide⟩ ⟨13, 2, 0, 231050, 91388, 85, 16384⟩
    (by decide) selected_cut_08159

theorem selected_cut_08160 : selected 8 ⟨231077, by decide⟩
    (prefixPartial 13 91389) = some ⟨13, 2, 0, 231077, 91389, 2701, 16384⟩ := by
  decide +kernel

theorem context_13_91389_231077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91389 ⟨231077, by decide⟩ :=
  accepted_of_selected 13 91389 ⟨231077, by decide⟩ ⟨13, 2, 0, 231077, 91389, 2701, 16384⟩
    (by decide) selected_cut_08160

theorem selected_cut_08161 : selected 8 ⟨231097, by decide⟩
    (prefixPartial 13 91390) = some ⟨13, 2, 0, 231097, 91390, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_91390_231097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91390 ⟨231097, by decide⟩ :=
  accepted_of_selected 13 91390 ⟨231097, by decide⟩ ⟨13, 2, 0, 231097, 91390, 1585, 16384⟩
    (by decide) selected_cut_08161

theorem selected_cut_08162 : selected 8 ⟨231103, by decide⟩
    (prefixPartial 13 91391) = some ⟨13, 2, 0, 231103, 91391, 849, 16384⟩ := by
  decide +kernel

theorem context_13_91391_231103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 91391 ⟨231103, by decide⟩ :=
  accepted_of_selected 13 91391 ⟨231103, by decide⟩ ⟨13, 2, 0, 231103, 91391, 849, 16384⟩
    (by decide) selected_cut_08162

theorem unmarked_context_12_22847_231104 : frontier 9 ⟨231104, by decide⟩
    (prefixCache 12 22847) (prefixPartial 12 22847) = false := by
  decide +kernel

theorem node_context_12_22847_231104 : EJMOriginalGlobalDAGData.nodes 9 ⟨231104, by decide⟩ =
    .split (coordinate 12) (![⟨231050, by decide⟩,⟨231077, by decide⟩,⟨231097, by decide⟩,⟨231103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_22847_231104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 22847 ⟨231104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 22847
    ⟨231104, by decide⟩ (by decide) (![⟨231050, by decide⟩,⟨231077, by decide⟩,⟨231097, by decide⟩,⟨231103, by decide⟩]) unmarked_context_12_22847_231104 node_context_12_22847_231104
  intro a
  fin_cases a
  · exact context_13_91388_231050
  · exact context_13_91389_231077
  · exact context_13_91390_231097
  · exact context_13_91391_231103

theorem unmarked_context_11_5711_231105 : frontier 10 ⟨231105, by decide⟩
    (prefixCache 11 5711) (prefixPartial 11 5711) = false := by
  decide +kernel

theorem node_context_11_5711_231105 : EJMOriginalGlobalDAGData.nodes 10 ⟨231105, by decide⟩ =
    .split (coordinate 11) (![⟨230931, by decide⟩,⟨230980, by decide⟩,⟨231045, by decide⟩,⟨231104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_5711_231105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 5711 ⟨231105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 5711
    ⟨231105, by decide⟩ (by decide) (![⟨230931, by decide⟩,⟨230980, by decide⟩,⟨231045, by decide⟩,⟨231104, by decide⟩]) unmarked_context_11_5711_231105 node_context_11_5711_231105
  intro a
  fin_cases a
  · exact context_12_22844_230931
  · exact context_12_22845_230980
  · exact context_12_22846_231045
  · exact context_12_22847_231104

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
