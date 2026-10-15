/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover308
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_29667 : selected 8 ⟨749066, by decide⟩
    (prefixPartial 13 374916) = some ⟨13, 2, 0, 749066, 374916, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_374916_749066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374916 ⟨749066, by decide⟩ :=
  accepted_of_selected 13 374916 ⟨749066, by decide⟩ ⟨13, 2, 0, 749066, 374916, 1277, 16384⟩
    (by decide) selected_cut_29667

theorem selected_cut_29668 : selected 8 ⟨749094, by decide⟩
    (prefixPartial 13 374917) = some ⟨13, 2, 0, 749094, 374917, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_374917_749094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374917 ⟨749094, by decide⟩ :=
  accepted_of_selected 13 374917 ⟨749094, by decide⟩ ⟨13, 2, 0, 749094, 374917, 1789, 16384⟩
    (by decide) selected_cut_29668

theorem selected_cut_29669 : selected 8 ⟨749113, by decide⟩
    (prefixPartial 13 374918) = some ⟨13, 2, 0, 749113, 374918, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_374918_749113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374918 ⟨749113, by decide⟩ :=
  accepted_of_selected 13 374918 ⟨749113, by decide⟩ ⟨13, 2, 0, 749113, 374918, 1529, 16384⟩
    (by decide) selected_cut_29669

theorem selected_cut_29670 : selected 8 ⟨749123, by decide⟩
    (prefixPartial 13 374919) = some ⟨13, 2, 0, 749123, 374919, 741, 16384⟩ := by
  decide +kernel

theorem context_13_374919_749123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374919 ⟨749123, by decide⟩ :=
  accepted_of_selected 13 374919 ⟨749123, by decide⟩ ⟨13, 2, 0, 749123, 374919, 741, 16384⟩
    (by decide) selected_cut_29670

theorem unmarked_context_12_93729_749124 : frontier 9 ⟨749124, by decide⟩
    (prefixCache 12 93729) (prefixPartial 12 93729) = false := by
  decide +kernel

theorem node_context_12_93729_749124 : EJMOriginalGlobalDAGData.nodes 9 ⟨749124, by decide⟩ =
    .split (coordinate 12) (![⟨749066, by decide⟩,⟨749094, by decide⟩,⟨749113, by decide⟩,⟨749123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93729_749124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93729 ⟨749124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93729
    ⟨749124, by decide⟩ (by decide) (![⟨749066, by decide⟩,⟨749094, by decide⟩,⟨749113, by decide⟩,⟨749123, by decide⟩]) unmarked_context_12_93729_749124 node_context_12_93729_749124
  intro a
  fin_cases a
  · exact context_13_374916_749066
  · exact context_13_374917_749094
  · exact context_13_374918_749113
  · exact context_13_374919_749123

theorem selected_cut_29671 : selected 8 ⟨749138, by decide⟩
    (prefixPartial 13 374920) = some ⟨13, 2, 0, 749138, 374920, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_374920_749138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374920 ⟨749138, by decide⟩ :=
  accepted_of_selected 13 374920 ⟨749138, by decide⟩ ⟨13, 2, 0, 749138, 374920, 1097, 16384⟩
    (by decide) selected_cut_29671

theorem selected_cut_29672 : selected 8 ⟨749160, by decide⟩
    (prefixPartial 13 374921) = some ⟨13, 2, 0, 749160, 374921, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_374921_749160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374921 ⟨749160, by decide⟩ :=
  accepted_of_selected 13 374921 ⟨749160, by decide⟩ ⟨13, 2, 0, 749160, 374921, 1517, 16384⟩
    (by decide) selected_cut_29672

theorem selected_cut_29673 : selected 8 ⟨749180, by decide⟩
    (prefixPartial 13 374922) = some ⟨13, 2, 0, 749180, 374922, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_374922_749180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374922 ⟨749180, by decide⟩ :=
  accepted_of_selected 13 374922 ⟨749180, by decide⟩ ⟨13, 2, 0, 749180, 374922, 1265, 16384⟩
    (by decide) selected_cut_29673

theorem selected_cut_29674 : selected 8 ⟨749191, by decide⟩
    (prefixPartial 13 374923) = some ⟨13, 2, 0, 749191, 374923, 769, 16384⟩ := by
  decide +kernel

theorem context_13_374923_749191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374923 ⟨749191, by decide⟩ :=
  accepted_of_selected 13 374923 ⟨749191, by decide⟩ ⟨13, 2, 0, 749191, 374923, 769, 16384⟩
    (by decide) selected_cut_29674

theorem unmarked_context_12_93730_749192 : frontier 9 ⟨749192, by decide⟩
    (prefixCache 12 93730) (prefixPartial 12 93730) = false := by
  decide +kernel

theorem node_context_12_93730_749192 : EJMOriginalGlobalDAGData.nodes 9 ⟨749192, by decide⟩ =
    .split (coordinate 12) (![⟨749138, by decide⟩,⟨749160, by decide⟩,⟨749180, by decide⟩,⟨749191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93730_749192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93730 ⟨749192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93730
    ⟨749192, by decide⟩ (by decide) (![⟨749138, by decide⟩,⟨749160, by decide⟩,⟨749180, by decide⟩,⟨749191, by decide⟩]) unmarked_context_12_93730_749192 node_context_12_93730_749192
  intro a
  fin_cases a
  · exact context_13_374920_749138
  · exact context_13_374921_749160
  · exact context_13_374922_749180
  · exact context_13_374923_749191

theorem selected_cut_29675 : selected 8 ⟨749211, by decide⟩
    (prefixPartial 13 374924) = some ⟨13, 2, 0, 749211, 374924, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_374924_749211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374924 ⟨749211, by decide⟩ :=
  accepted_of_selected 13 374924 ⟨749211, by decide⟩ ⟨13, 2, 0, 749211, 374924, 1273, 16384⟩
    (by decide) selected_cut_29675

theorem selected_cut_29676 : selected 8 ⟨749245, by decide⟩
    (prefixPartial 13 374925) = some ⟨13, 2, 0, 749245, 374925, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_374925_749245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374925 ⟨749245, by decide⟩ :=
  accepted_of_selected 13 374925 ⟨749245, by decide⟩ ⟨13, 2, 0, 749245, 374925, 2001, 16384⟩
    (by decide) selected_cut_29676

theorem selected_cut_29677 : selected 8 ⟨749268, by decide⟩
    (prefixPartial 13 374926) = some ⟨13, 2, 0, 749268, 374926, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_374926_749268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374926 ⟨749268, by decide⟩ :=
  accepted_of_selected 13 374926 ⟨749268, by decide⟩ ⟨13, 2, 0, 749268, 374926, 1649, 16384⟩
    (by decide) selected_cut_29677

theorem selected_cut_29678 : selected 8 ⟨749273, by decide⟩
    (prefixPartial 13 374927) = some ⟨13, 2, 0, 749273, 374927, 893, 16384⟩ := by
  decide +kernel

theorem context_13_374927_749273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374927 ⟨749273, by decide⟩ :=
  accepted_of_selected 13 374927 ⟨749273, by decide⟩ ⟨13, 2, 0, 749273, 374927, 893, 16384⟩
    (by decide) selected_cut_29678

theorem unmarked_context_12_93731_749274 : frontier 9 ⟨749274, by decide⟩
    (prefixCache 12 93731) (prefixPartial 12 93731) = false := by
  decide +kernel

theorem node_context_12_93731_749274 : EJMOriginalGlobalDAGData.nodes 9 ⟨749274, by decide⟩ =
    .split (coordinate 12) (![⟨749211, by decide⟩,⟨749245, by decide⟩,⟨749268, by decide⟩,⟨749273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93731_749274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93731 ⟨749274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93731
    ⟨749274, by decide⟩ (by decide) (![⟨749211, by decide⟩,⟨749245, by decide⟩,⟨749268, by decide⟩,⟨749273, by decide⟩]) unmarked_context_12_93731_749274 node_context_12_93731_749274
  intro a
  fin_cases a
  · exact context_13_374924_749211
  · exact context_13_374925_749245
  · exact context_13_374926_749268
  · exact context_13_374927_749273

theorem unmarked_context_11_23432_749275 : frontier 10 ⟨749275, by decide⟩
    (prefixCache 11 23432) (prefixPartial 11 23432) = false := by
  decide +kernel

theorem node_context_11_23432_749275 : EJMOriginalGlobalDAGData.nodes 10 ⟨749275, by decide⟩ =
    .split (coordinate 11) (![⟨749051, by decide⟩,⟨749124, by decide⟩,⟨749192, by decide⟩,⟨749274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23432_749275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23432 ⟨749275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23432
    ⟨749275, by decide⟩ (by decide) (![⟨749051, by decide⟩,⟨749124, by decide⟩,⟨749192, by decide⟩,⟨749274, by decide⟩]) unmarked_context_11_23432_749275 node_context_11_23432_749275
  intro a
  fin_cases a
  · exact context_12_93728_749051
  · exact context_12_93729_749124
  · exact context_12_93730_749192
  · exact context_12_93731_749274

theorem selected_cut_29679 : selected 8 ⟨749287, by decide⟩
    (prefixPartial 13 374928) = some ⟨13, 2, 0, 749287, 374928, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_374928_749287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374928 ⟨749287, by decide⟩ :=
  accepted_of_selected 13 374928 ⟨749287, by decide⟩ ⟨13, 2, 0, 749287, 374928, 1081, 16384⟩
    (by decide) selected_cut_29679

theorem selected_cut_29680 : selected 8 ⟨749310, by decide⟩
    (prefixPartial 13 374929) = some ⟨13, 2, 0, 749310, 374929, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_374929_749310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374929 ⟨749310, by decide⟩ :=
  accepted_of_selected 13 374929 ⟨749310, by decide⟩ ⟨13, 2, 0, 749310, 374929, 1665, 16384⟩
    (by decide) selected_cut_29680

theorem selected_cut_29681 : selected 8 ⟨749328, by decide⟩
    (prefixPartial 13 374930) = some ⟨13, 2, 0, 749328, 374930, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_374930_749328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374930 ⟨749328, by decide⟩ :=
  accepted_of_selected 13 374930 ⟨749328, by decide⟩ ⟨13, 2, 0, 749328, 374930, 1397, 16384⟩
    (by decide) selected_cut_29681

theorem selected_cut_29682 : selected 8 ⟨749336, by decide⟩
    (prefixPartial 13 374931) = some ⟨13, 2, 0, 749336, 374931, 745, 16384⟩ := by
  decide +kernel

theorem context_13_374931_749336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374931 ⟨749336, by decide⟩ :=
  accepted_of_selected 13 374931 ⟨749336, by decide⟩ ⟨13, 2, 0, 749336, 374931, 745, 16384⟩
    (by decide) selected_cut_29682

theorem unmarked_context_12_93732_749337 : frontier 9 ⟨749337, by decide⟩
    (prefixCache 12 93732) (prefixPartial 12 93732) = false := by
  decide +kernel

theorem node_context_12_93732_749337 : EJMOriginalGlobalDAGData.nodes 9 ⟨749337, by decide⟩ =
    .split (coordinate 12) (![⟨749287, by decide⟩,⟨749310, by decide⟩,⟨749328, by decide⟩,⟨749336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93732_749337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93732 ⟨749337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93732
    ⟨749337, by decide⟩ (by decide) (![⟨749287, by decide⟩,⟨749310, by decide⟩,⟨749328, by decide⟩,⟨749336, by decide⟩]) unmarked_context_12_93732_749337 node_context_12_93732_749337
  intro a
  fin_cases a
  · exact context_13_374928_749287
  · exact context_13_374929_749310
  · exact context_13_374930_749328
  · exact context_13_374931_749336

theorem selected_cut_29683 : selected 8 ⟨749351, by decide⟩
    (prefixPartial 13 374932) = some ⟨13, 2, 0, 749351, 374932, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_374932_749351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374932 ⟨749351, by decide⟩ :=
  accepted_of_selected 13 374932 ⟨749351, by decide⟩ ⟨13, 2, 0, 749351, 374932, 1109, 16384⟩
    (by decide) selected_cut_29683

theorem selected_cut_29684 : selected 8 ⟨749374, by decide⟩
    (prefixPartial 13 374933) = some ⟨13, 2, 0, 749374, 374933, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_374933_749374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374933 ⟨749374, by decide⟩ :=
  accepted_of_selected 13 374933 ⟨749374, by decide⟩ ⟨13, 2, 0, 749374, 374933, 1645, 16384⟩
    (by decide) selected_cut_29684

theorem selected_cut_29685 : selected 8 ⟨749392, by decide⟩
    (prefixPartial 13 374934) = some ⟨13, 2, 0, 749392, 374934, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_374934_749392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374934 ⟨749392, by decide⟩ :=
  accepted_of_selected 13 374934 ⟨749392, by decide⟩ ⟨13, 2, 0, 749392, 374934, 1517, 16384⟩
    (by decide) selected_cut_29685

theorem selected_cut_29686 : selected 8 ⟨749401, by decide⟩
    (prefixPartial 13 374935) = some ⟨13, 2, 0, 749401, 374935, 737, 16384⟩ := by
  decide +kernel

theorem context_13_374935_749401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374935 ⟨749401, by decide⟩ :=
  accepted_of_selected 13 374935 ⟨749401, by decide⟩ ⟨13, 2, 0, 749401, 374935, 737, 16384⟩
    (by decide) selected_cut_29686

theorem unmarked_context_12_93733_749402 : frontier 9 ⟨749402, by decide⟩
    (prefixCache 12 93733) (prefixPartial 12 93733) = false := by
  decide +kernel

theorem node_context_12_93733_749402 : EJMOriginalGlobalDAGData.nodes 9 ⟨749402, by decide⟩ =
    .split (coordinate 12) (![⟨749351, by decide⟩,⟨749374, by decide⟩,⟨749392, by decide⟩,⟨749401, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93733_749402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93733 ⟨749402, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93733
    ⟨749402, by decide⟩ (by decide) (![⟨749351, by decide⟩,⟨749374, by decide⟩,⟨749392, by decide⟩,⟨749401, by decide⟩]) unmarked_context_12_93733_749402 node_context_12_93733_749402
  intro a
  fin_cases a
  · exact context_13_374932_749351
  · exact context_13_374933_749374
  · exact context_13_374934_749392
  · exact context_13_374935_749401

theorem selected_cut_29687 : selected 8 ⟨749412, by decide⟩
    (prefixPartial 13 374936) = some ⟨13, 2, 0, 749412, 374936, 925, 16384⟩ := by
  decide +kernel

theorem context_13_374936_749412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374936 ⟨749412, by decide⟩ :=
  accepted_of_selected 13 374936 ⟨749412, by decide⟩ ⟨13, 2, 0, 749412, 374936, 925, 16384⟩
    (by decide) selected_cut_29687

theorem selected_cut_29688 : selected 8 ⟨749434, by decide⟩
    (prefixPartial 13 374937) = some ⟨13, 2, 0, 749434, 374937, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_374937_749434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374937 ⟨749434, by decide⟩ :=
  accepted_of_selected 13 374937 ⟨749434, by decide⟩ ⟨13, 2, 0, 749434, 374937, 1509, 16384⟩
    (by decide) selected_cut_29688

theorem selected_cut_29689 : selected 8 ⟨749447, by decide⟩
    (prefixPartial 13 374938) = some ⟨13, 2, 0, 749447, 374938, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_374938_749447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374938 ⟨749447, by decide⟩ :=
  accepted_of_selected 13 374938 ⟨749447, by decide⟩ ⟨13, 2, 0, 749447, 374938, 1353, 16384⟩
    (by decide) selected_cut_29689

theorem selected_cut_29690 : selected 8 ⟨749455, by decide⟩
    (prefixPartial 13 374939) = some ⟨13, 2, 0, 749455, 374939, 809, 16384⟩ := by
  decide +kernel

theorem context_13_374939_749455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374939 ⟨749455, by decide⟩ :=
  accepted_of_selected 13 374939 ⟨749455, by decide⟩ ⟨13, 2, 0, 749455, 374939, 809, 16384⟩
    (by decide) selected_cut_29690

theorem unmarked_context_12_93734_749456 : frontier 9 ⟨749456, by decide⟩
    (prefixCache 12 93734) (prefixPartial 12 93734) = false := by
  decide +kernel

theorem node_context_12_93734_749456 : EJMOriginalGlobalDAGData.nodes 9 ⟨749456, by decide⟩ =
    .split (coordinate 12) (![⟨749412, by decide⟩,⟨749434, by decide⟩,⟨749447, by decide⟩,⟨749455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93734_749456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93734 ⟨749456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93734
    ⟨749456, by decide⟩ (by decide) (![⟨749412, by decide⟩,⟨749434, by decide⟩,⟨749447, by decide⟩,⟨749455, by decide⟩]) unmarked_context_12_93734_749456 node_context_12_93734_749456
  intro a
  fin_cases a
  · exact context_13_374936_749412
  · exact context_13_374937_749434
  · exact context_13_374938_749447
  · exact context_13_374939_749455

theorem selected_cut_29691 : selected 8 ⟨749476, by decide⟩
    (prefixPartial 13 374940) = some ⟨13, 2, 0, 749476, 374940, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_374940_749476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374940 ⟨749476, by decide⟩ :=
  accepted_of_selected 13 374940 ⟨749476, by decide⟩ ⟨13, 2, 0, 749476, 374940, 1121, 16384⟩
    (by decide) selected_cut_29691

theorem selected_cut_29692 : selected 8 ⟨749503, by decide⟩
    (prefixPartial 13 374941) = some ⟨13, 2, 0, 749503, 374941, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_374941_749503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374941 ⟨749503, by decide⟩ :=
  accepted_of_selected 13 374941 ⟨749503, by decide⟩ ⟨13, 2, 0, 749503, 374941, 1817, 16384⟩
    (by decide) selected_cut_29692

theorem selected_cut_29693 : selected 8 ⟨749522, by decide⟩
    (prefixPartial 13 374942) = some ⟨13, 2, 0, 749522, 374942, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_374942_749522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374942 ⟨749522, by decide⟩ :=
  accepted_of_selected 13 374942 ⟨749522, by decide⟩ ⟨13, 2, 0, 749522, 374942, 1729, 16384⟩
    (by decide) selected_cut_29693

theorem selected_cut_29694 : selected 8 ⟨749531, by decide⟩
    (prefixPartial 13 374943) = some ⟨13, 2, 0, 749531, 374943, 897, 16384⟩ := by
  decide +kernel

theorem context_13_374943_749531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374943 ⟨749531, by decide⟩ :=
  accepted_of_selected 13 374943 ⟨749531, by decide⟩ ⟨13, 2, 0, 749531, 374943, 897, 16384⟩
    (by decide) selected_cut_29694

theorem unmarked_context_12_93735_749532 : frontier 9 ⟨749532, by decide⟩
    (prefixCache 12 93735) (prefixPartial 12 93735) = false := by
  decide +kernel

theorem node_context_12_93735_749532 : EJMOriginalGlobalDAGData.nodes 9 ⟨749532, by decide⟩ =
    .split (coordinate 12) (![⟨749476, by decide⟩,⟨749503, by decide⟩,⟨749522, by decide⟩,⟨749531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93735_749532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93735 ⟨749532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93735
    ⟨749532, by decide⟩ (by decide) (![⟨749476, by decide⟩,⟨749503, by decide⟩,⟨749522, by decide⟩,⟨749531, by decide⟩]) unmarked_context_12_93735_749532 node_context_12_93735_749532
  intro a
  fin_cases a
  · exact context_13_374940_749476
  · exact context_13_374941_749503
  · exact context_13_374942_749522
  · exact context_13_374943_749531

theorem unmarked_context_11_23433_749533 : frontier 10 ⟨749533, by decide⟩
    (prefixCache 11 23433) (prefixPartial 11 23433) = false := by
  decide +kernel

theorem node_context_11_23433_749533 : EJMOriginalGlobalDAGData.nodes 10 ⟨749533, by decide⟩ =
    .split (coordinate 11) (![⟨749337, by decide⟩,⟨749402, by decide⟩,⟨749456, by decide⟩,⟨749532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23433_749533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23433 ⟨749533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23433
    ⟨749533, by decide⟩ (by decide) (![⟨749337, by decide⟩,⟨749402, by decide⟩,⟨749456, by decide⟩,⟨749532, by decide⟩]) unmarked_context_11_23433_749533 node_context_11_23433_749533
  intro a
  fin_cases a
  · exact context_12_93732_749337
  · exact context_12_93733_749402
  · exact context_12_93734_749456
  · exact context_12_93735_749532

theorem selected_cut_29695 : selected 8 ⟨749546, by decide⟩
    (prefixPartial 13 374944) = some ⟨13, 2, 0, 749546, 374944, 709, 16384⟩ := by
  decide +kernel

theorem context_13_374944_749546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374944 ⟨749546, by decide⟩ :=
  accepted_of_selected 13 374944 ⟨749546, by decide⟩ ⟨13, 2, 0, 749546, 374944, 709, 16384⟩
    (by decide) selected_cut_29695

theorem selected_cut_29696 : selected 8 ⟨749566, by decide⟩
    (prefixPartial 13 374945) = some ⟨13, 2, 0, 749566, 374945, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_374945_749566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374945 ⟨749566, by decide⟩ :=
  accepted_of_selected 13 374945 ⟨749566, by decide⟩ ⟨13, 2, 0, 749566, 374945, 1449, 16384⟩
    (by decide) selected_cut_29696

theorem selected_cut_29697 : selected 8 ⟨749584, by decide⟩
    (prefixPartial 13 374946) = some ⟨13, 2, 0, 749584, 374946, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_374946_749584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374946 ⟨749584, by decide⟩ :=
  accepted_of_selected 13 374946 ⟨749584, by decide⟩ ⟨13, 2, 0, 749584, 374946, 1461, 16384⟩
    (by decide) selected_cut_29697

theorem selected_cut_29698 : selected 8 ⟨749592, by decide⟩
    (prefixPartial 13 374947) = some ⟨13, 2, 0, 749592, 374947, 705, 16384⟩ := by
  decide +kernel

theorem context_13_374947_749592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374947 ⟨749592, by decide⟩ :=
  accepted_of_selected 13 374947 ⟨749592, by decide⟩ ⟨13, 2, 0, 749592, 374947, 705, 16384⟩
    (by decide) selected_cut_29698

theorem unmarked_context_12_93736_749593 : frontier 9 ⟨749593, by decide⟩
    (prefixCache 12 93736) (prefixPartial 12 93736) = false := by
  decide +kernel

theorem node_context_12_93736_749593 : EJMOriginalGlobalDAGData.nodes 9 ⟨749593, by decide⟩ =
    .split (coordinate 12) (![⟨749546, by decide⟩,⟨749566, by decide⟩,⟨749584, by decide⟩,⟨749592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93736_749593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93736 ⟨749593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93736
    ⟨749593, by decide⟩ (by decide) (![⟨749546, by decide⟩,⟨749566, by decide⟩,⟨749584, by decide⟩,⟨749592, by decide⟩]) unmarked_context_12_93736_749593 node_context_12_93736_749593
  intro a
  fin_cases a
  · exact context_13_374944_749546
  · exact context_13_374945_749566
  · exact context_13_374946_749584
  · exact context_13_374947_749592

theorem selected_cut_29699 : selected 8 ⟨749607, by decide⟩
    (prefixPartial 13 374948) = some ⟨13, 2, 0, 749607, 374948, 905, 16384⟩ := by
  decide +kernel

theorem context_13_374948_749607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374948 ⟨749607, by decide⟩ :=
  accepted_of_selected 13 374948 ⟨749607, by decide⟩ ⟨13, 2, 0, 749607, 374948, 905, 16384⟩
    (by decide) selected_cut_29699

theorem selected_cut_29700 : selected 8 ⟨749630, by decide⟩
    (prefixPartial 13 374949) = some ⟨13, 2, 0, 749630, 374949, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_374949_749630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374949 ⟨749630, by decide⟩ :=
  accepted_of_selected 13 374949 ⟨749630, by decide⟩ ⟨13, 2, 0, 749630, 374949, 1541, 16384⟩
    (by decide) selected_cut_29700

theorem selected_cut_29701 : selected 8 ⟨749651, by decide⟩
    (prefixPartial 13 374950) = some ⟨13, 2, 0, 749651, 374950, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_374950_749651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374950 ⟨749651, by decide⟩ :=
  accepted_of_selected 13 374950 ⟨749651, by decide⟩ ⟨13, 2, 0, 749651, 374950, 1661, 16384⟩
    (by decide) selected_cut_29701

theorem selected_cut_29702 : selected 8 ⟨749659, by decide⟩
    (prefixPartial 13 374951) = some ⟨13, 2, 0, 749659, 374951, 801, 16384⟩ := by
  decide +kernel

theorem context_13_374951_749659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374951 ⟨749659, by decide⟩ :=
  accepted_of_selected 13 374951 ⟨749659, by decide⟩ ⟨13, 2, 0, 749659, 374951, 801, 16384⟩
    (by decide) selected_cut_29702

theorem unmarked_context_12_93737_749660 : frontier 9 ⟨749660, by decide⟩
    (prefixCache 12 93737) (prefixPartial 12 93737) = false := by
  decide +kernel

theorem node_context_12_93737_749660 : EJMOriginalGlobalDAGData.nodes 9 ⟨749660, by decide⟩ =
    .split (coordinate 12) (![⟨749607, by decide⟩,⟨749630, by decide⟩,⟨749651, by decide⟩,⟨749659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93737_749660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93737 ⟨749660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93737
    ⟨749660, by decide⟩ (by decide) (![⟨749607, by decide⟩,⟨749630, by decide⟩,⟨749651, by decide⟩,⟨749659, by decide⟩]) unmarked_context_12_93737_749660 node_context_12_93737_749660
  intro a
  fin_cases a
  · exact context_13_374948_749607
  · exact context_13_374949_749630
  · exact context_13_374950_749651
  · exact context_13_374951_749659

theorem selected_cut_29703 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 93738) = some ⟨12, 1, 0, 445248, 93738, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93738_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93738 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 93738 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 93738, 1, 65536⟩
    (by decide) selected_cut_29703

theorem selected_cut_29704 : selected 8 ⟨749672, by decide⟩
    (prefixPartial 13 374956) = some ⟨13, 2, 0, 749672, 374956, 749, 16384⟩ := by
  decide +kernel

theorem context_13_374956_749672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374956 ⟨749672, by decide⟩ :=
  accepted_of_selected 13 374956 ⟨749672, by decide⟩ ⟨13, 2, 0, 749672, 374956, 749, 16384⟩
    (by decide) selected_cut_29704

theorem selected_cut_29705 : selected 8 ⟨749701, by decide⟩
    (prefixPartial 13 374957) = some ⟨13, 2, 0, 749701, 374957, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_374957_749701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374957 ⟨749701, by decide⟩ :=
  accepted_of_selected 13 374957 ⟨749701, by decide⟩ ⟨13, 2, 0, 749701, 374957, 1761, 16384⟩
    (by decide) selected_cut_29705

theorem selected_cut_29706 : selected 8 ⟨749721, by decide⟩
    (prefixPartial 13 374958) = some ⟨13, 2, 0, 749721, 374958, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_374958_749721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374958 ⟨749721, by decide⟩ :=
  accepted_of_selected 13 374958 ⟨749721, by decide⟩ ⟨13, 2, 0, 749721, 374958, 1649, 16384⟩
    (by decide) selected_cut_29706

theorem selected_cut_29707 : selected 8 ⟨749731, by decide⟩
    (prefixPartial 13 374959) = some ⟨13, 2, 0, 749731, 374959, 793, 16384⟩ := by
  decide +kernel

theorem context_13_374959_749731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374959 ⟨749731, by decide⟩ :=
  accepted_of_selected 13 374959 ⟨749731, by decide⟩ ⟨13, 2, 0, 749731, 374959, 793, 16384⟩
    (by decide) selected_cut_29707

theorem unmarked_context_12_93739_749732 : frontier 9 ⟨749732, by decide⟩
    (prefixCache 12 93739) (prefixPartial 12 93739) = false := by
  decide +kernel

theorem node_context_12_93739_749732 : EJMOriginalGlobalDAGData.nodes 9 ⟨749732, by decide⟩ =
    .split (coordinate 12) (![⟨749672, by decide⟩,⟨749701, by decide⟩,⟨749721, by decide⟩,⟨749731, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93739_749732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93739 ⟨749732, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93739
    ⟨749732, by decide⟩ (by decide) (![⟨749672, by decide⟩,⟨749701, by decide⟩,⟨749721, by decide⟩,⟨749731, by decide⟩]) unmarked_context_12_93739_749732 node_context_12_93739_749732
  intro a
  fin_cases a
  · exact context_13_374956_749672
  · exact context_13_374957_749701
  · exact context_13_374958_749721
  · exact context_13_374959_749731

theorem unmarked_context_11_23434_749733 : frontier 10 ⟨749733, by decide⟩
    (prefixCache 11 23434) (prefixPartial 11 23434) = false := by
  decide +kernel

theorem node_context_11_23434_749733 : EJMOriginalGlobalDAGData.nodes 10 ⟨749733, by decide⟩ =
    .split (coordinate 11) (![⟨749593, by decide⟩,⟨749660, by decide⟩,⟨445248, by decide⟩,⟨749732, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23434_749733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23434 ⟨749733, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23434
    ⟨749733, by decide⟩ (by decide) (![⟨749593, by decide⟩,⟨749660, by decide⟩,⟨445248, by decide⟩,⟨749732, by decide⟩]) unmarked_context_11_23434_749733 node_context_11_23434_749733
  intro a
  fin_cases a
  · exact context_12_93736_749593
  · exact context_12_93737_749660
  · exact context_12_93738_445248
  · exact context_12_93739_749732

theorem selected_cut_29708 : selected 8 ⟨749745, by decide⟩
    (prefixPartial 13 374960) = some ⟨13, 2, 0, 749745, 374960, 705, 16384⟩ := by
  decide +kernel

theorem context_13_374960_749745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374960 ⟨749745, by decide⟩ :=
  accepted_of_selected 13 374960 ⟨749745, by decide⟩ ⟨13, 2, 0, 749745, 374960, 705, 16384⟩
    (by decide) selected_cut_29708

theorem selected_cut_29709 : selected 8 ⟨749764, by decide⟩
    (prefixPartial 13 374961) = some ⟨13, 2, 0, 749764, 374961, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_374961_749764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374961 ⟨749764, by decide⟩ :=
  accepted_of_selected 13 374961 ⟨749764, by decide⟩ ⟨13, 2, 0, 749764, 374961, 1509, 16384⟩
    (by decide) selected_cut_29709

theorem selected_cut_29710 : selected 8 ⟨749782, by decide⟩
    (prefixPartial 13 374962) = some ⟨13, 2, 0, 749782, 374962, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_374962_749782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374962 ⟨749782, by decide⟩ :=
  accepted_of_selected 13 374962 ⟨749782, by decide⟩ ⟨13, 2, 0, 749782, 374962, 1357, 16384⟩
    (by decide) selected_cut_29710

theorem selected_cut_29711 : selected 8 ⟨749787, by decide⟩
    (prefixPartial 13 374963) = some ⟨13, 2, 0, 749787, 374963, 721, 16384⟩ := by
  decide +kernel

theorem context_13_374963_749787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374963 ⟨749787, by decide⟩ :=
  accepted_of_selected 13 374963 ⟨749787, by decide⟩ ⟨13, 2, 0, 749787, 374963, 721, 16384⟩
    (by decide) selected_cut_29711

theorem unmarked_context_12_93740_749788 : frontier 9 ⟨749788, by decide⟩
    (prefixCache 12 93740) (prefixPartial 12 93740) = false := by
  decide +kernel

theorem node_context_12_93740_749788 : EJMOriginalGlobalDAGData.nodes 9 ⟨749788, by decide⟩ =
    .split (coordinate 12) (![⟨749745, by decide⟩,⟨749764, by decide⟩,⟨749782, by decide⟩,⟨749787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93740_749788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93740 ⟨749788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93740
    ⟨749788, by decide⟩ (by decide) (![⟨749745, by decide⟩,⟨749764, by decide⟩,⟨749782, by decide⟩,⟨749787, by decide⟩]) unmarked_context_12_93740_749788 node_context_12_93740_749788
  intro a
  fin_cases a
  · exact context_13_374960_749745
  · exact context_13_374961_749764
  · exact context_13_374962_749782
  · exact context_13_374963_749787

theorem selected_cut_29712 : selected 8 ⟨749801, by decide⟩
    (prefixPartial 13 374964) = some ⟨13, 2, 0, 749801, 374964, 777, 16384⟩ := by
  decide +kernel

theorem context_13_374964_749801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374964 ⟨749801, by decide⟩ :=
  accepted_of_selected 13 374964 ⟨749801, by decide⟩ ⟨13, 2, 0, 749801, 374964, 777, 16384⟩
    (by decide) selected_cut_29712

theorem selected_cut_29713 : selected 8 ⟨749826, by decide⟩
    (prefixPartial 13 374965) = some ⟨13, 2, 0, 749826, 374965, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_374965_749826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374965 ⟨749826, by decide⟩ :=
  accepted_of_selected 13 374965 ⟨749826, by decide⟩ ⟨13, 2, 0, 749826, 374965, 1625, 16384⟩
    (by decide) selected_cut_29713

theorem selected_cut_29714 : selected 8 ⟨749843, by decide⟩
    (prefixPartial 13 374966) = some ⟨13, 2, 0, 749843, 374966, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_374966_749843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374966 ⟨749843, by decide⟩ :=
  accepted_of_selected 13 374966 ⟨749843, by decide⟩ ⟨13, 2, 0, 749843, 374966, 1533, 16384⟩
    (by decide) selected_cut_29714

theorem selected_cut_29715 : selected 8 ⟨749851, by decide⟩
    (prefixPartial 13 374967) = some ⟨13, 2, 0, 749851, 374967, 705, 16384⟩ := by
  decide +kernel

theorem context_13_374967_749851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374967 ⟨749851, by decide⟩ :=
  accepted_of_selected 13 374967 ⟨749851, by decide⟩ ⟨13, 2, 0, 749851, 374967, 705, 16384⟩
    (by decide) selected_cut_29715

theorem unmarked_context_12_93741_749852 : frontier 9 ⟨749852, by decide⟩
    (prefixCache 12 93741) (prefixPartial 12 93741) = false := by
  decide +kernel

theorem node_context_12_93741_749852 : EJMOriginalGlobalDAGData.nodes 9 ⟨749852, by decide⟩ =
    .split (coordinate 12) (![⟨749801, by decide⟩,⟨749826, by decide⟩,⟨749843, by decide⟩,⟨749851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93741_749852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93741 ⟨749852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93741
    ⟨749852, by decide⟩ (by decide) (![⟨749801, by decide⟩,⟨749826, by decide⟩,⟨749843, by decide⟩,⟨749851, by decide⟩]) unmarked_context_12_93741_749852 node_context_12_93741_749852
  intro a
  fin_cases a
  · exact context_13_374964_749801
  · exact context_13_374965_749826
  · exact context_13_374966_749843
  · exact context_13_374967_749851

theorem selected_cut_29716 : selected 8 ⟨749861, by decide⟩
    (prefixPartial 13 374968) = some ⟨13, 2, 0, 749861, 374968, 573, 16384⟩ := by
  decide +kernel

theorem context_13_374968_749861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374968 ⟨749861, by decide⟩ :=
  accepted_of_selected 13 374968 ⟨749861, by decide⟩ ⟨13, 2, 0, 749861, 374968, 573, 16384⟩
    (by decide) selected_cut_29716

theorem selected_cut_29717 : selected 8 ⟨749888, by decide⟩
    (prefixPartial 13 374969) = some ⟨13, 2, 0, 749888, 374969, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_374969_749888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374969 ⟨749888, by decide⟩ :=
  accepted_of_selected 13 374969 ⟨749888, by decide⟩ ⟨13, 2, 0, 749888, 374969, 1533, 16384⟩
    (by decide) selected_cut_29717

theorem selected_cut_29718 : selected 8 ⟨749902, by decide⟩
    (prefixPartial 13 374970) = some ⟨13, 2, 0, 749902, 374970, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_374970_749902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374970 ⟨749902, by decide⟩ :=
  accepted_of_selected 13 374970 ⟨749902, by decide⟩ ⟨13, 2, 0, 749902, 374970, 1293, 16384⟩
    (by decide) selected_cut_29718

theorem selected_cut_29719 : selected 8 ⟨749912, by decide⟩
    (prefixPartial 13 374971) = some ⟨13, 2, 0, 749912, 374971, 809, 16384⟩ := by
  decide +kernel

theorem context_13_374971_749912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374971 ⟨749912, by decide⟩ :=
  accepted_of_selected 13 374971 ⟨749912, by decide⟩ ⟨13, 2, 0, 749912, 374971, 809, 16384⟩
    (by decide) selected_cut_29719

theorem unmarked_context_12_93742_749913 : frontier 9 ⟨749913, by decide⟩
    (prefixCache 12 93742) (prefixPartial 12 93742) = false := by
  decide +kernel

theorem node_context_12_93742_749913 : EJMOriginalGlobalDAGData.nodes 9 ⟨749913, by decide⟩ =
    .split (coordinate 12) (![⟨749861, by decide⟩,⟨749888, by decide⟩,⟨749902, by decide⟩,⟨749912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93742_749913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93742 ⟨749913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93742
    ⟨749913, by decide⟩ (by decide) (![⟨749861, by decide⟩,⟨749888, by decide⟩,⟨749902, by decide⟩,⟨749912, by decide⟩]) unmarked_context_12_93742_749913 node_context_12_93742_749913
  intro a
  fin_cases a
  · exact context_13_374968_749861
  · exact context_13_374969_749888
  · exact context_13_374970_749902
  · exact context_13_374971_749912

theorem selected_cut_29720 : selected 8 ⟨749921, by decide⟩
    (prefixPartial 13 374972) = some ⟨13, 2, 0, 749921, 374972, 681, 16384⟩ := by
  decide +kernel

theorem context_13_374972_749921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374972 ⟨749921, by decide⟩ :=
  accepted_of_selected 13 374972 ⟨749921, by decide⟩ ⟨13, 2, 0, 749921, 374972, 681, 16384⟩
    (by decide) selected_cut_29720

theorem selected_cut_29721 : selected 8 ⟨749944, by decide⟩
    (prefixPartial 13 374973) = some ⟨13, 2, 0, 749944, 374973, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_374973_749944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374973 ⟨749944, by decide⟩ :=
  accepted_of_selected 13 374973 ⟨749944, by decide⟩ ⟨13, 2, 0, 749944, 374973, 1821, 16384⟩
    (by decide) selected_cut_29721

theorem selected_cut_29722 : selected 8 ⟨749962, by decide⟩
    (prefixPartial 13 374974) = some ⟨13, 2, 0, 749962, 374974, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_374974_749962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374974 ⟨749962, by decide⟩ :=
  accepted_of_selected 13 374974 ⟨749962, by decide⟩ ⟨13, 2, 0, 749962, 374974, 1613, 16384⟩
    (by decide) selected_cut_29722

theorem selected_cut_29723 : selected 8 ⟨749970, by decide⟩
    (prefixPartial 13 374975) = some ⟨13, 2, 0, 749970, 374975, 901, 16384⟩ := by
  decide +kernel

theorem context_13_374975_749970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374975 ⟨749970, by decide⟩ :=
  accepted_of_selected 13 374975 ⟨749970, by decide⟩ ⟨13, 2, 0, 749970, 374975, 901, 16384⟩
    (by decide) selected_cut_29723

theorem unmarked_context_12_93743_749971 : frontier 9 ⟨749971, by decide⟩
    (prefixCache 12 93743) (prefixPartial 12 93743) = false := by
  decide +kernel

theorem node_context_12_93743_749971 : EJMOriginalGlobalDAGData.nodes 9 ⟨749971, by decide⟩ =
    .split (coordinate 12) (![⟨749921, by decide⟩,⟨749944, by decide⟩,⟨749962, by decide⟩,⟨749970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93743_749971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93743 ⟨749971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93743
    ⟨749971, by decide⟩ (by decide) (![⟨749921, by decide⟩,⟨749944, by decide⟩,⟨749962, by decide⟩,⟨749970, by decide⟩]) unmarked_context_12_93743_749971 node_context_12_93743_749971
  intro a
  fin_cases a
  · exact context_13_374972_749921
  · exact context_13_374973_749944
  · exact context_13_374974_749962
  · exact context_13_374975_749970

theorem unmarked_context_11_23435_749972 : frontier 10 ⟨749972, by decide⟩
    (prefixCache 11 23435) (prefixPartial 11 23435) = false := by
  decide +kernel

theorem node_context_11_23435_749972 : EJMOriginalGlobalDAGData.nodes 10 ⟨749972, by decide⟩ =
    .split (coordinate 11) (![⟨749788, by decide⟩,⟨749852, by decide⟩,⟨749913, by decide⟩,⟨749971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23435_749972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23435 ⟨749972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23435
    ⟨749972, by decide⟩ (by decide) (![⟨749788, by decide⟩,⟨749852, by decide⟩,⟨749913, by decide⟩,⟨749971, by decide⟩]) unmarked_context_11_23435_749972 node_context_11_23435_749972
  intro a
  fin_cases a
  · exact context_12_93740_749788
  · exact context_12_93741_749852
  · exact context_12_93742_749913
  · exact context_12_93743_749971

theorem unmarked_context_10_5858_749973 : frontier 11 ⟨749973, by decide⟩
    (prefixCache 10 5858) (prefixPartial 10 5858) = false := by
  decide +kernel

theorem node_context_10_5858_749973 : EJMOriginalGlobalDAGData.nodes 11 ⟨749973, by decide⟩ =
    .split (coordinate 10) (![⟨749275, by decide⟩,⟨749533, by decide⟩,⟨749733, by decide⟩,⟨749972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5858_749973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5858 ⟨749973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5858
    ⟨749973, by decide⟩ (by decide) (![⟨749275, by decide⟩,⟨749533, by decide⟩,⟨749733, by decide⟩,⟨749972, by decide⟩]) unmarked_context_10_5858_749973 node_context_10_5858_749973
  intro a
  fin_cases a
  · exact context_11_23432_749275
  · exact context_11_23433_749533
  · exact context_11_23434_749733
  · exact context_11_23435_749972

theorem selected_cut_29724 : selected 8 ⟨749985, by decide⟩
    (prefixPartial 13 374976) = some ⟨13, 2, 0, 749985, 374976, 761, 16384⟩ := by
  decide +kernel

theorem context_13_374976_749985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374976 ⟨749985, by decide⟩ :=
  accepted_of_selected 13 374976 ⟨749985, by decide⟩ ⟨13, 2, 0, 749985, 374976, 761, 16384⟩
    (by decide) selected_cut_29724

theorem selected_cut_29725 : selected 8 ⟨750010, by decide⟩
    (prefixPartial 13 374977) = some ⟨13, 2, 0, 750010, 374977, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_374977_750010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374977 ⟨750010, by decide⟩ :=
  accepted_of_selected 13 374977 ⟨750010, by decide⟩ ⟨13, 2, 0, 750010, 374977, 1885, 16384⟩
    (by decide) selected_cut_29725

theorem selected_cut_29726 : selected 8 ⟨750027, by decide⟩
    (prefixPartial 13 374978) = some ⟨13, 2, 0, 750027, 374978, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_374978_750027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374978 ⟨750027, by decide⟩ :=
  accepted_of_selected 13 374978 ⟨750027, by decide⟩ ⟨13, 2, 0, 750027, 374978, 1453, 16384⟩
    (by decide) selected_cut_29726

theorem selected_cut_29727 : selected 8 ⟨750031, by decide⟩
    (prefixPartial 13 374979) = some ⟨13, 2, 0, 750031, 374979, 689, 16384⟩ := by
  decide +kernel

theorem context_13_374979_750031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374979 ⟨750031, by decide⟩ :=
  accepted_of_selected 13 374979 ⟨750031, by decide⟩ ⟨13, 2, 0, 750031, 374979, 689, 16384⟩
    (by decide) selected_cut_29727

theorem unmarked_context_12_93744_750032 : frontier 9 ⟨750032, by decide⟩
    (prefixCache 12 93744) (prefixPartial 12 93744) = false := by
  decide +kernel

theorem node_context_12_93744_750032 : EJMOriginalGlobalDAGData.nodes 9 ⟨750032, by decide⟩ =
    .split (coordinate 12) (![⟨749985, by decide⟩,⟨750010, by decide⟩,⟨750027, by decide⟩,⟨750031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93744_750032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93744 ⟨750032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93744
    ⟨750032, by decide⟩ (by decide) (![⟨749985, by decide⟩,⟨750010, by decide⟩,⟨750027, by decide⟩,⟨750031, by decide⟩]) unmarked_context_12_93744_750032 node_context_12_93744_750032
  intro a
  fin_cases a
  · exact context_13_374976_749985
  · exact context_13_374977_750010
  · exact context_13_374978_750027
  · exact context_13_374979_750031

theorem selected_cut_29728 : selected 8 ⟨750044, by decide⟩
    (prefixPartial 13 374980) = some ⟨13, 2, 0, 750044, 374980, 653, 16384⟩ := by
  decide +kernel

theorem context_13_374980_750044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374980 ⟨750044, by decide⟩ :=
  accepted_of_selected 13 374980 ⟨750044, by decide⟩ ⟨13, 2, 0, 750044, 374980, 653, 16384⟩
    (by decide) selected_cut_29728

theorem selected_cut_29729 : selected 8 ⟨750067, by decide⟩
    (prefixPartial 13 374981) = some ⟨13, 2, 0, 750067, 374981, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_374981_750067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374981 ⟨750067, by decide⟩ :=
  accepted_of_selected 13 374981 ⟨750067, by decide⟩ ⟨13, 2, 0, 750067, 374981, 1829, 16384⟩
    (by decide) selected_cut_29729

theorem selected_cut_29730 : selected 8 ⟨750084, by decide⟩
    (prefixPartial 13 374982) = some ⟨13, 2, 0, 750084, 374982, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_374982_750084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374982 ⟨750084, by decide⟩ :=
  accepted_of_selected 13 374982 ⟨750084, by decide⟩ ⟨13, 2, 0, 750084, 374982, 1665, 16384⟩
    (by decide) selected_cut_29730

theorem selected_cut_29731 : selected 8 ⟨750091, by decide⟩
    (prefixPartial 13 374983) = some ⟨13, 2, 0, 750091, 374983, 925, 16384⟩ := by
  decide +kernel

theorem context_13_374983_750091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374983 ⟨750091, by decide⟩ :=
  accepted_of_selected 13 374983 ⟨750091, by decide⟩ ⟨13, 2, 0, 750091, 374983, 925, 16384⟩
    (by decide) selected_cut_29731

theorem unmarked_context_12_93745_750092 : frontier 9 ⟨750092, by decide⟩
    (prefixCache 12 93745) (prefixPartial 12 93745) = false := by
  decide +kernel

theorem node_context_12_93745_750092 : EJMOriginalGlobalDAGData.nodes 9 ⟨750092, by decide⟩ =
    .split (coordinate 12) (![⟨750044, by decide⟩,⟨750067, by decide⟩,⟨750084, by decide⟩,⟨750091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93745_750092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93745 ⟨750092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93745
    ⟨750092, by decide⟩ (by decide) (![⟨750044, by decide⟩,⟨750067, by decide⟩,⟨750084, by decide⟩,⟨750091, by decide⟩]) unmarked_context_12_93745_750092 node_context_12_93745_750092
  intro a
  fin_cases a
  · exact context_13_374980_750044
  · exact context_13_374981_750067
  · exact context_13_374982_750084
  · exact context_13_374983_750091

theorem selected_cut_29732 : selected 8 ⟨750098, by decide⟩
    (prefixPartial 13 374984) = some ⟨13, 2, 0, 750098, 374984, 497, 16384⟩ := by
  decide +kernel

theorem context_13_374984_750098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374984 ⟨750098, by decide⟩ :=
  accepted_of_selected 13 374984 ⟨750098, by decide⟩ ⟨13, 2, 0, 750098, 374984, 497, 16384⟩
    (by decide) selected_cut_29732

theorem selected_cut_29733 : selected 8 ⟨750120, by decide⟩
    (prefixPartial 13 374985) = some ⟨13, 2, 0, 750120, 374985, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_374985_750120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374985 ⟨750120, by decide⟩ :=
  accepted_of_selected 13 374985 ⟨750120, by decide⟩ ⟨13, 2, 0, 750120, 374985, 1625, 16384⟩
    (by decide) selected_cut_29733

theorem selected_cut_29734 : selected 8 ⟨750139, by decide⟩
    (prefixPartial 13 374986) = some ⟨13, 2, 0, 750139, 374986, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_374986_750139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374986 ⟨750139, by decide⟩ :=
  accepted_of_selected 13 374986 ⟨750139, by decide⟩ ⟨13, 2, 0, 750139, 374986, 1349, 16384⟩
    (by decide) selected_cut_29734

theorem selected_cut_29735 : selected 8 ⟨750145, by decide⟩
    (prefixPartial 13 374987) = some ⟨13, 2, 0, 750145, 374987, 885, 16384⟩ := by
  decide +kernel

theorem context_13_374987_750145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374987 ⟨750145, by decide⟩ :=
  accepted_of_selected 13 374987 ⟨750145, by decide⟩ ⟨13, 2, 0, 750145, 374987, 885, 16384⟩
    (by decide) selected_cut_29735

theorem unmarked_context_12_93746_750146 : frontier 9 ⟨750146, by decide⟩
    (prefixCache 12 93746) (prefixPartial 12 93746) = false := by
  decide +kernel

theorem node_context_12_93746_750146 : EJMOriginalGlobalDAGData.nodes 9 ⟨750146, by decide⟩ =
    .split (coordinate 12) (![⟨750098, by decide⟩,⟨750120, by decide⟩,⟨750139, by decide⟩,⟨750145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93746_750146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93746 ⟨750146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93746
    ⟨750146, by decide⟩ (by decide) (![⟨750098, by decide⟩,⟨750120, by decide⟩,⟨750139, by decide⟩,⟨750145, by decide⟩]) unmarked_context_12_93746_750146 node_context_12_93746_750146
  intro a
  fin_cases a
  · exact context_13_374984_750098
  · exact context_13_374985_750120
  · exact context_13_374986_750139
  · exact context_13_374987_750145

theorem selected_cut_29736 : selected 8 ⟨750158, by decide⟩
    (prefixPartial 13 374988) = some ⟨13, 2, 0, 750158, 374988, 629, 16384⟩ := by
  decide +kernel

theorem context_13_374988_750158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374988 ⟨750158, by decide⟩ :=
  accepted_of_selected 13 374988 ⟨750158, by decide⟩ ⟨13, 2, 0, 750158, 374988, 629, 16384⟩
    (by decide) selected_cut_29736

theorem selected_cut_29737 : selected 8 ⟨750196, by decide⟩
    (prefixPartial 13 374989) = some ⟨13, 2, 0, 750196, 374989, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_374989_750196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374989 ⟨750196, by decide⟩ :=
  accepted_of_selected 13 374989 ⟨750196, by decide⟩ ⟨13, 2, 0, 750196, 374989, 2289, 16384⟩
    (by decide) selected_cut_29737

theorem selected_cut_29738 : selected 8 ⟨750220, by decide⟩
    (prefixPartial 13 374990) = some ⟨13, 2, 0, 750220, 374990, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_374990_750220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374990 ⟨750220, by decide⟩ :=
  accepted_of_selected 13 374990 ⟨750220, by decide⟩ ⟨13, 2, 0, 750220, 374990, 1817, 16384⟩
    (by decide) selected_cut_29738

theorem selected_cut_29739 : selected 8 ⟨750230, by decide⟩
    (prefixPartial 13 374991) = some ⟨13, 2, 0, 750230, 374991, 941, 16384⟩ := by
  decide +kernel

theorem context_13_374991_750230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374991 ⟨750230, by decide⟩ :=
  accepted_of_selected 13 374991 ⟨750230, by decide⟩ ⟨13, 2, 0, 750230, 374991, 941, 16384⟩
    (by decide) selected_cut_29739

theorem unmarked_context_12_93747_750231 : frontier 9 ⟨750231, by decide⟩
    (prefixCache 12 93747) (prefixPartial 12 93747) = false := by
  decide +kernel

theorem node_context_12_93747_750231 : EJMOriginalGlobalDAGData.nodes 9 ⟨750231, by decide⟩ =
    .split (coordinate 12) (![⟨750158, by decide⟩,⟨750196, by decide⟩,⟨750220, by decide⟩,⟨750230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93747_750231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93747 ⟨750231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93747
    ⟨750231, by decide⟩ (by decide) (![⟨750158, by decide⟩,⟨750196, by decide⟩,⟨750220, by decide⟩,⟨750230, by decide⟩]) unmarked_context_12_93747_750231 node_context_12_93747_750231
  intro a
  fin_cases a
  · exact context_13_374988_750158
  · exact context_13_374989_750196
  · exact context_13_374990_750220
  · exact context_13_374991_750230

theorem unmarked_context_11_23436_750232 : frontier 10 ⟨750232, by decide⟩
    (prefixCache 11 23436) (prefixPartial 11 23436) = false := by
  decide +kernel

theorem node_context_11_23436_750232 : EJMOriginalGlobalDAGData.nodes 10 ⟨750232, by decide⟩ =
    .split (coordinate 11) (![⟨750032, by decide⟩,⟨750092, by decide⟩,⟨750146, by decide⟩,⟨750231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23436_750232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23436 ⟨750232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23436
    ⟨750232, by decide⟩ (by decide) (![⟨750032, by decide⟩,⟨750092, by decide⟩,⟨750146, by decide⟩,⟨750231, by decide⟩]) unmarked_context_11_23436_750232 node_context_11_23436_750232
  intro a
  fin_cases a
  · exact context_12_93744_750032
  · exact context_12_93745_750092
  · exact context_12_93746_750146
  · exact context_12_93747_750231

theorem selected_cut_29740 : selected 8 ⟨750244, by decide⟩
    (prefixPartial 13 374992) = some ⟨13, 2, 0, 750244, 374992, 473, 16384⟩ := by
  decide +kernel

theorem context_13_374992_750244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374992 ⟨750244, by decide⟩ :=
  accepted_of_selected 13 374992 ⟨750244, by decide⟩ ⟨13, 2, 0, 750244, 374992, 473, 16384⟩
    (by decide) selected_cut_29740

theorem selected_cut_29741 : selected 8 ⟨750275, by decide⟩
    (prefixPartial 13 374993) = some ⟨13, 2, 0, 750275, 374993, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_374993_750275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374993 ⟨750275, by decide⟩ :=
  accepted_of_selected 13 374993 ⟨750275, by decide⟩ ⟨13, 2, 0, 750275, 374993, 1933, 16384⟩
    (by decide) selected_cut_29741

theorem selected_cut_29742 : selected 8 ⟨750292, by decide⟩
    (prefixPartial 13 374994) = some ⟨13, 2, 0, 750292, 374994, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_374994_750292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374994 ⟨750292, by decide⟩ :=
  accepted_of_selected 13 374994 ⟨750292, by decide⟩ ⟨13, 2, 0, 750292, 374994, 1345, 16384⟩
    (by decide) selected_cut_29742

theorem selected_cut_29743 : selected 8 ⟨750298, by decide⟩
    (prefixPartial 13 374995) = some ⟨13, 2, 0, 750298, 374995, 741, 16384⟩ := by
  decide +kernel

theorem context_13_374995_750298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374995 ⟨750298, by decide⟩ :=
  accepted_of_selected 13 374995 ⟨750298, by decide⟩ ⟨13, 2, 0, 750298, 374995, 741, 16384⟩
    (by decide) selected_cut_29743

theorem unmarked_context_12_93748_750299 : frontier 9 ⟨750299, by decide⟩
    (prefixCache 12 93748) (prefixPartial 12 93748) = false := by
  decide +kernel

theorem node_context_12_93748_750299 : EJMOriginalGlobalDAGData.nodes 9 ⟨750299, by decide⟩ =
    .split (coordinate 12) (![⟨750244, by decide⟩,⟨750275, by decide⟩,⟨750292, by decide⟩,⟨750298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93748_750299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93748 ⟨750299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93748
    ⟨750299, by decide⟩ (by decide) (![⟨750244, by decide⟩,⟨750275, by decide⟩,⟨750292, by decide⟩,⟨750298, by decide⟩]) unmarked_context_12_93748_750299 node_context_12_93748_750299
  intro a
  fin_cases a
  · exact context_13_374992_750244
  · exact context_13_374993_750275
  · exact context_13_374994_750292
  · exact context_13_374995_750298

theorem selected_cut_29744 : selected 8 ⟨750303, by decide⟩
    (prefixPartial 13 374996) = some ⟨13, 2, 0, 750303, 374996, 413, 16384⟩ := by
  decide +kernel

theorem context_13_374996_750303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374996 ⟨750303, by decide⟩ :=
  accepted_of_selected 13 374996 ⟨750303, by decide⟩ ⟨13, 2, 0, 750303, 374996, 413, 16384⟩
    (by decide) selected_cut_29744

theorem selected_cut_29745 : selected 8 ⟨750323, by decide⟩
    (prefixPartial 13 374997) = some ⟨13, 2, 0, 750323, 374997, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_374997_750323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374997 ⟨750323, by decide⟩ :=
  accepted_of_selected 13 374997 ⟨750323, by decide⟩ ⟨13, 2, 0, 750323, 374997, 1569, 16384⟩
    (by decide) selected_cut_29745

theorem selected_cut_29746 : selected 8 ⟨750342, by decide⟩
    (prefixPartial 13 374998) = some ⟨13, 2, 0, 750342, 374998, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_374998_750342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374998 ⟨750342, by decide⟩ :=
  accepted_of_selected 13 374998 ⟨750342, by decide⟩ ⟨13, 2, 0, 750342, 374998, 1493, 16384⟩
    (by decide) selected_cut_29746

theorem selected_cut_29747 : selected 8 ⟨750352, by decide⟩
    (prefixPartial 13 374999) = some ⟨13, 2, 0, 750352, 374999, 909, 16384⟩ := by
  decide +kernel

theorem context_13_374999_750352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 374999 ⟨750352, by decide⟩ :=
  accepted_of_selected 13 374999 ⟨750352, by decide⟩ ⟨13, 2, 0, 750352, 374999, 909, 16384⟩
    (by decide) selected_cut_29747

theorem unmarked_context_12_93749_750353 : frontier 9 ⟨750353, by decide⟩
    (prefixCache 12 93749) (prefixPartial 12 93749) = false := by
  decide +kernel

theorem node_context_12_93749_750353 : EJMOriginalGlobalDAGData.nodes 9 ⟨750353, by decide⟩ =
    .split (coordinate 12) (![⟨750303, by decide⟩,⟨750323, by decide⟩,⟨750342, by decide⟩,⟨750352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93749_750353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93749 ⟨750353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93749
    ⟨750353, by decide⟩ (by decide) (![⟨750303, by decide⟩,⟨750323, by decide⟩,⟨750342, by decide⟩,⟨750352, by decide⟩]) unmarked_context_12_93749_750353 node_context_12_93749_750353
  intro a
  fin_cases a
  · exact context_13_374996_750303
  · exact context_13_374997_750323
  · exact context_13_374998_750342
  · exact context_13_374999_750352

theorem selected_cut_29748 : selected 9 ⟨750400, by decide⟩
    (prefixPartial 12 93750) = some ⟨12, 2, 0, 750400, 93750, 4013, 65536⟩ := by
  decide +kernel

theorem context_12_93750_750400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93750 ⟨750400, by decide⟩ :=
  accepted_of_selected 12 93750 ⟨750400, by decide⟩ ⟨12, 2, 0, 750400, 93750, 4013, 65536⟩
    (by decide) selected_cut_29748

theorem selected_cut_29749 : selected 8 ⟨750411, by decide⟩
    (prefixPartial 13 375004) = some ⟨13, 2, 0, 750411, 375004, 373, 16384⟩ := by
  decide +kernel

theorem context_13_375004_750411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375004 ⟨750411, by decide⟩ :=
  accepted_of_selected 13 375004 ⟨750411, by decide⟩ ⟨13, 2, 0, 750411, 375004, 373, 16384⟩
    (by decide) selected_cut_29749

theorem selected_cut_29750 : selected 8 ⟨750438, by decide⟩
    (prefixPartial 13 375005) = some ⟨13, 2, 0, 750438, 375005, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_375005_750438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375005 ⟨750438, by decide⟩ :=
  accepted_of_selected 13 375005 ⟨750438, by decide⟩ ⟨13, 2, 0, 750438, 375005, 2025, 16384⟩
    (by decide) selected_cut_29750

theorem selected_cut_29751 : selected 8 ⟨750459, by decide⟩
    (prefixPartial 13 375006) = some ⟨13, 2, 0, 750459, 375006, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_375006_750459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375006 ⟨750459, by decide⟩ :=
  accepted_of_selected 13 375006 ⟨750459, by decide⟩ ⟨13, 2, 0, 750459, 375006, 1737, 16384⟩
    (by decide) selected_cut_29751

theorem selected_cut_29752 : selected 8 ⟨750464, by decide⟩
    (prefixPartial 13 375007) = some ⟨13, 2, 0, 750464, 375007, 921, 16384⟩ := by
  decide +kernel

theorem context_13_375007_750464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375007 ⟨750464, by decide⟩ :=
  accepted_of_selected 13 375007 ⟨750464, by decide⟩ ⟨13, 2, 0, 750464, 375007, 921, 16384⟩
    (by decide) selected_cut_29752

theorem unmarked_context_12_93751_750465 : frontier 9 ⟨750465, by decide⟩
    (prefixCache 12 93751) (prefixPartial 12 93751) = false := by
  decide +kernel

theorem node_context_12_93751_750465 : EJMOriginalGlobalDAGData.nodes 9 ⟨750465, by decide⟩ =
    .split (coordinate 12) (![⟨750411, by decide⟩,⟨750438, by decide⟩,⟨750459, by decide⟩,⟨750464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93751_750465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93751 ⟨750465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93751
    ⟨750465, by decide⟩ (by decide) (![⟨750411, by decide⟩,⟨750438, by decide⟩,⟨750459, by decide⟩,⟨750464, by decide⟩]) unmarked_context_12_93751_750465 node_context_12_93751_750465
  intro a
  fin_cases a
  · exact context_13_375004_750411
  · exact context_13_375005_750438
  · exact context_13_375006_750459
  · exact context_13_375007_750464

theorem unmarked_context_11_23437_750466 : frontier 10 ⟨750466, by decide⟩
    (prefixCache 11 23437) (prefixPartial 11 23437) = false := by
  decide +kernel

theorem node_context_11_23437_750466 : EJMOriginalGlobalDAGData.nodes 10 ⟨750466, by decide⟩ =
    .split (coordinate 11) (![⟨750299, by decide⟩,⟨750353, by decide⟩,⟨750400, by decide⟩,⟨750465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23437_750466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23437 ⟨750466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23437
    ⟨750466, by decide⟩ (by decide) (![⟨750299, by decide⟩,⟨750353, by decide⟩,⟨750400, by decide⟩,⟨750465, by decide⟩]) unmarked_context_11_23437_750466 node_context_11_23437_750466
  intro a
  fin_cases a
  · exact context_12_93748_750299
  · exact context_12_93749_750353
  · exact context_12_93750_750400
  · exact context_12_93751_750465

theorem selected_cut_29753 : selected 8 ⟨750471, by decide⟩
    (prefixPartial 13 375008) = some ⟨13, 2, 0, 750471, 375008, 169, 16384⟩ := by
  decide +kernel

theorem context_13_375008_750471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375008 ⟨750471, by decide⟩ :=
  accepted_of_selected 13 375008 ⟨750471, by decide⟩ ⟨13, 2, 0, 750471, 375008, 169, 16384⟩
    (by decide) selected_cut_29753

theorem selected_cut_29754 : selected 8 ⟨750501, by decide⟩
    (prefixPartial 13 375009) = some ⟨13, 2, 0, 750501, 375009, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_375009_750501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375009 ⟨750501, by decide⟩ :=
  accepted_of_selected 13 375009 ⟨750501, by decide⟩ ⟨13, 2, 0, 750501, 375009, 1877, 16384⟩
    (by decide) selected_cut_29754

theorem selected_cut_29755 : selected 8 ⟨750520, by decide⟩
    (prefixPartial 13 375010) = some ⟨13, 2, 0, 750520, 375010, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_375010_750520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375010 ⟨750520, by decide⟩ :=
  accepted_of_selected 13 375010 ⟨750520, by decide⟩ ⟨13, 2, 0, 750520, 375010, 1485, 16384⟩
    (by decide) selected_cut_29755

theorem selected_cut_29756 : selected 8 ⟨750527, by decide⟩
    (prefixPartial 13 375011) = some ⟨13, 2, 0, 750527, 375011, 781, 16384⟩ := by
  decide +kernel

theorem context_13_375011_750527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375011 ⟨750527, by decide⟩ :=
  accepted_of_selected 13 375011 ⟨750527, by decide⟩ ⟨13, 2, 0, 750527, 375011, 781, 16384⟩
    (by decide) selected_cut_29756

theorem unmarked_context_12_93752_750528 : frontier 9 ⟨750528, by decide⟩
    (prefixCache 12 93752) (prefixPartial 12 93752) = false := by
  decide +kernel

theorem node_context_12_93752_750528 : EJMOriginalGlobalDAGData.nodes 9 ⟨750528, by decide⟩ =
    .split (coordinate 12) (![⟨750471, by decide⟩,⟨750501, by decide⟩,⟨750520, by decide⟩,⟨750527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93752_750528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93752 ⟨750528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93752
    ⟨750528, by decide⟩ (by decide) (![⟨750471, by decide⟩,⟨750501, by decide⟩,⟨750520, by decide⟩,⟨750527, by decide⟩]) unmarked_context_12_93752_750528 node_context_12_93752_750528
  intro a
  fin_cases a
  · exact context_13_375008_750471
  · exact context_13_375009_750501
  · exact context_13_375010_750520
  · exact context_13_375011_750527

theorem selected_cut_29757 : selected 8 ⟨750540, by decide⟩
    (prefixPartial 13 375012) = some ⟨13, 2, 0, 750540, 375012, 277, 16384⟩ := by
  decide +kernel

theorem context_13_375012_750540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375012 ⟨750540, by decide⟩ :=
  accepted_of_selected 13 375012 ⟨750540, by decide⟩ ⟨13, 2, 0, 750540, 375012, 277, 16384⟩
    (by decide) selected_cut_29757

theorem selected_cut_29758 : selected 8 ⟨750565, by decide⟩
    (prefixPartial 13 375013) = some ⟨13, 2, 0, 750565, 375013, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_375013_750565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375013 ⟨750565, by decide⟩ :=
  accepted_of_selected 13 375013 ⟨750565, by decide⟩ ⟨13, 2, 0, 750565, 375013, 1505, 16384⟩
    (by decide) selected_cut_29758

theorem selected_cut_29759 : selected 8 ⟨750581, by decide⟩
    (prefixPartial 13 375014) = some ⟨13, 2, 0, 750581, 375014, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_375014_750581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375014 ⟨750581, by decide⟩ :=
  accepted_of_selected 13 375014 ⟨750581, by decide⟩ ⟨13, 2, 0, 750581, 375014, 1773, 16384⟩
    (by decide) selected_cut_29759

theorem selected_cut_29760 : selected 8 ⟨750592, by decide⟩
    (prefixPartial 13 375015) = some ⟨13, 2, 0, 750592, 375015, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_375015_750592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375015 ⟨750592, by decide⟩ :=
  accepted_of_selected 13 375015 ⟨750592, by decide⟩ ⟨13, 2, 0, 750592, 375015, 1049, 16384⟩
    (by decide) selected_cut_29760

theorem unmarked_context_12_93753_750593 : frontier 9 ⟨750593, by decide⟩
    (prefixCache 12 93753) (prefixPartial 12 93753) = false := by
  decide +kernel

theorem node_context_12_93753_750593 : EJMOriginalGlobalDAGData.nodes 9 ⟨750593, by decide⟩ =
    .split (coordinate 12) (![⟨750540, by decide⟩,⟨750565, by decide⟩,⟨750581, by decide⟩,⟨750592, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93753_750593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93753 ⟨750593, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93753
    ⟨750593, by decide⟩ (by decide) (![⟨750540, by decide⟩,⟨750565, by decide⟩,⟨750581, by decide⟩,⟨750592, by decide⟩]) unmarked_context_12_93753_750593 node_context_12_93753_750593
  intro a
  fin_cases a
  · exact context_13_375012_750540
  · exact context_13_375013_750565
  · exact context_13_375014_750581
  · exact context_13_375015_750592

theorem selected_cut_29761 : selected 9 ⟨750716, by decide⟩
    (prefixPartial 12 93754) = some ⟨12, 2, 0, 750716, 93754, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_93754_750716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93754 ⟨750716, by decide⟩ :=
  accepted_of_selected 12 93754 ⟨750716, by decide⟩ ⟨12, 2, 0, 750716, 93754, 3369, 65536⟩
    (by decide) selected_cut_29761

theorem selected_cut_29762 : selected 8 ⟨750720, by decide⟩
    (prefixPartial 13 375020) = some ⟨13, 2, 0, 750720, 375020, 77, 16384⟩ := by
  decide +kernel

theorem context_13_375020_750720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375020 ⟨750720, by decide⟩ :=
  accepted_of_selected 13 375020 ⟨750720, by decide⟩ ⟨13, 2, 0, 750720, 375020, 77, 16384⟩
    (by decide) selected_cut_29762

theorem selected_cut_29763 : selected 8 ⟨750760, by decide⟩
    (prefixPartial 13 375021) = some ⟨13, 2, 0, 750760, 375021, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_375021_750760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375021 ⟨750760, by decide⟩ :=
  accepted_of_selected 13 375021 ⟨750760, by decide⟩ ⟨13, 2, 0, 750760, 375021, 2141, 16384⟩
    (by decide) selected_cut_29763

theorem selected_cut_29764 : selected 8 ⟨750781, by decide⟩
    (prefixPartial 13 375022) = some ⟨13, 2, 0, 750781, 375022, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_375022_750781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375022 ⟨750781, by decide⟩ :=
  accepted_of_selected 13 375022 ⟨750781, by decide⟩ ⟨13, 2, 0, 750781, 375022, 1829, 16384⟩
    (by decide) selected_cut_29764

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
