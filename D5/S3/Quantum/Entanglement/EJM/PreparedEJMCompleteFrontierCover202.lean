/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover201
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_19395 : selected 8 ⟨495462, by decide⟩
    (prefixPartial 13 288813) = some ⟨13, 2, 0, 495462, 288813, 3449, 16384⟩ := by
  decide +kernel

theorem context_13_288813_495462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288813 ⟨495462, by decide⟩ :=
  accepted_of_selected 13 288813 ⟨495462, by decide⟩ ⟨13, 2, 0, 495462, 288813, 3449, 16384⟩
    (by decide) selected_cut_19395

theorem selected_cut_19396 : selected 8 ⟨495481, by decide⟩
    (prefixPartial 13 288814) = some ⟨13, 2, 0, 495481, 288814, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_288814_495481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288814 ⟨495481, by decide⟩ :=
  accepted_of_selected 13 288814 ⟨495481, by decide⟩ ⟨13, 2, 0, 495481, 288814, 1629, 16384⟩
    (by decide) selected_cut_19396

theorem selected_cut_19397 : selected 8 ⟨495493, by decide⟩
    (prefixPartial 13 288815) = some ⟨13, 2, 0, 495493, 288815, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_288815_495493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288815 ⟨495493, by decide⟩ :=
  accepted_of_selected 13 288815 ⟨495493, by decide⟩ ⟨13, 2, 0, 495493, 288815, 1225, 16384⟩
    (by decide) selected_cut_19397

theorem unmarked_context_12_72203_495494 : frontier 9 ⟨495494, by decide⟩
    (prefixCache 12 72203) (prefixPartial 12 72203) = false := by
  decide +kernel

theorem node_context_12_72203_495494 : EJMOriginalGlobalDAGData.nodes 9 ⟨495494, by decide⟩ =
    .split (coordinate 12) (![⟨495408, by decide⟩,⟨495462, by decide⟩,⟨495481, by decide⟩,⟨495493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72203_495494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72203 ⟨495494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72203
    ⟨495494, by decide⟩ (by decide) (![⟨495408, by decide⟩,⟨495462, by decide⟩,⟨495481, by decide⟩,⟨495493, by decide⟩]) unmarked_context_12_72203_495494 node_context_12_72203_495494
  intro a
  fin_cases a
  · exact context_13_288812_495408
  · exact context_13_288813_495462
  · exact context_13_288814_495481
  · exact context_13_288815_495493

theorem unmarked_context_11_18050_495495 : frontier 10 ⟨495495, by decide⟩
    (prefixCache 11 18050) (prefixPartial 11 18050) = false := by
  decide +kernel

theorem node_context_11_18050_495495 : EJMOriginalGlobalDAGData.nodes 10 ⟨495495, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨495320, by decide⟩,⟨88909, by decide⟩,⟨495494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18050_495495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18050 ⟨495495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18050
    ⟨495495, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨495320, by decide⟩,⟨88909, by decide⟩,⟨495494, by decide⟩]) unmarked_context_11_18050_495495 node_context_11_18050_495495
  intro a
  fin_cases a
  · exact context_12_72200_448748
  · exact context_12_72201_495320
  · exact context_12_72202_88909
  · exact context_12_72203_495494

theorem selected_cut_19398 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 72204) = some ⟨12, 1, 0, 448748, 72204, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72204_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72204 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 72204 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 72204, 1, 65536⟩
    (by decide) selected_cut_19398

theorem selected_cut_19399 : selected 8 ⟨495581, by decide⟩
    (prefixPartial 13 288820) = some ⟨13, 2, 0, 495581, 288820, 3721, 16384⟩ := by
  decide +kernel

theorem context_13_288820_495581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288820 ⟨495581, by decide⟩ :=
  accepted_of_selected 13 288820 ⟨495581, by decide⟩ ⟨13, 2, 0, 495581, 288820, 3721, 16384⟩
    (by decide) selected_cut_19399

theorem selected_cut_19400 : selected 8 ⟨495647, by decide⟩
    (prefixPartial 13 288821) = some ⟨13, 2, 0, 495647, 288821, 3321, 16384⟩ := by
  decide +kernel

theorem context_13_288821_495647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288821 ⟨495647, by decide⟩ :=
  accepted_of_selected 13 288821 ⟨495647, by decide⟩ ⟨13, 2, 0, 495647, 288821, 3321, 16384⟩
    (by decide) selected_cut_19400

theorem selected_cut_19401 : selected 8 ⟨495671, by decide⟩
    (prefixPartial 13 288822) = some ⟨13, 2, 0, 495671, 288822, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_288822_495671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288822 ⟨495671, by decide⟩ :=
  accepted_of_selected 13 288822 ⟨495671, by decide⟩ ⟨13, 2, 0, 495671, 288822, 1765, 16384⟩
    (by decide) selected_cut_19401

theorem selected_cut_19402 : selected 8 ⟨495709, by decide⟩
    (prefixPartial 13 288823) = some ⟨13, 2, 0, 495709, 288823, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_288823_495709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288823 ⟨495709, by decide⟩ :=
  accepted_of_selected 13 288823 ⟨495709, by decide⟩ ⟨13, 2, 0, 495709, 288823, 1509, 16384⟩
    (by decide) selected_cut_19402

theorem unmarked_context_12_72205_495710 : frontier 9 ⟨495710, by decide⟩
    (prefixCache 12 72205) (prefixPartial 12 72205) = false := by
  decide +kernel

theorem node_context_12_72205_495710 : EJMOriginalGlobalDAGData.nodes 9 ⟨495710, by decide⟩ =
    .split (coordinate 12) (![⟨495581, by decide⟩,⟨495647, by decide⟩,⟨495671, by decide⟩,⟨495709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72205_495710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72205 ⟨495710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72205
    ⟨495710, by decide⟩ (by decide) (![⟨495581, by decide⟩,⟨495647, by decide⟩,⟨495671, by decide⟩,⟨495709, by decide⟩]) unmarked_context_12_72205_495710 node_context_12_72205_495710
  intro a
  fin_cases a
  · exact context_13_288820_495581
  · exact context_13_288821_495647
  · exact context_13_288822_495671
  · exact context_13_288823_495709

theorem selected_cut_19403 : selected 8 ⟨495777, by decide⟩
    (prefixPartial 13 288824) = some ⟨13, 2, 0, 495777, 288824, 3657, 16384⟩ := by
  decide +kernel

theorem context_13_288824_495777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288824 ⟨495777, by decide⟩ :=
  accepted_of_selected 13 288824 ⟨495777, by decide⟩ ⟨13, 2, 0, 495777, 288824, 3657, 16384⟩
    (by decide) selected_cut_19403

theorem selected_cut_19404 : selected 8 ⟨495833, by decide⟩
    (prefixPartial 13 288825) = some ⟨13, 2, 0, 495833, 288825, 3641, 16384⟩ := by
  decide +kernel

theorem context_13_288825_495833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288825 ⟨495833, by decide⟩ :=
  accepted_of_selected 13 288825 ⟨495833, by decide⟩ ⟨13, 2, 0, 495833, 288825, 3641, 16384⟩
    (by decide) selected_cut_19404

theorem selected_cut_19405 : selected 8 ⟨495863, by decide⟩
    (prefixPartial 13 288826) = some ⟨13, 2, 0, 495863, 288826, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_288826_495863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288826 ⟨495863, by decide⟩ :=
  accepted_of_selected 13 288826 ⟨495863, by decide⟩ ⟨13, 2, 0, 495863, 288826, 2057, 16384⟩
    (by decide) selected_cut_19405

theorem selected_cut_19406 : selected 8 ⟨495888, by decide⟩
    (prefixPartial 13 288827) = some ⟨13, 2, 0, 495888, 288827, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_288827_495888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288827 ⟨495888, by decide⟩ :=
  accepted_of_selected 13 288827 ⟨495888, by decide⟩ ⟨13, 2, 0, 495888, 288827, 1357, 16384⟩
    (by decide) selected_cut_19406

theorem unmarked_context_12_72206_495889 : frontier 9 ⟨495889, by decide⟩
    (prefixCache 12 72206) (prefixPartial 12 72206) = false := by
  decide +kernel

theorem node_context_12_72206_495889 : EJMOriginalGlobalDAGData.nodes 9 ⟨495889, by decide⟩ =
    .split (coordinate 12) (![⟨495777, by decide⟩,⟨495833, by decide⟩,⟨495863, by decide⟩,⟨495888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72206_495889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72206 ⟨495889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72206
    ⟨495889, by decide⟩ (by decide) (![⟨495777, by decide⟩,⟨495833, by decide⟩,⟨495863, by decide⟩,⟨495888, by decide⟩]) unmarked_context_12_72206_495889 node_context_12_72206_495889
  intro a
  fin_cases a
  · exact context_13_288824_495777
  · exact context_13_288825_495833
  · exact context_13_288826_495863
  · exact context_13_288827_495888

theorem selected_cut_19407 : selected 8 ⟨495942, by decide⟩
    (prefixPartial 13 288828) = some ⟨13, 2, 0, 495942, 288828, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_288828_495942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288828 ⟨495942, by decide⟩ :=
  accepted_of_selected 13 288828 ⟨495942, by decide⟩ ⟨13, 2, 0, 495942, 288828, 2033, 16384⟩
    (by decide) selected_cut_19407

theorem selected_cut_19408 : selected 8 ⟨496035, by decide⟩
    (prefixPartial 13 288829) = some ⟨13, 2, 0, 496035, 288829, 3321, 16384⟩ := by
  decide +kernel

theorem context_13_288829_496035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288829 ⟨496035, by decide⟩ :=
  accepted_of_selected 13 288829 ⟨496035, by decide⟩ ⟨13, 2, 0, 496035, 288829, 3321, 16384⟩
    (by decide) selected_cut_19408

theorem selected_cut_19409 : selected 8 ⟨496059, by decide⟩
    (prefixPartial 13 288830) = some ⟨13, 2, 0, 496059, 288830, 505, 16384⟩ := by
  decide +kernel

theorem context_13_288830_496059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288830 ⟨496059, by decide⟩ :=
  accepted_of_selected 13 288830 ⟨496059, by decide⟩ ⟨13, 2, 0, 496059, 288830, 505, 16384⟩
    (by decide) selected_cut_19409

theorem selected_cut_19410 : selected 8 ⟨51129, by decide⟩
    (prefixPartial 13 288831) = some ⟨13, 1, 0, 51129, 288831, 1, 16384⟩ := by
  decide +kernel

theorem context_13_288831_51129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288831 ⟨51129, by decide⟩ :=
  accepted_of_selected 13 288831 ⟨51129, by decide⟩ ⟨13, 1, 0, 51129, 288831, 1, 16384⟩
    (by decide) selected_cut_19410

theorem unmarked_context_12_72207_496060 : frontier 9 ⟨496060, by decide⟩
    (prefixCache 12 72207) (prefixPartial 12 72207) = false := by
  decide +kernel

theorem node_context_12_72207_496060 : EJMOriginalGlobalDAGData.nodes 9 ⟨496060, by decide⟩ =
    .split (coordinate 12) (![⟨495942, by decide⟩,⟨496035, by decide⟩,⟨496059, by decide⟩,⟨51129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72207_496060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72207 ⟨496060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72207
    ⟨496060, by decide⟩ (by decide) (![⟨495942, by decide⟩,⟨496035, by decide⟩,⟨496059, by decide⟩,⟨51129, by decide⟩]) unmarked_context_12_72207_496060 node_context_12_72207_496060
  intro a
  fin_cases a
  · exact context_13_288828_495942
  · exact context_13_288829_496035
  · exact context_13_288830_496059
  · exact context_13_288831_51129

theorem unmarked_context_11_18051_496061 : frontier 10 ⟨496061, by decide⟩
    (prefixCache 11 18051) (prefixPartial 11 18051) = false := by
  decide +kernel

theorem node_context_11_18051_496061 : EJMOriginalGlobalDAGData.nodes 10 ⟨496061, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨495710, by decide⟩,⟨495889, by decide⟩,⟨496060, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18051_496061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18051 ⟨496061, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18051
    ⟨496061, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨495710, by decide⟩,⟨495889, by decide⟩,⟨496060, by decide⟩]) unmarked_context_11_18051_496061 node_context_11_18051_496061
  intro a
  fin_cases a
  · exact context_12_72204_448748
  · exact context_12_72205_495710
  · exact context_12_72206_495889
  · exact context_12_72207_496060

theorem unmarked_context_10_4512_496062 : frontier 11 ⟨496062, by decide⟩
    (prefixCache 10 4512) (prefixPartial 10 4512) = false := by
  decide +kernel

theorem node_context_10_4512_496062 : EJMOriginalGlobalDAGData.nodes 11 ⟨496062, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨495150, by decide⟩,⟨495495, by decide⟩,⟨496061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4512_496062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4512 ⟨496062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4512
    ⟨496062, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨495150, by decide⟩,⟨495495, by decide⟩,⟨496061, by decide⟩]) unmarked_context_10_4512_496062 node_context_10_4512_496062
  intro a
  fin_cases a
  · exact context_11_18048_434745
  · exact context_11_18049_495150
  · exact context_11_18050_495495
  · exact context_11_18051_496061

theorem selected_cut_19411 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 72208) = some ⟨12, 1, 0, 435160, 72208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72208_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72208 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 72208 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 72208, 1, 65536⟩
    (by decide) selected_cut_19411

theorem selected_cut_19412 : selected 8 ⟨496135, by decide⟩
    (prefixPartial 13 288836) = some ⟨13, 2, 0, 496135, 288836, 2837, 16384⟩ := by
  decide +kernel

theorem context_13_288836_496135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288836 ⟨496135, by decide⟩ :=
  accepted_of_selected 13 288836 ⟨496135, by decide⟩ ⟨13, 2, 0, 496135, 288836, 2837, 16384⟩
    (by decide) selected_cut_19412

theorem selected_cut_19413 : selected 8 ⟨496184, by decide⟩
    (prefixPartial 13 288837) = some ⟨13, 2, 0, 496184, 288837, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_288837_496184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288837 ⟨496184, by decide⟩ :=
  accepted_of_selected 13 288837 ⟨496184, by decide⟩ ⟨13, 2, 0, 496184, 288837, 2253, 16384⟩
    (by decide) selected_cut_19413

theorem selected_cut_19414 : selected 8 ⟨496202, by decide⟩
    (prefixPartial 13 288838) = some ⟨13, 2, 0, 496202, 288838, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_288838_496202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288838 ⟨496202, by decide⟩ :=
  accepted_of_selected 13 288838 ⟨496202, by decide⟩ ⟨13, 2, 0, 496202, 288838, 1297, 16384⟩
    (by decide) selected_cut_19414

theorem selected_cut_19415 : selected 8 ⟨496227, by decide⟩
    (prefixPartial 13 288839) = some ⟨13, 2, 0, 496227, 288839, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_288839_496227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288839 ⟨496227, by decide⟩ :=
  accepted_of_selected 13 288839 ⟨496227, by decide⟩ ⟨13, 2, 0, 496227, 288839, 1121, 16384⟩
    (by decide) selected_cut_19415

theorem unmarked_context_12_72209_496228 : frontier 9 ⟨496228, by decide⟩
    (prefixCache 12 72209) (prefixPartial 12 72209) = false := by
  decide +kernel

theorem node_context_12_72209_496228 : EJMOriginalGlobalDAGData.nodes 9 ⟨496228, by decide⟩ =
    .split (coordinate 12) (![⟨496135, by decide⟩,⟨496184, by decide⟩,⟨496202, by decide⟩,⟨496227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72209_496228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72209 ⟨496228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72209
    ⟨496228, by decide⟩ (by decide) (![⟨496135, by decide⟩,⟨496184, by decide⟩,⟨496202, by decide⟩,⟨496227, by decide⟩]) unmarked_context_12_72209_496228 node_context_12_72209_496228
  intro a
  fin_cases a
  · exact context_13_288836_496135
  · exact context_13_288837_496184
  · exact context_13_288838_496202
  · exact context_13_288839_496227

theorem selected_cut_19416 : selected 8 ⟨496287, by decide⟩
    (prefixPartial 13 288840) = some ⟨13, 2, 0, 496287, 288840, 2717, 16384⟩ := by
  decide +kernel

theorem context_13_288840_496287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288840 ⟨496287, by decide⟩ :=
  accepted_of_selected 13 288840 ⟨496287, by decide⟩ ⟨13, 2, 0, 496287, 288840, 2717, 16384⟩
    (by decide) selected_cut_19416

theorem selected_cut_19417 : selected 8 ⟨496318, by decide⟩
    (prefixPartial 13 288841) = some ⟨13, 2, 0, 496318, 288841, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_288841_496318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288841 ⟨496318, by decide⟩ :=
  accepted_of_selected 13 288841 ⟨496318, by decide⟩ ⟨13, 2, 0, 496318, 288841, 2233, 16384⟩
    (by decide) selected_cut_19417

theorem selected_cut_19418 : selected 8 ⟨496337, by decide⟩
    (prefixPartial 13 288842) = some ⟨13, 2, 0, 496337, 288842, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_288842_496337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288842 ⟨496337, by decide⟩ :=
  accepted_of_selected 13 288842 ⟨496337, by decide⟩ ⟨13, 2, 0, 496337, 288842, 1317, 16384⟩
    (by decide) selected_cut_19418

theorem selected_cut_19419 : selected 8 ⟨496349, by decide⟩
    (prefixPartial 13 288843) = some ⟨13, 2, 0, 496349, 288843, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_288843_496349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288843 ⟨496349, by decide⟩ :=
  accepted_of_selected 13 288843 ⟨496349, by decide⟩ ⟨13, 2, 0, 496349, 288843, 1065, 16384⟩
    (by decide) selected_cut_19419

theorem unmarked_context_12_72210_496350 : frontier 9 ⟨496350, by decide⟩
    (prefixCache 12 72210) (prefixPartial 12 72210) = false := by
  decide +kernel

theorem node_context_12_72210_496350 : EJMOriginalGlobalDAGData.nodes 9 ⟨496350, by decide⟩ =
    .split (coordinate 12) (![⟨496287, by decide⟩,⟨496318, by decide⟩,⟨496337, by decide⟩,⟨496349, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72210_496350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72210 ⟨496350, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72210
    ⟨496350, by decide⟩ (by decide) (![⟨496287, by decide⟩,⟨496318, by decide⟩,⟨496337, by decide⟩,⟨496349, by decide⟩]) unmarked_context_12_72210_496350 node_context_12_72210_496350
  intro a
  fin_cases a
  · exact context_13_288840_496287
  · exact context_13_288841_496318
  · exact context_13_288842_496337
  · exact context_13_288843_496349

theorem selected_cut_19420 : selected 8 ⟨496427, by decide⟩
    (prefixPartial 13 288844) = some ⟨13, 2, 0, 496427, 288844, 3193, 16384⟩ := by
  decide +kernel

theorem context_13_288844_496427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288844 ⟨496427, by decide⟩ :=
  accepted_of_selected 13 288844 ⟨496427, by decide⟩ ⟨13, 2, 0, 496427, 288844, 3193, 16384⟩
    (by decide) selected_cut_19420

theorem selected_cut_19421 : selected 8 ⟨496479, by decide⟩
    (prefixPartial 13 288845) = some ⟨13, 2, 0, 496479, 288845, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_288845_496479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288845 ⟨496479, by decide⟩ :=
  accepted_of_selected 13 288845 ⟨496479, by decide⟩ ⟨13, 2, 0, 496479, 288845, 2501, 16384⟩
    (by decide) selected_cut_19421

theorem selected_cut_19422 : selected 8 ⟨496498, by decide⟩
    (prefixPartial 13 288846) = some ⟨13, 2, 0, 496498, 288846, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_288846_496498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288846 ⟨496498, by decide⟩ :=
  accepted_of_selected 13 288846 ⟨496498, by decide⟩ ⟨13, 2, 0, 496498, 288846, 1385, 16384⟩
    (by decide) selected_cut_19422

theorem selected_cut_19423 : selected 8 ⟨496514, by decide⟩
    (prefixPartial 13 288847) = some ⟨13, 2, 0, 496514, 288847, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_288847_496514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288847 ⟨496514, by decide⟩ :=
  accepted_of_selected 13 288847 ⟨496514, by decide⟩ ⟨13, 2, 0, 496514, 288847, 1077, 16384⟩
    (by decide) selected_cut_19423

theorem unmarked_context_12_72211_496515 : frontier 9 ⟨496515, by decide⟩
    (prefixCache 12 72211) (prefixPartial 12 72211) = false := by
  decide +kernel

theorem node_context_12_72211_496515 : EJMOriginalGlobalDAGData.nodes 9 ⟨496515, by decide⟩ =
    .split (coordinate 12) (![⟨496427, by decide⟩,⟨496479, by decide⟩,⟨496498, by decide⟩,⟨496514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72211_496515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72211 ⟨496515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72211
    ⟨496515, by decide⟩ (by decide) (![⟨496427, by decide⟩,⟨496479, by decide⟩,⟨496498, by decide⟩,⟨496514, by decide⟩]) unmarked_context_12_72211_496515 node_context_12_72211_496515
  intro a
  fin_cases a
  · exact context_13_288844_496427
  · exact context_13_288845_496479
  · exact context_13_288846_496498
  · exact context_13_288847_496514

theorem unmarked_context_11_18052_496516 : frontier 10 ⟨496516, by decide⟩
    (prefixCache 11 18052) (prefixPartial 11 18052) = false := by
  decide +kernel

theorem node_context_11_18052_496516 : EJMOriginalGlobalDAGData.nodes 10 ⟨496516, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨496228, by decide⟩,⟨496350, by decide⟩,⟨496515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18052_496516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18052 ⟨496516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18052
    ⟨496516, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨496228, by decide⟩,⟨496350, by decide⟩,⟨496515, by decide⟩]) unmarked_context_11_18052_496516 node_context_11_18052_496516
  intro a
  fin_cases a
  · exact context_12_72208_435160
  · exact context_12_72209_496228
  · exact context_12_72210_496350
  · exact context_12_72211_496515

theorem selected_cut_19424 : selected 8 ⟨496598, by decide⟩
    (prefixPartial 13 288848) = some ⟨13, 2, 0, 496598, 288848, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_288848_496598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288848 ⟨496598, by decide⟩ :=
  accepted_of_selected 13 288848 ⟨496598, by decide⟩ ⟨13, 2, 0, 496598, 288848, 1845, 16384⟩
    (by decide) selected_cut_19424

theorem selected_cut_19425 : selected 8 ⟨496685, by decide⟩
    (prefixPartial 13 288849) = some ⟨13, 2, 0, 496685, 288849, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_288849_496685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288849 ⟨496685, by decide⟩ :=
  accepted_of_selected 13 288849 ⟨496685, by decide⟩ ⟨13, 2, 0, 496685, 288849, 2585, 16384⟩
    (by decide) selected_cut_19425

theorem selected_cut_19426 : selected 8 ⟨496721, by decide⟩
    (prefixPartial 13 288850) = some ⟨13, 2, 0, 496721, 288850, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_288850_496721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288850 ⟨496721, by decide⟩ :=
  accepted_of_selected 13 288850 ⟨496721, by decide⟩ ⟨13, 2, 0, 496721, 288850, 1269, 16384⟩
    (by decide) selected_cut_19426

theorem selected_cut_19427 : selected 8 ⟨496788, by decide⟩
    (prefixPartial 13 288851) = some ⟨13, 2, 0, 496788, 288851, 989, 16384⟩ := by
  decide +kernel

theorem context_13_288851_496788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288851 ⟨496788, by decide⟩ :=
  accepted_of_selected 13 288851 ⟨496788, by decide⟩ ⟨13, 2, 0, 496788, 288851, 989, 16384⟩
    (by decide) selected_cut_19427

theorem unmarked_context_12_72212_496789 : frontier 9 ⟨496789, by decide⟩
    (prefixCache 12 72212) (prefixPartial 12 72212) = false := by
  decide +kernel

theorem node_context_12_72212_496789 : EJMOriginalGlobalDAGData.nodes 9 ⟨496789, by decide⟩ =
    .split (coordinate 12) (![⟨496598, by decide⟩,⟨496685, by decide⟩,⟨496721, by decide⟩,⟨496788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72212_496789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72212 ⟨496789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72212
    ⟨496789, by decide⟩ (by decide) (![⟨496598, by decide⟩,⟨496685, by decide⟩,⟨496721, by decide⟩,⟨496788, by decide⟩]) unmarked_context_12_72212_496789 node_context_12_72212_496789
  intro a
  fin_cases a
  · exact context_13_288848_496598
  · exact context_13_288849_496685
  · exact context_13_288850_496721
  · exact context_13_288851_496788

theorem selected_cut_19428 : selected 8 ⟨496841, by decide⟩
    (prefixPartial 13 288852) = some ⟨13, 2, 0, 496841, 288852, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_288852_496841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288852 ⟨496841, by decide⟩ :=
  accepted_of_selected 13 288852 ⟨496841, by decide⟩ ⟨13, 2, 0, 496841, 288852, 2633, 16384⟩
    (by decide) selected_cut_19428

theorem selected_cut_19429 : selected 8 ⟨496891, by decide⟩
    (prefixPartial 13 288853) = some ⟨13, 2, 0, 496891, 288853, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_288853_496891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288853 ⟨496891, by decide⟩ :=
  accepted_of_selected 13 288853 ⟨496891, by decide⟩ ⟨13, 2, 0, 496891, 288853, 2457, 16384⟩
    (by decide) selected_cut_19429

theorem selected_cut_19430 : selected 8 ⟨496913, by decide⟩
    (prefixPartial 13 288854) = some ⟨13, 2, 0, 496913, 288854, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_288854_496913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288854 ⟨496913, by decide⟩ :=
  accepted_of_selected 13 288854 ⟨496913, by decide⟩ ⟨13, 2, 0, 496913, 288854, 1249, 16384⟩
    (by decide) selected_cut_19430

theorem selected_cut_19431 : selected 8 ⟨496921, by decide⟩
    (prefixPartial 13 288855) = some ⟨13, 2, 0, 496921, 288855, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_288855_496921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288855 ⟨496921, by decide⟩ :=
  accepted_of_selected 13 288855 ⟨496921, by decide⟩ ⟨13, 2, 0, 496921, 288855, 1045, 16384⟩
    (by decide) selected_cut_19431

theorem unmarked_context_12_72213_496922 : frontier 9 ⟨496922, by decide⟩
    (prefixCache 12 72213) (prefixPartial 12 72213) = false := by
  decide +kernel

theorem node_context_12_72213_496922 : EJMOriginalGlobalDAGData.nodes 9 ⟨496922, by decide⟩ =
    .split (coordinate 12) (![⟨496841, by decide⟩,⟨496891, by decide⟩,⟨496913, by decide⟩,⟨496921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72213_496922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72213 ⟨496922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72213
    ⟨496922, by decide⟩ (by decide) (![⟨496841, by decide⟩,⟨496891, by decide⟩,⟨496913, by decide⟩,⟨496921, by decide⟩]) unmarked_context_12_72213_496922 node_context_12_72213_496922
  intro a
  fin_cases a
  · exact context_13_288852_496841
  · exact context_13_288853_496891
  · exact context_13_288854_496913
  · exact context_13_288855_496921

theorem selected_cut_19432 : selected 8 ⟨496969, by decide⟩
    (prefixPartial 13 288856) = some ⟨13, 2, 0, 496969, 288856, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_288856_496969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288856 ⟨496969, by decide⟩ :=
  accepted_of_selected 13 288856 ⟨496969, by decide⟩ ⟨13, 2, 0, 496969, 288856, 2621, 16384⟩
    (by decide) selected_cut_19432

theorem selected_cut_19433 : selected 8 ⟨497000, by decide⟩
    (prefixPartial 13 288857) = some ⟨13, 2, 0, 497000, 288857, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_288857_497000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288857 ⟨497000, by decide⟩ :=
  accepted_of_selected 13 288857 ⟨497000, by decide⟩ ⟨13, 2, 0, 497000, 288857, 2669, 16384⟩
    (by decide) selected_cut_19433

theorem selected_cut_19434 : selected 8 ⟨497022, by decide⟩
    (prefixPartial 13 288858) = some ⟨13, 2, 0, 497022, 288858, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_288858_497022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288858 ⟨497022, by decide⟩ :=
  accepted_of_selected 13 288858 ⟨497022, by decide⟩ ⟨13, 2, 0, 497022, 288858, 1385, 16384⟩
    (by decide) selected_cut_19434

theorem selected_cut_19435 : selected 8 ⟨497038, by decide⟩
    (prefixPartial 13 288859) = some ⟨13, 2, 0, 497038, 288859, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_288859_497038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288859 ⟨497038, by decide⟩ :=
  accepted_of_selected 13 288859 ⟨497038, by decide⟩ ⟨13, 2, 0, 497038, 288859, 1125, 16384⟩
    (by decide) selected_cut_19435

theorem unmarked_context_12_72214_497039 : frontier 9 ⟨497039, by decide⟩
    (prefixCache 12 72214) (prefixPartial 12 72214) = false := by
  decide +kernel

theorem node_context_12_72214_497039 : EJMOriginalGlobalDAGData.nodes 9 ⟨497039, by decide⟩ =
    .split (coordinate 12) (![⟨496969, by decide⟩,⟨497000, by decide⟩,⟨497022, by decide⟩,⟨497038, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72214_497039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72214 ⟨497039, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72214
    ⟨497039, by decide⟩ (by decide) (![⟨496969, by decide⟩,⟨497000, by decide⟩,⟨497022, by decide⟩,⟨497038, by decide⟩]) unmarked_context_12_72214_497039 node_context_12_72214_497039
  intro a
  fin_cases a
  · exact context_13_288856_496969
  · exact context_13_288857_497000
  · exact context_13_288858_497022
  · exact context_13_288859_497038

theorem selected_cut_19436 : selected 8 ⟨497086, by decide⟩
    (prefixPartial 13 288860) = some ⟨13, 2, 0, 497086, 288860, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_288860_497086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288860 ⟨497086, by decide⟩ :=
  accepted_of_selected 13 288860 ⟨497086, by decide⟩ ⟨13, 2, 0, 497086, 288860, 2769, 16384⟩
    (by decide) selected_cut_19436

theorem selected_cut_19437 : selected 8 ⟨497132, by decide⟩
    (prefixPartial 13 288861) = some ⟨13, 2, 0, 497132, 288861, 2869, 16384⟩ := by
  decide +kernel

theorem context_13_288861_497132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288861 ⟨497132, by decide⟩ :=
  accepted_of_selected 13 288861 ⟨497132, by decide⟩ ⟨13, 2, 0, 497132, 288861, 2869, 16384⟩
    (by decide) selected_cut_19437

theorem selected_cut_19438 : selected 8 ⟨497153, by decide⟩
    (prefixPartial 13 288862) = some ⟨13, 2, 0, 497153, 288862, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_288862_497153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288862 ⟨497153, by decide⟩ :=
  accepted_of_selected 13 288862 ⟨497153, by decide⟩ ⟨13, 2, 0, 497153, 288862, 1445, 16384⟩
    (by decide) selected_cut_19438

theorem selected_cut_19439 : selected 8 ⟨497165, by decide⟩
    (prefixPartial 13 288863) = some ⟨13, 2, 0, 497165, 288863, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_288863_497165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288863 ⟨497165, by decide⟩ :=
  accepted_of_selected 13 288863 ⟨497165, by decide⟩ ⟨13, 2, 0, 497165, 288863, 1093, 16384⟩
    (by decide) selected_cut_19439

theorem unmarked_context_12_72215_497166 : frontier 9 ⟨497166, by decide⟩
    (prefixCache 12 72215) (prefixPartial 12 72215) = false := by
  decide +kernel

theorem node_context_12_72215_497166 : EJMOriginalGlobalDAGData.nodes 9 ⟨497166, by decide⟩ =
    .split (coordinate 12) (![⟨497086, by decide⟩,⟨497132, by decide⟩,⟨497153, by decide⟩,⟨497165, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72215_497166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72215 ⟨497166, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72215
    ⟨497166, by decide⟩ (by decide) (![⟨497086, by decide⟩,⟨497132, by decide⟩,⟨497153, by decide⟩,⟨497165, by decide⟩]) unmarked_context_12_72215_497166 node_context_12_72215_497166
  intro a
  fin_cases a
  · exact context_13_288860_497086
  · exact context_13_288861_497132
  · exact context_13_288862_497153
  · exact context_13_288863_497165

theorem unmarked_context_11_18053_497167 : frontier 10 ⟨497167, by decide⟩
    (prefixCache 11 18053) (prefixPartial 11 18053) = false := by
  decide +kernel

theorem node_context_11_18053_497167 : EJMOriginalGlobalDAGData.nodes 10 ⟨497167, by decide⟩ =
    .split (coordinate 11) (![⟨496789, by decide⟩,⟨496922, by decide⟩,⟨497039, by decide⟩,⟨497166, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18053_497167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18053 ⟨497167, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18053
    ⟨497167, by decide⟩ (by decide) (![⟨496789, by decide⟩,⟨496922, by decide⟩,⟨497039, by decide⟩,⟨497166, by decide⟩]) unmarked_context_11_18053_497167 node_context_11_18053_497167
  intro a
  fin_cases a
  · exact context_12_72212_496789
  · exact context_12_72213_496922
  · exact context_12_72214_497039
  · exact context_12_72215_497166

theorem selected_cut_19440 : selected 8 ⟨497230, by decide⟩
    (prefixPartial 13 288864) = some ⟨13, 2, 0, 497230, 288864, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_288864_497230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288864 ⟨497230, by decide⟩ :=
  accepted_of_selected 13 288864 ⟨497230, by decide⟩ ⟨13, 2, 0, 497230, 288864, 2953, 16384⟩
    (by decide) selected_cut_19440

theorem selected_cut_19441 : selected 8 ⟨497284, by decide⟩
    (prefixPartial 13 288865) = some ⟨13, 2, 0, 497284, 288865, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_288865_497284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288865 ⟨497284, by decide⟩ :=
  accepted_of_selected 13 288865 ⟨497284, by decide⟩ ⟨13, 2, 0, 497284, 288865, 3033, 16384⟩
    (by decide) selected_cut_19441

theorem selected_cut_19442 : selected 8 ⟨497311, by decide⟩
    (prefixPartial 13 288866) = some ⟨13, 2, 0, 497311, 288866, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_288866_497311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288866 ⟨497311, by decide⟩ :=
  accepted_of_selected 13 288866 ⟨497311, by decide⟩ ⟨13, 2, 0, 497311, 288866, 1845, 16384⟩
    (by decide) selected_cut_19442

theorem selected_cut_19443 : selected 8 ⟨497338, by decide⟩
    (prefixPartial 13 288867) = some ⟨13, 2, 0, 497338, 288867, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_288867_497338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288867 ⟨497338, by decide⟩ :=
  accepted_of_selected 13 288867 ⟨497338, by decide⟩ ⟨13, 2, 0, 497338, 288867, 1261, 16384⟩
    (by decide) selected_cut_19443

theorem unmarked_context_12_72216_497339 : frontier 9 ⟨497339, by decide⟩
    (prefixCache 12 72216) (prefixPartial 12 72216) = false := by
  decide +kernel

theorem node_context_12_72216_497339 : EJMOriginalGlobalDAGData.nodes 9 ⟨497339, by decide⟩ =
    .split (coordinate 12) (![⟨497230, by decide⟩,⟨497284, by decide⟩,⟨497311, by decide⟩,⟨497338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72216_497339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72216 ⟨497339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72216
    ⟨497339, by decide⟩ (by decide) (![⟨497230, by decide⟩,⟨497284, by decide⟩,⟨497311, by decide⟩,⟨497338, by decide⟩]) unmarked_context_12_72216_497339 node_context_12_72216_497339
  intro a
  fin_cases a
  · exact context_13_288864_497230
  · exact context_13_288865_497284
  · exact context_13_288866_497311
  · exact context_13_288867_497338

theorem selected_cut_19444 : selected 8 ⟨497380, by decide⟩
    (prefixPartial 13 288868) = some ⟨13, 2, 0, 497380, 288868, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_288868_497380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288868 ⟨497380, by decide⟩ :=
  accepted_of_selected 13 288868 ⟨497380, by decide⟩ ⟨13, 2, 0, 497380, 288868, 2037, 16384⟩
    (by decide) selected_cut_19444

theorem selected_cut_19445 : selected 8 ⟨497412, by decide⟩
    (prefixPartial 13 288869) = some ⟨13, 2, 0, 497412, 288869, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_288869_497412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288869 ⟨497412, by decide⟩ :=
  accepted_of_selected 13 288869 ⟨497412, by decide⟩ ⟨13, 2, 0, 497412, 288869, 1913, 16384⟩
    (by decide) selected_cut_19445

theorem selected_cut_19446 : selected 8 ⟨497433, by decide⟩
    (prefixPartial 13 288870) = some ⟨13, 2, 0, 497433, 288870, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_288870_497433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288870 ⟨497433, by decide⟩ :=
  accepted_of_selected 13 288870 ⟨497433, by decide⟩ ⟨13, 2, 0, 497433, 288870, 1257, 16384⟩
    (by decide) selected_cut_19446

theorem selected_cut_19447 : selected 8 ⟨497445, by decide⟩
    (prefixPartial 13 288871) = some ⟨13, 2, 0, 497445, 288871, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_288871_497445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288871 ⟨497445, by decide⟩ :=
  accepted_of_selected 13 288871 ⟨497445, by decide⟩ ⟨13, 2, 0, 497445, 288871, 1085, 16384⟩
    (by decide) selected_cut_19447

theorem unmarked_context_12_72217_497446 : frontier 9 ⟨497446, by decide⟩
    (prefixCache 12 72217) (prefixPartial 12 72217) = false := by
  decide +kernel

theorem node_context_12_72217_497446 : EJMOriginalGlobalDAGData.nodes 9 ⟨497446, by decide⟩ =
    .split (coordinate 12) (![⟨497380, by decide⟩,⟨497412, by decide⟩,⟨497433, by decide⟩,⟨497445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72217_497446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72217 ⟨497446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72217
    ⟨497446, by decide⟩ (by decide) (![⟨497380, by decide⟩,⟨497412, by decide⟩,⟨497433, by decide⟩,⟨497445, by decide⟩]) unmarked_context_12_72217_497446 node_context_12_72217_497446
  intro a
  fin_cases a
  · exact context_13_288868_497380
  · exact context_13_288869_497412
  · exact context_13_288870_497433
  · exact context_13_288871_497445

theorem selected_cut_19448 : selected 8 ⟨497522, by decide⟩
    (prefixPartial 13 288872) = some ⟨13, 2, 0, 497522, 288872, 3349, 16384⟩ := by
  decide +kernel

theorem context_13_288872_497522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288872 ⟨497522, by decide⟩ :=
  accepted_of_selected 13 288872 ⟨497522, by decide⟩ ⟨13, 2, 0, 497522, 288872, 3349, 16384⟩
    (by decide) selected_cut_19448

theorem selected_cut_19449 : selected 8 ⟨497590, by decide⟩
    (prefixPartial 13 288873) = some ⟨13, 2, 0, 497590, 288873, 3561, 16384⟩ := by
  decide +kernel

theorem context_13_288873_497590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288873 ⟨497590, by decide⟩ :=
  accepted_of_selected 13 288873 ⟨497590, by decide⟩ ⟨13, 2, 0, 497590, 288873, 3561, 16384⟩
    (by decide) selected_cut_19449

theorem selected_cut_19450 : selected 8 ⟨497628, by decide⟩
    (prefixPartial 13 288874) = some ⟨13, 2, 0, 497628, 288874, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_288874_497628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288874 ⟨497628, by decide⟩ :=
  accepted_of_selected 13 288874 ⟨497628, by decide⟩ ⟨13, 2, 0, 497628, 288874, 2125, 16384⟩
    (by decide) selected_cut_19450

theorem selected_cut_19451 : selected 8 ⟨497678, by decide⟩
    (prefixPartial 13 288875) = some ⟨13, 2, 0, 497678, 288875, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_288875_497678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288875 ⟨497678, by decide⟩ :=
  accepted_of_selected 13 288875 ⟨497678, by decide⟩ ⟨13, 2, 0, 497678, 288875, 1465, 16384⟩
    (by decide) selected_cut_19451

theorem unmarked_context_12_72218_497679 : frontier 9 ⟨497679, by decide⟩
    (prefixCache 12 72218) (prefixPartial 12 72218) = false := by
  decide +kernel

theorem node_context_12_72218_497679 : EJMOriginalGlobalDAGData.nodes 9 ⟨497679, by decide⟩ =
    .split (coordinate 12) (![⟨497522, by decide⟩,⟨497590, by decide⟩,⟨497628, by decide⟩,⟨497678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72218_497679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72218 ⟨497679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72218
    ⟨497679, by decide⟩ (by decide) (![⟨497522, by decide⟩,⟨497590, by decide⟩,⟨497628, by decide⟩,⟨497678, by decide⟩]) unmarked_context_12_72218_497679 node_context_12_72218_497679
  intro a
  fin_cases a
  · exact context_13_288872_497522
  · exact context_13_288873_497590
  · exact context_13_288874_497628
  · exact context_13_288875_497678

theorem selected_cut_19452 : selected 8 ⟨497726, by decide⟩
    (prefixPartial 13 288876) = some ⟨13, 2, 0, 497726, 288876, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_288876_497726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288876 ⟨497726, by decide⟩ :=
  accepted_of_selected 13 288876 ⟨497726, by decide⟩ ⟨13, 2, 0, 497726, 288876, 2157, 16384⟩
    (by decide) selected_cut_19452

theorem selected_cut_19453 : selected 8 ⟨497778, by decide⟩
    (prefixPartial 13 288877) = some ⟨13, 2, 0, 497778, 288877, 2681, 16384⟩ := by
  decide +kernel

theorem context_13_288877_497778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288877 ⟨497778, by decide⟩ :=
  accepted_of_selected 13 288877 ⟨497778, by decide⟩ ⟨13, 2, 0, 497778, 288877, 2681, 16384⟩
    (by decide) selected_cut_19453

theorem selected_cut_19454 : selected 8 ⟨497797, by decide⟩
    (prefixPartial 13 288878) = some ⟨13, 2, 0, 497797, 288878, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_288878_497797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288878 ⟨497797, by decide⟩ :=
  accepted_of_selected 13 288878 ⟨497797, by decide⟩ ⟨13, 2, 0, 497797, 288878, 1373, 16384⟩
    (by decide) selected_cut_19454

theorem selected_cut_19455 : selected 8 ⟨497813, by decide⟩
    (prefixPartial 13 288879) = some ⟨13, 2, 0, 497813, 288879, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_288879_497813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288879 ⟨497813, by decide⟩ :=
  accepted_of_selected 13 288879 ⟨497813, by decide⟩ ⟨13, 2, 0, 497813, 288879, 1009, 16384⟩
    (by decide) selected_cut_19455

theorem unmarked_context_12_72219_497814 : frontier 9 ⟨497814, by decide⟩
    (prefixCache 12 72219) (prefixPartial 12 72219) = false := by
  decide +kernel

theorem node_context_12_72219_497814 : EJMOriginalGlobalDAGData.nodes 9 ⟨497814, by decide⟩ =
    .split (coordinate 12) (![⟨497726, by decide⟩,⟨497778, by decide⟩,⟨497797, by decide⟩,⟨497813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72219_497814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72219 ⟨497814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72219
    ⟨497814, by decide⟩ (by decide) (![⟨497726, by decide⟩,⟨497778, by decide⟩,⟨497797, by decide⟩,⟨497813, by decide⟩]) unmarked_context_12_72219_497814 node_context_12_72219_497814
  intro a
  fin_cases a
  · exact context_13_288876_497726
  · exact context_13_288877_497778
  · exact context_13_288878_497797
  · exact context_13_288879_497813

theorem unmarked_context_11_18054_497815 : frontier 10 ⟨497815, by decide⟩
    (prefixCache 11 18054) (prefixPartial 11 18054) = false := by
  decide +kernel

theorem node_context_11_18054_497815 : EJMOriginalGlobalDAGData.nodes 10 ⟨497815, by decide⟩ =
    .split (coordinate 11) (![⟨497339, by decide⟩,⟨497446, by decide⟩,⟨497679, by decide⟩,⟨497814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18054_497815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18054 ⟨497815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18054
    ⟨497815, by decide⟩ (by decide) (![⟨497339, by decide⟩,⟨497446, by decide⟩,⟨497679, by decide⟩,⟨497814, by decide⟩]) unmarked_context_11_18054_497815 node_context_11_18054_497815
  intro a
  fin_cases a
  · exact context_12_72216_497339
  · exact context_12_72217_497446
  · exact context_12_72218_497679
  · exact context_12_72219_497814

theorem selected_cut_19456 : selected 8 ⟨497867, by decide⟩
    (prefixPartial 13 288880) = some ⟨13, 2, 0, 497867, 288880, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_288880_497867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288880 ⟨497867, by decide⟩ :=
  accepted_of_selected 13 288880 ⟨497867, by decide⟩ ⟨13, 2, 0, 497867, 288880, 2749, 16384⟩
    (by decide) selected_cut_19456

theorem selected_cut_19457 : selected 8 ⟨497927, by decide⟩
    (prefixPartial 13 288881) = some ⟨13, 2, 0, 497927, 288881, 3765, 16384⟩ := by
  decide +kernel

theorem context_13_288881_497927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288881 ⟨497927, by decide⟩ :=
  accepted_of_selected 13 288881 ⟨497927, by decide⟩ ⟨13, 2, 0, 497927, 288881, 3765, 16384⟩
    (by decide) selected_cut_19457

theorem selected_cut_19458 : selected 8 ⟨497954, by decide⟩
    (prefixPartial 13 288882) = some ⟨13, 2, 0, 497954, 288882, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_288882_497954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288882 ⟨497954, by decide⟩ :=
  accepted_of_selected 13 288882 ⟨497954, by decide⟩ ⟨13, 2, 0, 497954, 288882, 2173, 16384⟩
    (by decide) selected_cut_19458

theorem selected_cut_19459 : selected 8 ⟨497983, by decide⟩
    (prefixPartial 13 288883) = some ⟨13, 2, 0, 497983, 288883, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_288883_497983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288883 ⟨497983, by decide⟩ :=
  accepted_of_selected 13 288883 ⟨497983, by decide⟩ ⟨13, 2, 0, 497983, 288883, 1417, 16384⟩
    (by decide) selected_cut_19459

theorem unmarked_context_12_72220_497984 : frontier 9 ⟨497984, by decide⟩
    (prefixCache 12 72220) (prefixPartial 12 72220) = false := by
  decide +kernel

theorem node_context_12_72220_497984 : EJMOriginalGlobalDAGData.nodes 9 ⟨497984, by decide⟩ =
    .split (coordinate 12) (![⟨497867, by decide⟩,⟨497927, by decide⟩,⟨497954, by decide⟩,⟨497983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72220_497984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72220 ⟨497984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72220
    ⟨497984, by decide⟩ (by decide) (![⟨497867, by decide⟩,⟨497927, by decide⟩,⟨497954, by decide⟩,⟨497983, by decide⟩]) unmarked_context_12_72220_497984 node_context_12_72220_497984
  intro a
  fin_cases a
  · exact context_13_288880_497867
  · exact context_13_288881_497927
  · exact context_13_288882_497954
  · exact context_13_288883_497983

theorem selected_cut_19460 : selected 8 ⟨498019, by decide⟩
    (prefixPartial 13 288884) = some ⟨13, 2, 0, 498019, 288884, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_288884_498019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288884 ⟨498019, by decide⟩ :=
  accepted_of_selected 13 288884 ⟨498019, by decide⟩ ⟨13, 2, 0, 498019, 288884, 1885, 16384⟩
    (by decide) selected_cut_19460

theorem selected_cut_19461 : selected 8 ⟨498064, by decide⟩
    (prefixPartial 13 288885) = some ⟨13, 2, 0, 498064, 288885, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_288885_498064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288885 ⟨498064, by decide⟩ :=
  accepted_of_selected 13 288885 ⟨498064, by decide⟩ ⟨13, 2, 0, 498064, 288885, 2277, 16384⟩
    (by decide) selected_cut_19461

theorem selected_cut_19462 : selected 8 ⟨498082, by decide⟩
    (prefixPartial 13 288886) = some ⟨13, 2, 0, 498082, 288886, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_288886_498082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288886 ⟨498082, by decide⟩ :=
  accepted_of_selected 13 288886 ⟨498082, by decide⟩ ⟨13, 2, 0, 498082, 288886, 1457, 16384⟩
    (by decide) selected_cut_19462

theorem selected_cut_19463 : selected 8 ⟨498094, by decide⟩
    (prefixPartial 13 288887) = some ⟨13, 2, 0, 498094, 288887, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_288887_498094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288887 ⟨498094, by decide⟩ :=
  accepted_of_selected 13 288887 ⟨498094, by decide⟩ ⟨13, 2, 0, 498094, 288887, 1133, 16384⟩
    (by decide) selected_cut_19463

theorem unmarked_context_12_72221_498095 : frontier 9 ⟨498095, by decide⟩
    (prefixCache 12 72221) (prefixPartial 12 72221) = false := by
  decide +kernel

theorem node_context_12_72221_498095 : EJMOriginalGlobalDAGData.nodes 9 ⟨498095, by decide⟩ =
    .split (coordinate 12) (![⟨498019, by decide⟩,⟨498064, by decide⟩,⟨498082, by decide⟩,⟨498094, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72221_498095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72221 ⟨498095, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72221
    ⟨498095, by decide⟩ (by decide) (![⟨498019, by decide⟩,⟨498064, by decide⟩,⟨498082, by decide⟩,⟨498094, by decide⟩]) unmarked_context_12_72221_498095 node_context_12_72221_498095
  intro a
  fin_cases a
  · exact context_13_288884_498019
  · exact context_13_288885_498064
  · exact context_13_288886_498082
  · exact context_13_288887_498094

theorem selected_cut_19464 : selected 8 ⟨498133, by decide⟩
    (prefixPartial 13 288888) = some ⟨13, 2, 0, 498133, 288888, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_288888_498133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288888 ⟨498133, by decide⟩ :=
  accepted_of_selected 13 288888 ⟨498133, by decide⟩ ⟨13, 2, 0, 498133, 288888, 1961, 16384⟩
    (by decide) selected_cut_19464

theorem selected_cut_19465 : selected 8 ⟨498169, by decide⟩
    (prefixPartial 13 288889) = some ⟨13, 2, 0, 498169, 288889, 2749, 16384⟩ := by
  decide +kernel

theorem context_13_288889_498169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288889 ⟨498169, by decide⟩ :=
  accepted_of_selected 13 288889 ⟨498169, by decide⟩ ⟨13, 2, 0, 498169, 288889, 2749, 16384⟩
    (by decide) selected_cut_19465

theorem selected_cut_19466 : selected 8 ⟨498188, by decide⟩
    (prefixPartial 13 288890) = some ⟨13, 2, 0, 498188, 288890, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_288890_498188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288890 ⟨498188, by decide⟩ :=
  accepted_of_selected 13 288890 ⟨498188, by decide⟩ ⟨13, 2, 0, 498188, 288890, 1613, 16384⟩
    (by decide) selected_cut_19466

theorem selected_cut_19467 : selected 8 ⟨498200, by decide⟩
    (prefixPartial 13 288891) = some ⟨13, 2, 0, 498200, 288891, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_288891_498200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288891 ⟨498200, by decide⟩ :=
  accepted_of_selected 13 288891 ⟨498200, by decide⟩ ⟨13, 2, 0, 498200, 288891, 1137, 16384⟩
    (by decide) selected_cut_19467

theorem unmarked_context_12_72222_498201 : frontier 9 ⟨498201, by decide⟩
    (prefixCache 12 72222) (prefixPartial 12 72222) = false := by
  decide +kernel

theorem node_context_12_72222_498201 : EJMOriginalGlobalDAGData.nodes 9 ⟨498201, by decide⟩ =
    .split (coordinate 12) (![⟨498133, by decide⟩,⟨498169, by decide⟩,⟨498188, by decide⟩,⟨498200, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72222_498201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72222 ⟨498201, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72222
    ⟨498201, by decide⟩ (by decide) (![⟨498133, by decide⟩,⟨498169, by decide⟩,⟨498188, by decide⟩,⟨498200, by decide⟩]) unmarked_context_12_72222_498201 node_context_12_72222_498201
  intro a
  fin_cases a
  · exact context_13_288888_498133
  · exact context_13_288889_498169
  · exact context_13_288890_498188
  · exact context_13_288891_498200

theorem selected_cut_19468 : selected 8 ⟨498237, by decide⟩
    (prefixPartial 13 288892) = some ⟨13, 2, 0, 498237, 288892, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_288892_498237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288892 ⟨498237, by decide⟩ :=
  accepted_of_selected 13 288892 ⟨498237, by decide⟩ ⟨13, 2, 0, 498237, 288892, 1913, 16384⟩
    (by decide) selected_cut_19468

theorem selected_cut_19469 : selected 8 ⟨498283, by decide⟩
    (prefixPartial 13 288893) = some ⟨13, 2, 0, 498283, 288893, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_288893_498283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288893 ⟨498283, by decide⟩ :=
  accepted_of_selected 13 288893 ⟨498283, by decide⟩ ⟨13, 2, 0, 498283, 288893, 2933, 16384⟩
    (by decide) selected_cut_19469

theorem selected_cut_19470 : selected 8 ⟨498300, by decide⟩
    (prefixPartial 13 288894) = some ⟨13, 2, 0, 498300, 288894, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_288894_498300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288894 ⟨498300, by decide⟩ :=
  accepted_of_selected 13 288894 ⟨498300, by decide⟩ ⟨13, 2, 0, 498300, 288894, 1725, 16384⟩
    (by decide) selected_cut_19470

theorem selected_cut_19471 : selected 8 ⟨498314, by decide⟩
    (prefixPartial 13 288895) = some ⟨13, 2, 0, 498314, 288895, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_288895_498314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288895 ⟨498314, by decide⟩ :=
  accepted_of_selected 13 288895 ⟨498314, by decide⟩ ⟨13, 2, 0, 498314, 288895, 1117, 16384⟩
    (by decide) selected_cut_19471

theorem unmarked_context_12_72223_498315 : frontier 9 ⟨498315, by decide⟩
    (prefixCache 12 72223) (prefixPartial 12 72223) = false := by
  decide +kernel

theorem node_context_12_72223_498315 : EJMOriginalGlobalDAGData.nodes 9 ⟨498315, by decide⟩ =
    .split (coordinate 12) (![⟨498237, by decide⟩,⟨498283, by decide⟩,⟨498300, by decide⟩,⟨498314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72223_498315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72223 ⟨498315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72223
    ⟨498315, by decide⟩ (by decide) (![⟨498237, by decide⟩,⟨498283, by decide⟩,⟨498300, by decide⟩,⟨498314, by decide⟩]) unmarked_context_12_72223_498315 node_context_12_72223_498315
  intro a
  fin_cases a
  · exact context_13_288892_498237
  · exact context_13_288893_498283
  · exact context_13_288894_498300
  · exact context_13_288895_498314

theorem unmarked_context_11_18055_498316 : frontier 10 ⟨498316, by decide⟩
    (prefixCache 11 18055) (prefixPartial 11 18055) = false := by
  decide +kernel

theorem node_context_11_18055_498316 : EJMOriginalGlobalDAGData.nodes 10 ⟨498316, by decide⟩ =
    .split (coordinate 11) (![⟨497984, by decide⟩,⟨498095, by decide⟩,⟨498201, by decide⟩,⟨498315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18055_498316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18055 ⟨498316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18055
    ⟨498316, by decide⟩ (by decide) (![⟨497984, by decide⟩,⟨498095, by decide⟩,⟨498201, by decide⟩,⟨498315, by decide⟩]) unmarked_context_11_18055_498316 node_context_11_18055_498316
  intro a
  fin_cases a
  · exact context_12_72220_497984
  · exact context_12_72221_498095
  · exact context_12_72222_498201
  · exact context_12_72223_498315

theorem unmarked_context_10_4513_498317 : frontier 11 ⟨498317, by decide⟩
    (prefixCache 10 4513) (prefixPartial 10 4513) = false := by
  decide +kernel

theorem node_context_10_4513_498317 : EJMOriginalGlobalDAGData.nodes 11 ⟨498317, by decide⟩ =
    .split (coordinate 10) (![⟨496516, by decide⟩,⟨497167, by decide⟩,⟨497815, by decide⟩,⟨498316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4513_498317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4513 ⟨498317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4513
    ⟨498317, by decide⟩ (by decide) (![⟨496516, by decide⟩,⟨497167, by decide⟩,⟨497815, by decide⟩,⟨498316, by decide⟩]) unmarked_context_10_4513_498317 node_context_10_4513_498317
  intro a
  fin_cases a
  · exact context_11_18052_496516
  · exact context_11_18053_497167
  · exact context_11_18054_497815
  · exact context_11_18055_498316

theorem selected_cut_19472 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 72224) = some ⟨12, 1, 0, 435790, 72224, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72224_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72224 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 72224 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 72224, 1, 65536⟩
    (by decide) selected_cut_19472

theorem selected_cut_19473 : selected 8 ⟨498339, by decide⟩
    (prefixPartial 13 288900) = some ⟨13, 2, 0, 498339, 288900, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_288900_498339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288900 ⟨498339, by decide⟩ :=
  accepted_of_selected 13 288900 ⟨498339, by decide⟩ ⟨13, 2, 0, 498339, 288900, 1265, 16384⟩
    (by decide) selected_cut_19473

theorem selected_cut_19474 : selected 8 ⟨498383, by decide⟩
    (prefixPartial 13 288901) = some ⟨13, 2, 0, 498383, 288901, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_288901_498383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288901 ⟨498383, by decide⟩ :=
  accepted_of_selected 13 288901 ⟨498383, by decide⟩ ⟨13, 2, 0, 498383, 288901, 2385, 16384⟩
    (by decide) selected_cut_19474

theorem selected_cut_19475 : selected 8 ⟨498399, by decide⟩
    (prefixPartial 13 288902) = some ⟨13, 2, 0, 498399, 288902, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_288902_498399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288902 ⟨498399, by decide⟩ :=
  accepted_of_selected 13 288902 ⟨498399, by decide⟩ ⟨13, 2, 0, 498399, 288902, 1413, 16384⟩
    (by decide) selected_cut_19475

theorem selected_cut_19476 : selected 8 ⟨498410, by decide⟩
    (prefixPartial 13 288903) = some ⟨13, 2, 0, 498410, 288903, 997, 16384⟩ := by
  decide +kernel

theorem context_13_288903_498410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288903 ⟨498410, by decide⟩ :=
  accepted_of_selected 13 288903 ⟨498410, by decide⟩ ⟨13, 2, 0, 498410, 288903, 997, 16384⟩
    (by decide) selected_cut_19476

theorem unmarked_context_12_72225_498411 : frontier 9 ⟨498411, by decide⟩
    (prefixCache 12 72225) (prefixPartial 12 72225) = false := by
  decide +kernel

theorem node_context_12_72225_498411 : EJMOriginalGlobalDAGData.nodes 9 ⟨498411, by decide⟩ =
    .split (coordinate 12) (![⟨498339, by decide⟩,⟨498383, by decide⟩,⟨498399, by decide⟩,⟨498410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72225_498411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72225 ⟨498411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72225
    ⟨498411, by decide⟩ (by decide) (![⟨498339, by decide⟩,⟨498383, by decide⟩,⟨498399, by decide⟩,⟨498410, by decide⟩]) unmarked_context_12_72225_498411 node_context_12_72225_498411
  intro a
  fin_cases a
  · exact context_13_288900_498339
  · exact context_13_288901_498383
  · exact context_13_288902_498399
  · exact context_13_288903_498410

theorem selected_cut_19477 : selected 8 ⟨498430, by decide⟩
    (prefixPartial 13 288904) = some ⟨13, 2, 0, 498430, 288904, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_288904_498430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288904 ⟨498430, by decide⟩ :=
  accepted_of_selected 13 288904 ⟨498430, by decide⟩ ⟨13, 2, 0, 498430, 288904, 1145, 16384⟩
    (by decide) selected_cut_19477

theorem selected_cut_19478 : selected 8 ⟨498461, by decide⟩
    (prefixPartial 13 288905) = some ⟨13, 2, 0, 498461, 288905, 2133, 16384⟩ := by
  decide +kernel

theorem context_13_288905_498461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288905 ⟨498461, by decide⟩ :=
  accepted_of_selected 13 288905 ⟨498461, by decide⟩ ⟨13, 2, 0, 498461, 288905, 2133, 16384⟩
    (by decide) selected_cut_19478

theorem selected_cut_19479 : selected 8 ⟨498477, by decide⟩
    (prefixPartial 13 288906) = some ⟨13, 2, 0, 498477, 288906, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_288906_498477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288906 ⟨498477, by decide⟩ :=
  accepted_of_selected 13 288906 ⟨498477, by decide⟩ ⟨13, 2, 0, 498477, 288906, 1289, 16384⟩
    (by decide) selected_cut_19479

theorem selected_cut_19480 : selected 8 ⟨498484, by decide⟩
    (prefixPartial 13 288907) = some ⟨13, 2, 0, 498484, 288907, 849, 16384⟩ := by
  decide +kernel

theorem context_13_288907_498484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288907 ⟨498484, by decide⟩ :=
  accepted_of_selected 13 288907 ⟨498484, by decide⟩ ⟨13, 2, 0, 498484, 288907, 849, 16384⟩
    (by decide) selected_cut_19480

theorem unmarked_context_12_72226_498485 : frontier 9 ⟨498485, by decide⟩
    (prefixCache 12 72226) (prefixPartial 12 72226) = false := by
  decide +kernel

theorem node_context_12_72226_498485 : EJMOriginalGlobalDAGData.nodes 9 ⟨498485, by decide⟩ =
    .split (coordinate 12) (![⟨498430, by decide⟩,⟨498461, by decide⟩,⟨498477, by decide⟩,⟨498484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72226_498485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72226 ⟨498485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72226
    ⟨498485, by decide⟩ (by decide) (![⟨498430, by decide⟩,⟨498461, by decide⟩,⟨498477, by decide⟩,⟨498484, by decide⟩]) unmarked_context_12_72226_498485 node_context_12_72226_498485
  intro a
  fin_cases a
  · exact context_13_288904_498430
  · exact context_13_288905_498461
  · exact context_13_288906_498477
  · exact context_13_288907_498484

theorem selected_cut_19481 : selected 8 ⟨498509, by decide⟩
    (prefixPartial 13 288908) = some ⟨13, 2, 0, 498509, 288908, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_288908_498509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288908 ⟨498509, by decide⟩ :=
  accepted_of_selected 13 288908 ⟨498509, by decide⟩ ⟨13, 2, 0, 498509, 288908, 1309, 16384⟩
    (by decide) selected_cut_19481

theorem selected_cut_19482 : selected 8 ⟨498548, by decide⟩
    (prefixPartial 13 288909) = some ⟨13, 2, 0, 498548, 288909, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_288909_498548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288909 ⟨498548, by decide⟩ :=
  accepted_of_selected 13 288909 ⟨498548, by decide⟩ ⟨13, 2, 0, 498548, 288909, 2577, 16384⟩
    (by decide) selected_cut_19482

theorem selected_cut_19483 : selected 8 ⟨498566, by decide⟩
    (prefixPartial 13 288910) = some ⟨13, 2, 0, 498566, 288910, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_288910_498566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288910 ⟨498566, by decide⟩ :=
  accepted_of_selected 13 288910 ⟨498566, by decide⟩ ⟨13, 2, 0, 498566, 288910, 1745, 16384⟩
    (by decide) selected_cut_19483

theorem selected_cut_19484 : selected 8 ⟨498573, by decide⟩
    (prefixPartial 13 288911) = some ⟨13, 2, 0, 498573, 288911, 989, 16384⟩ := by
  decide +kernel

theorem context_13_288911_498573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288911 ⟨498573, by decide⟩ :=
  accepted_of_selected 13 288911 ⟨498573, by decide⟩ ⟨13, 2, 0, 498573, 288911, 989, 16384⟩
    (by decide) selected_cut_19484

theorem unmarked_context_12_72227_498574 : frontier 9 ⟨498574, by decide⟩
    (prefixCache 12 72227) (prefixPartial 12 72227) = false := by
  decide +kernel

theorem node_context_12_72227_498574 : EJMOriginalGlobalDAGData.nodes 9 ⟨498574, by decide⟩ =
    .split (coordinate 12) (![⟨498509, by decide⟩,⟨498548, by decide⟩,⟨498566, by decide⟩,⟨498573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72227_498574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72227 ⟨498574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72227
    ⟨498574, by decide⟩ (by decide) (![⟨498509, by decide⟩,⟨498548, by decide⟩,⟨498566, by decide⟩,⟨498573, by decide⟩]) unmarked_context_12_72227_498574 node_context_12_72227_498574
  intro a
  fin_cases a
  · exact context_13_288908_498509
  · exact context_13_288909_498548
  · exact context_13_288910_498566
  · exact context_13_288911_498573

theorem unmarked_context_11_18056_498575 : frontier 10 ⟨498575, by decide⟩
    (prefixCache 11 18056) (prefixPartial 11 18056) = false := by
  decide +kernel

theorem node_context_11_18056_498575 : EJMOriginalGlobalDAGData.nodes 10 ⟨498575, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨498411, by decide⟩,⟨498485, by decide⟩,⟨498574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18056_498575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18056 ⟨498575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18056
    ⟨498575, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨498411, by decide⟩,⟨498485, by decide⟩,⟨498574, by decide⟩]) unmarked_context_11_18056_498575 node_context_11_18056_498575
  intro a
  fin_cases a
  · exact context_12_72224_435790
  · exact context_12_72225_498411
  · exact context_12_72226_498485
  · exact context_12_72227_498574

theorem selected_cut_19485 : selected 8 ⟨498607, by decide⟩
    (prefixPartial 13 288912) = some ⟨13, 2, 0, 498607, 288912, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_288912_498607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288912 ⟨498607, by decide⟩ :=
  accepted_of_selected 13 288912 ⟨498607, by decide⟩ ⟨13, 2, 0, 498607, 288912, 1821, 16384⟩
    (by decide) selected_cut_19485

theorem selected_cut_19486 : selected 8 ⟨498672, by decide⟩
    (prefixPartial 13 288913) = some ⟨13, 2, 0, 498672, 288913, 3517, 16384⟩ := by
  decide +kernel

theorem context_13_288913_498672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288913 ⟨498672, by decide⟩ :=
  accepted_of_selected 13 288913 ⟨498672, by decide⟩ ⟨13, 2, 0, 498672, 288913, 3517, 16384⟩
    (by decide) selected_cut_19486

theorem selected_cut_19487 : selected 8 ⟨498700, by decide⟩
    (prefixPartial 13 288914) = some ⟨13, 2, 0, 498700, 288914, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_288914_498700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288914 ⟨498700, by decide⟩ :=
  accepted_of_selected 13 288914 ⟨498700, by decide⟩ ⟨13, 2, 0, 498700, 288914, 1977, 16384⟩
    (by decide) selected_cut_19487

theorem selected_cut_19488 : selected 8 ⟨498725, by decide⟩
    (prefixPartial 13 288915) = some ⟨13, 2, 0, 498725, 288915, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_288915_498725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288915 ⟨498725, by decide⟩ :=
  accepted_of_selected 13 288915 ⟨498725, by decide⟩ ⟨13, 2, 0, 498725, 288915, 1381, 16384⟩
    (by decide) selected_cut_19488

theorem unmarked_context_12_72228_498726 : frontier 9 ⟨498726, by decide⟩
    (prefixCache 12 72228) (prefixPartial 12 72228) = false := by
  decide +kernel

theorem node_context_12_72228_498726 : EJMOriginalGlobalDAGData.nodes 9 ⟨498726, by decide⟩ =
    .split (coordinate 12) (![⟨498607, by decide⟩,⟨498672, by decide⟩,⟨498700, by decide⟩,⟨498725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72228_498726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72228 ⟨498726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72228
    ⟨498726, by decide⟩ (by decide) (![⟨498607, by decide⟩,⟨498672, by decide⟩,⟨498700, by decide⟩,⟨498725, by decide⟩]) unmarked_context_12_72228_498726 node_context_12_72228_498726
  intro a
  fin_cases a
  · exact context_13_288912_498607
  · exact context_13_288913_498672
  · exact context_13_288914_498700
  · exact context_13_288915_498725

theorem selected_cut_19489 : selected 8 ⟨498749, by decide⟩
    (prefixPartial 13 288916) = some ⟨13, 2, 0, 498749, 288916, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_288916_498749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288916 ⟨498749, by decide⟩ :=
  accepted_of_selected 13 288916 ⟨498749, by decide⟩ ⟨13, 2, 0, 498749, 288916, 1205, 16384⟩
    (by decide) selected_cut_19489

theorem selected_cut_19490 : selected 8 ⟨498780, by decide⟩
    (prefixPartial 13 288917) = some ⟨13, 2, 0, 498780, 288917, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_288917_498780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 288917 ⟨498780, by decide⟩ :=
  accepted_of_selected 13 288917 ⟨498780, by decide⟩ ⟨13, 2, 0, 498780, 288917, 2017, 16384⟩
    (by decide) selected_cut_19490

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
