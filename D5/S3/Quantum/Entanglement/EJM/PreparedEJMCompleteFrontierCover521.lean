/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover520
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_50020 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 421660) = some ⟨12, 1, 0, 1415033, 421660, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421660_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421660 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 421660 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 421660, 1, 65536⟩
    (by decide) selected_cut_50020

theorem selected_cut_50021 : selected 9 ⟨1421854, by decide⟩
    (prefixPartial 12 421661) = some ⟨12, 2, 0, 1421854, 421661, 2465, 65536⟩ := by
  decide +kernel

theorem context_12_421661_1421854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421661 ⟨1421854, by decide⟩ :=
  accepted_of_selected 12 421661 ⟨1421854, by decide⟩ ⟨12, 2, 0, 1421854, 421661, 2465, 65536⟩
    (by decide) selected_cut_50021

theorem selected_cut_50022 : selected 9 ⟨1421921, by decide⟩
    (prefixPartial 12 421662) = some ⟨12, 2, 0, 1421921, 421662, 2541, 65536⟩ := by
  decide +kernel

theorem context_12_421662_1421921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421662 ⟨1421921, by decide⟩ :=
  accepted_of_selected 12 421662 ⟨1421921, by decide⟩ ⟨12, 2, 0, 1421921, 421662, 2541, 65536⟩
    (by decide) selected_cut_50022

theorem selected_cut_50023 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 421663) = some ⟨12, 1, 0, 903806, 421663, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421663_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421663 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 421663 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 421663, 1, 65536⟩
    (by decide) selected_cut_50023

theorem unmarked_context_11_105415_1421922 : frontier 10 ⟨1421922, by decide⟩
    (prefixCache 11 105415) (prefixPartial 11 105415) = false := by
  decide +kernel

theorem node_context_11_105415_1421922 : EJMOriginalGlobalDAGData.nodes 10 ⟨1421922, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1421854, by decide⟩,⟨1421921, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105415_1421922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105415 ⟨1421922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105415
    ⟨1421922, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1421854, by decide⟩,⟨1421921, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_105415_1421922 node_context_11_105415_1421922
  intro a
  fin_cases a
  · exact context_12_421660_1415033
  · exact context_12_421661_1421854
  · exact context_12_421662_1421921
  · exact context_12_421663_903806

theorem unmarked_context_10_26353_1421923 : frontier 11 ⟨1421923, by decide⟩
    (prefixCache 10 26353) (prefixPartial 10 26353) = false := by
  decide +kernel

theorem node_context_10_26353_1421923 : EJMOriginalGlobalDAGData.nodes 11 ⟨1421923, by decide⟩ =
    .split (coordinate 10) (![⟨1421562, by decide⟩,⟨1241271, by decide⟩,⟨1421782, by decide⟩,⟨1421922, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26353_1421923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26353 ⟨1421923, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26353
    ⟨1421923, by decide⟩ (by decide) (![⟨1421562, by decide⟩,⟨1241271, by decide⟩,⟨1421782, by decide⟩,⟨1421922, by decide⟩]) unmarked_context_10_26353_1421923 node_context_10_26353_1421923
  intro a
  fin_cases a
  · exact context_11_105412_1421562
  · exact context_11_105413_1241271
  · exact context_11_105414_1421782
  · exact context_11_105415_1421922

theorem selected_cut_50024 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 421664) = some ⟨12, 1, 0, 435160, 421664, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421664_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421664 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 421664 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 421664, 1, 65536⟩
    (by decide) selected_cut_50024

theorem selected_cut_50025 : selected 9 ⟨1421997, by decide⟩
    (prefixPartial 12 421665) = some ⟨12, 2, 0, 1421997, 421665, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_421665_1421997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421665 ⟨1421997, by decide⟩ :=
  accepted_of_selected 12 421665 ⟨1421997, by decide⟩ ⟨12, 2, 0, 1421997, 421665, 2493, 65536⟩
    (by decide) selected_cut_50025

theorem selected_cut_50026 : selected 9 ⟨1422076, by decide⟩
    (prefixPartial 12 421666) = some ⟨12, 2, 0, 1422076, 421666, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_421666_1422076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421666 ⟨1422076, by decide⟩ :=
  accepted_of_selected 12 421666 ⟨1422076, by decide⟩ ⟨12, 2, 0, 1422076, 421666, 2405, 65536⟩
    (by decide) selected_cut_50026

theorem selected_cut_50027 : selected 9 ⟨1422144, by decide⟩
    (prefixPartial 12 421667) = some ⟨12, 2, 0, 1422144, 421667, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_421667_1422144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421667 ⟨1422144, by decide⟩ :=
  accepted_of_selected 12 421667 ⟨1422144, by decide⟩ ⟨12, 2, 0, 1422144, 421667, 2421, 65536⟩
    (by decide) selected_cut_50027

theorem unmarked_context_11_105416_1422145 : frontier 10 ⟨1422145, by decide⟩
    (prefixCache 11 105416) (prefixPartial 11 105416) = false := by
  decide +kernel

theorem node_context_11_105416_1422145 : EJMOriginalGlobalDAGData.nodes 10 ⟨1422145, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1421997, by decide⟩,⟨1422076, by decide⟩,⟨1422144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105416_1422145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105416 ⟨1422145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105416
    ⟨1422145, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1421997, by decide⟩,⟨1422076, by decide⟩,⟨1422144, by decide⟩]) unmarked_context_11_105416_1422145 node_context_11_105416_1422145
  intro a
  fin_cases a
  · exact context_12_421664_435160
  · exact context_12_421665_1421997
  · exact context_12_421666_1422076
  · exact context_12_421667_1422144

theorem selected_cut_50028 : selected 10 ⟨1422253, by decide⟩
    (prefixPartial 11 105417) = some ⟨11, 2, 0, 1422253, 105417, 3837, 262144⟩ := by
  decide +kernel

theorem context_11_105417_1422253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105417 ⟨1422253, by decide⟩ :=
  accepted_of_selected 11 105417 ⟨1422253, by decide⟩ ⟨11, 2, 0, 1422253, 105417, 3837, 262144⟩
    (by decide) selected_cut_50028

theorem selected_cut_50029 : selected 10 ⟨1422372, by decide⟩
    (prefixPartial 11 105418) = some ⟨11, 2, 0, 1422372, 105418, 2909, 262144⟩ := by
  decide +kernel

theorem context_11_105418_1422372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105418 ⟨1422372, by decide⟩ :=
  accepted_of_selected 11 105418 ⟨1422372, by decide⟩ ⟨11, 2, 0, 1422372, 105418, 2909, 262144⟩
    (by decide) selected_cut_50029

theorem selected_cut_50030 : selected 9 ⟨1422427, by decide⟩
    (prefixPartial 12 421676) = some ⟨12, 2, 0, 1422427, 421676, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_421676_1422427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421676 ⟨1422427, by decide⟩ :=
  accepted_of_selected 12 421676 ⟨1422427, by decide⟩ ⟨12, 2, 0, 1422427, 421676, 1745, 65536⟩
    (by decide) selected_cut_50030

theorem selected_cut_50031 : selected 9 ⟨1422478, by decide⟩
    (prefixPartial 12 421677) = some ⟨12, 2, 0, 1422478, 421677, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_421677_1422478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421677 ⟨1422478, by decide⟩ :=
  accepted_of_selected 12 421677 ⟨1422478, by decide⟩ ⟨12, 2, 0, 1422478, 421677, 1869, 65536⟩
    (by decide) selected_cut_50031

theorem selected_cut_50032 : selected 9 ⟨1422522, by decide⟩
    (prefixPartial 12 421678) = some ⟨12, 2, 0, 1422522, 421678, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_421678_1422522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421678 ⟨1422522, by decide⟩ :=
  accepted_of_selected 12 421678 ⟨1422522, by decide⟩ ⟨12, 2, 0, 1422522, 421678, 1705, 65536⟩
    (by decide) selected_cut_50032

theorem selected_cut_50033 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 421679) = some ⟨12, 1, 0, 903806, 421679, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421679_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421679 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 421679 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 421679, 1, 65536⟩
    (by decide) selected_cut_50033

theorem unmarked_context_11_105419_1422523 : frontier 10 ⟨1422523, by decide⟩
    (prefixCache 11 105419) (prefixPartial 11 105419) = false := by
  decide +kernel

theorem node_context_11_105419_1422523 : EJMOriginalGlobalDAGData.nodes 10 ⟨1422523, by decide⟩ =
    .split (coordinate 11) (![⟨1422427, by decide⟩,⟨1422478, by decide⟩,⟨1422522, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105419_1422523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105419 ⟨1422523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105419
    ⟨1422523, by decide⟩ (by decide) (![⟨1422427, by decide⟩,⟨1422478, by decide⟩,⟨1422522, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_105419_1422523 node_context_11_105419_1422523
  intro a
  fin_cases a
  · exact context_12_421676_1422427
  · exact context_12_421677_1422478
  · exact context_12_421678_1422522
  · exact context_12_421679_903806

theorem unmarked_context_10_26354_1422524 : frontier 11 ⟨1422524, by decide⟩
    (prefixCache 10 26354) (prefixPartial 10 26354) = false := by
  decide +kernel

theorem node_context_10_26354_1422524 : EJMOriginalGlobalDAGData.nodes 11 ⟨1422524, by decide⟩ =
    .split (coordinate 10) (![⟨1422145, by decide⟩,⟨1422253, by decide⟩,⟨1422372, by decide⟩,⟨1422523, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26354_1422524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26354 ⟨1422524, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26354
    ⟨1422524, by decide⟩ (by decide) (![⟨1422145, by decide⟩,⟨1422253, by decide⟩,⟨1422372, by decide⟩,⟨1422523, by decide⟩]) unmarked_context_10_26354_1422524 node_context_10_26354_1422524
  intro a
  fin_cases a
  · exact context_11_105416_1422145
  · exact context_11_105417_1422253
  · exact context_11_105418_1422372
  · exact context_11_105419_1422523

theorem selected_cut_50034 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 421680) = some ⟨12, 1, 0, 1416143, 421680, 1, 65536⟩ := by
  decide +kernel

theorem context_12_421680_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421680 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 421680 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 421680, 1, 65536⟩
    (by decide) selected_cut_50034

theorem selected_cut_50035 : selected 9 ⟨1422592, by decide⟩
    (prefixPartial 12 421681) = some ⟨12, 2, 0, 1422592, 421681, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_421681_1422592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421681 ⟨1422592, by decide⟩ :=
  accepted_of_selected 12 421681 ⟨1422592, by decide⟩ ⟨12, 2, 0, 1422592, 421681, 1757, 65536⟩
    (by decide) selected_cut_50035

theorem selected_cut_50036 : selected 9 ⟨1422640, by decide⟩
    (prefixPartial 12 421682) = some ⟨12, 2, 0, 1422640, 421682, 1605, 65536⟩ := by
  decide +kernel

theorem context_12_421682_1422640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421682 ⟨1422640, by decide⟩ :=
  accepted_of_selected 12 421682 ⟨1422640, by decide⟩ ⟨12, 2, 0, 1422640, 421682, 1605, 65536⟩
    (by decide) selected_cut_50036

theorem selected_cut_50037 : selected 9 ⟨1422698, by decide⟩
    (prefixPartial 12 421683) = some ⟨12, 2, 0, 1422698, 421683, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_421683_1422698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 421683 ⟨1422698, by decide⟩ :=
  accepted_of_selected 12 421683 ⟨1422698, by decide⟩ ⟨12, 2, 0, 1422698, 421683, 1669, 65536⟩
    (by decide) selected_cut_50037

theorem unmarked_context_11_105420_1422699 : frontier 10 ⟨1422699, by decide⟩
    (prefixCache 11 105420) (prefixPartial 11 105420) = false := by
  decide +kernel

theorem node_context_11_105420_1422699 : EJMOriginalGlobalDAGData.nodes 10 ⟨1422699, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1422592, by decide⟩,⟨1422640, by decide⟩,⟨1422698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105420_1422699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105420 ⟨1422699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105420
    ⟨1422699, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1422592, by decide⟩,⟨1422640, by decide⟩,⟨1422698, by decide⟩]) unmarked_context_11_105420_1422699 node_context_11_105420_1422699
  intro a
  fin_cases a
  · exact context_12_421680_1416143
  · exact context_12_421681_1422592
  · exact context_12_421682_1422640
  · exact context_12_421683_1422698

theorem selected_cut_50038 : selected 10 ⟨1422791, by decide⟩
    (prefixPartial 11 105421) = some ⟨11, 2, 0, 1422791, 105421, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_105421_1422791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105421 ⟨1422791, by decide⟩ :=
  accepted_of_selected 11 105421 ⟨1422791, by decide⟩ ⟨11, 2, 0, 1422791, 105421, 2569, 262144⟩
    (by decide) selected_cut_50038

theorem selected_cut_50039 : selected 10 ⟨1422861, by decide⟩
    (prefixPartial 11 105422) = some ⟨11, 2, 0, 1422861, 105422, 1081, 262144⟩ := by
  decide +kernel

theorem context_11_105422_1422861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105422 ⟨1422861, by decide⟩ :=
  accepted_of_selected 11 105422 ⟨1422861, by decide⟩ ⟨11, 2, 0, 1422861, 105422, 1081, 262144⟩
    (by decide) selected_cut_50039

theorem selected_cut_50040 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 105423) = some ⟨11, 1, 0, 977886, 105423, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105423_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105423 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 105423 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 105423, 1, 262144⟩
    (by decide) selected_cut_50040

theorem unmarked_context_10_26355_1422862 : frontier 11 ⟨1422862, by decide⟩
    (prefixCache 10 26355) (prefixPartial 10 26355) = false := by
  decide +kernel

theorem node_context_10_26355_1422862 : EJMOriginalGlobalDAGData.nodes 11 ⟨1422862, by decide⟩ =
    .split (coordinate 10) (![⟨1422699, by decide⟩,⟨1422791, by decide⟩,⟨1422861, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26355_1422862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26355 ⟨1422862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26355
    ⟨1422862, by decide⟩ (by decide) (![⟨1422699, by decide⟩,⟨1422791, by decide⟩,⟨1422861, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_26355_1422862 node_context_10_26355_1422862
  intro a
  fin_cases a
  · exact context_11_105420_1422699
  · exact context_11_105421_1422791
  · exact context_11_105422_1422861
  · exact context_11_105423_977886

theorem unmarked_context_9_6588_1422863 : frontier 12 ⟨1422863, by decide⟩
    (prefixCache 9 6588) (prefixPartial 9 6588) = false := by
  decide +kernel

theorem node_context_9_6588_1422863 : EJMOriginalGlobalDAGData.nodes 12 ⟨1422863, by decide⟩ =
    .split (coordinate 9) (![⟨1421292, by decide⟩,⟨1421923, by decide⟩,⟨1422524, by decide⟩,⟨1422862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6588_1422863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6588 ⟨1422863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6588
    ⟨1422863, by decide⟩ (by decide) (![⟨1421292, by decide⟩,⟨1421923, by decide⟩,⟨1422524, by decide⟩,⟨1422862, by decide⟩]) unmarked_context_9_6588_1422863 node_context_9_6588_1422863
  intro a
  fin_cases a
  · exact context_10_26352_1421292
  · exact context_10_26353_1421923
  · exact context_10_26354_1422524
  · exact context_10_26355_1422862

theorem selected_cut_50041 : selected 10 ⟨1422947, by decide⟩
    (prefixPartial 11 105424) = some ⟨11, 2, 0, 1422947, 105424, 1213, 262144⟩ := by
  decide +kernel

theorem context_11_105424_1422947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105424 ⟨1422947, by decide⟩ :=
  accepted_of_selected 11 105424 ⟨1422947, by decide⟩ ⟨11, 2, 0, 1422947, 105424, 1213, 262144⟩
    (by decide) selected_cut_50041

theorem selected_cut_50042 : selected 10 ⟨1423114, by decide⟩
    (prefixPartial 11 105425) = some ⟨11, 2, 0, 1423114, 105425, 3061, 262144⟩ := by
  decide +kernel

theorem context_11_105425_1423114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105425 ⟨1423114, by decide⟩ :=
  accepted_of_selected 11 105425 ⟨1423114, by decide⟩ ⟨11, 2, 0, 1423114, 105425, 3061, 262144⟩
    (by decide) selected_cut_50042

theorem selected_cut_50043 : selected 10 ⟨1377801, by decide⟩
    (prefixPartial 11 105426) = some ⟨11, 1, 0, 1377801, 105426, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105426_1377801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105426 ⟨1377801, by decide⟩ :=
  accepted_of_selected 11 105426 ⟨1377801, by decide⟩ ⟨11, 1, 0, 1377801, 105426, 1, 262144⟩
    (by decide) selected_cut_50043

theorem selected_cut_50044 : selected 10 ⟨1423203, by decide⟩
    (prefixPartial 11 105427) = some ⟨11, 2, 0, 1423203, 105427, 1549, 262144⟩ := by
  decide +kernel

theorem context_11_105427_1423203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105427 ⟨1423203, by decide⟩ :=
  accepted_of_selected 11 105427 ⟨1423203, by decide⟩ ⟨11, 2, 0, 1423203, 105427, 1549, 262144⟩
    (by decide) selected_cut_50044

theorem unmarked_context_10_26356_1423204 : frontier 11 ⟨1423204, by decide⟩
    (prefixCache 10 26356) (prefixPartial 10 26356) = false := by
  decide +kernel

theorem node_context_10_26356_1423204 : EJMOriginalGlobalDAGData.nodes 11 ⟨1423204, by decide⟩ =
    .split (coordinate 10) (![⟨1422947, by decide⟩,⟨1423114, by decide⟩,⟨1377801, by decide⟩,⟨1423203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26356_1423204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26356 ⟨1423204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26356
    ⟨1423204, by decide⟩ (by decide) (![⟨1422947, by decide⟩,⟨1423114, by decide⟩,⟨1377801, by decide⟩,⟨1423203, by decide⟩]) unmarked_context_10_26356_1423204 node_context_10_26356_1423204
  intro a
  fin_cases a
  · exact context_11_105424_1422947
  · exact context_11_105425_1423114
  · exact context_11_105426_1377801
  · exact context_11_105427_1423203

theorem selected_cut_50045 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26357) = some ⟨10, 1, 0, 893098, 26357, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26357_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26357 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26357 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26357, 1, 1048576⟩
    (by decide) selected_cut_50045

theorem selected_cut_50046 : selected 10 ⟨1423323, by decide⟩
    (prefixPartial 11 105432) = some ⟨11, 2, 0, 1423323, 105432, 2845, 262144⟩ := by
  decide +kernel

theorem context_11_105432_1423323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105432 ⟨1423323, by decide⟩ :=
  accepted_of_selected 11 105432 ⟨1423323, by decide⟩ ⟨11, 2, 0, 1423323, 105432, 2845, 262144⟩
    (by decide) selected_cut_50046

theorem selected_cut_50047 : selected 10 ⟨1423398, by decide⟩
    (prefixPartial 11 105433) = some ⟨11, 2, 0, 1423398, 105433, 1909, 262144⟩ := by
  decide +kernel

theorem context_11_105433_1423398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105433 ⟨1423398, by decide⟩ :=
  accepted_of_selected 11 105433 ⟨1423398, by decide⟩ ⟨11, 2, 0, 1423398, 105433, 1909, 262144⟩
    (by decide) selected_cut_50047

theorem selected_cut_50048 : selected 10 ⟨1377801, by decide⟩
    (prefixPartial 11 105434) = some ⟨11, 1, 0, 1377801, 105434, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105434_1377801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105434 ⟨1377801, by decide⟩ :=
  accepted_of_selected 11 105434 ⟨1377801, by decide⟩ ⟨11, 1, 0, 1377801, 105434, 1, 262144⟩
    (by decide) selected_cut_50048

theorem selected_cut_50049 : selected 10 ⟨1423424, by decide⟩
    (prefixPartial 11 105435) = some ⟨11, 2, 0, 1423424, 105435, 405, 262144⟩ := by
  decide +kernel

theorem context_11_105435_1423424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105435 ⟨1423424, by decide⟩ :=
  accepted_of_selected 11 105435 ⟨1423424, by decide⟩ ⟨11, 2, 0, 1423424, 105435, 405, 262144⟩
    (by decide) selected_cut_50049

theorem unmarked_context_10_26358_1423425 : frontier 11 ⟨1423425, by decide⟩
    (prefixCache 10 26358) (prefixPartial 10 26358) = false := by
  decide +kernel

theorem node_context_10_26358_1423425 : EJMOriginalGlobalDAGData.nodes 11 ⟨1423425, by decide⟩ =
    .split (coordinate 10) (![⟨1423323, by decide⟩,⟨1423398, by decide⟩,⟨1377801, by decide⟩,⟨1423424, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26358_1423425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26358 ⟨1423425, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26358
    ⟨1423425, by decide⟩ (by decide) (![⟨1423323, by decide⟩,⟨1423398, by decide⟩,⟨1377801, by decide⟩,⟨1423424, by decide⟩]) unmarked_context_10_26358_1423425 node_context_10_26358_1423425
  intro a
  fin_cases a
  · exact context_11_105432_1423323
  · exact context_11_105433_1423398
  · exact context_11_105434_1377801
  · exact context_11_105435_1423424

theorem selected_cut_50050 : selected 11 ⟨1423535, by decide⟩
    (prefixPartial 10 26359) = some ⟨10, 2, 0, 1423535, 26359, 2565, 1048576⟩ := by
  decide +kernel

theorem context_10_26359_1423535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26359 ⟨1423535, by decide⟩ :=
  accepted_of_selected 10 26359 ⟨1423535, by decide⟩ ⟨10, 2, 0, 1423535, 26359, 2565, 1048576⟩
    (by decide) selected_cut_50050

theorem unmarked_context_9_6589_1423536 : frontier 12 ⟨1423536, by decide⟩
    (prefixCache 9 6589) (prefixPartial 9 6589) = false := by
  decide +kernel

theorem node_context_9_6589_1423536 : EJMOriginalGlobalDAGData.nodes 12 ⟨1423536, by decide⟩ =
    .split (coordinate 9) (![⟨1423204, by decide⟩,⟨893098, by decide⟩,⟨1423425, by decide⟩,⟨1423535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6589_1423536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6589 ⟨1423536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6589
    ⟨1423536, by decide⟩ (by decide) (![⟨1423204, by decide⟩,⟨893098, by decide⟩,⟨1423425, by decide⟩,⟨1423535, by decide⟩]) unmarked_context_9_6589_1423536 node_context_9_6589_1423536
  intro a
  fin_cases a
  · exact context_10_26356_1423204
  · exact context_10_26357_893098
  · exact context_10_26358_1423425
  · exact context_10_26359_1423535

theorem selected_cut_50051 : selected 12 ⟨1423748, by decide⟩
    (prefixPartial 9 6590) = some ⟨9, 2, 0, 1423748, 6590, 2637, 4194304⟩ := by
  decide +kernel

theorem context_9_6590_1423748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6590 ⟨1423748, by decide⟩ :=
  accepted_of_selected 9 6590 ⟨1423748, by decide⟩ ⟨9, 2, 0, 1423748, 6590, 2637, 4194304⟩
    (by decide) selected_cut_50051

theorem selected_cut_50052 : selected 12 ⟨1423766, by decide⟩
    (prefixPartial 9 6591) = some ⟨9, 2, 0, 1423766, 6591, 145, 4194304⟩ := by
  decide +kernel

theorem context_9_6591_1423766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6591 ⟨1423766, by decide⟩ :=
  accepted_of_selected 9 6591 ⟨1423766, by decide⟩ ⟨9, 2, 0, 1423766, 6591, 145, 4194304⟩
    (by decide) selected_cut_50052

theorem unmarked_context_8_1647_1423767 : frontier 13 ⟨1423767, by decide⟩
    (prefixCache 8 1647) (prefixPartial 8 1647) = false := by
  decide +kernel

theorem node_context_8_1647_1423767 : EJMOriginalGlobalDAGData.nodes 13 ⟨1423767, by decide⟩ =
    .split (coordinate 8) (![⟨1422863, by decide⟩,⟨1423536, by decide⟩,⟨1423748, by decide⟩,⟨1423766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1647_1423767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1647 ⟨1423767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1647
    ⟨1423767, by decide⟩ (by decide) (![⟨1422863, by decide⟩,⟨1423536, by decide⟩,⟨1423748, by decide⟩,⟨1423766, by decide⟩]) unmarked_context_8_1647_1423767 node_context_8_1647_1423767
  intro a
  fin_cases a
  · exact context_9_6588_1422863
  · exact context_9_6589_1423536
  · exact context_9_6590_1423748
  · exact context_9_6591_1423766

theorem unmarked_context_7_411_1423768 : frontier 14 ⟨1423768, by decide⟩
    (prefixCache 7 411) (prefixPartial 7 411) = false := by
  decide +kernel

theorem node_context_7_411_1423768 : EJMOriginalGlobalDAGData.nodes 14 ⟨1423768, by decide⟩ =
    .split (coordinate 7) (![⟨1364555, by decide⟩,⟨1421000, by decide⟩,⟨1366235, by decide⟩,⟨1423767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_411_1423768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 411 ⟨1423768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 411
    ⟨1423768, by decide⟩ (by decide) (![⟨1364555, by decide⟩,⟨1421000, by decide⟩,⟨1366235, by decide⟩,⟨1423767, by decide⟩]) unmarked_context_7_411_1423768 node_context_7_411_1423768
  intro a
  fin_cases a
  · exact context_8_1644_1364555
  · exact context_8_1645_1421000
  · exact context_8_1646_1366235
  · exact context_8_1647_1423767

theorem unmarked_context_6_102_1423769 : frontier 15 ⟨1423769, by decide⟩
    (prefixCache 6 102) (prefixPartial 6 102) = false := by
  decide +kernel

theorem node_context_6_102_1423769 : EJMOriginalGlobalDAGData.nodes 15 ⟨1423769, by decide⟩ =
    .split (coordinate 6) (![⟨116316, by decide⟩,⟨1418680, by decide⟩,⟨1418683, by decide⟩,⟨1423768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_102_1423769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 102 ⟨1423769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 102
    ⟨1423769, by decide⟩ (by decide) (![⟨116316, by decide⟩,⟨1418680, by decide⟩,⟨1418683, by decide⟩,⟨1423768, by decide⟩]) unmarked_context_6_102_1423769 node_context_6_102_1423769
  intro a
  fin_cases a
  · exact context_7_408_116316
  · exact context_7_409_1418680
  · exact context_7_410_1418683
  · exact context_7_411_1423768

theorem selected_cut_50053 : selected 14 ⟨1423770, by decide⟩
    (prefixPartial 7 412) = some ⟨7, 1, 0, 1423770, 412, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_412_1423770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 412 ⟨1423770, by decide⟩ :=
  accepted_of_selected 7 412 ⟨1423770, by decide⟩ ⟨7, 1, 0, 1423770, 412, 1, 67108864⟩
    (by decide) selected_cut_50053

theorem selected_cut_50054 : selected 11 ⟨1423976, by decide⟩
    (prefixPartial 10 26432) = some ⟨10, 2, 0, 1423976, 26432, 3245, 1048576⟩ := by
  decide +kernel

theorem context_10_26432_1423976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26432 ⟨1423976, by decide⟩ :=
  accepted_of_selected 10 26432 ⟨1423976, by decide⟩ ⟨10, 2, 0, 1423976, 26432, 3245, 1048576⟩
    (by decide) selected_cut_50054

theorem selected_cut_50055 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 422928) = some ⟨12, 1, 0, 1415033, 422928, 1, 65536⟩ := by
  decide +kernel

theorem context_12_422928_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422928 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 422928 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 422928, 1, 65536⟩
    (by decide) selected_cut_50055

theorem selected_cut_50056 : selected 9 ⟨1424031, by decide⟩
    (prefixPartial 12 422929) = some ⟨12, 2, 0, 1424031, 422929, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_422929_1424031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422929 ⟨1424031, by decide⟩ :=
  accepted_of_selected 12 422929 ⟨1424031, by decide⟩ ⟨12, 2, 0, 1424031, 422929, 1697, 65536⟩
    (by decide) selected_cut_50056

theorem selected_cut_50057 : selected 9 ⟨1424096, by decide⟩
    (prefixPartial 12 422930) = some ⟨12, 2, 0, 1424096, 422930, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_422930_1424096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422930 ⟨1424096, by decide⟩ :=
  accepted_of_selected 12 422930 ⟨1424096, by decide⟩ ⟨12, 2, 0, 1424096, 422930, 2285, 65536⟩
    (by decide) selected_cut_50057

theorem selected_cut_50058 : selected 9 ⟨1424151, by decide⟩
    (prefixPartial 12 422931) = some ⟨12, 2, 0, 1424151, 422931, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_422931_1424151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422931 ⟨1424151, by decide⟩ :=
  accepted_of_selected 12 422931 ⟨1424151, by decide⟩ ⟨12, 2, 0, 1424151, 422931, 1993, 65536⟩
    (by decide) selected_cut_50058

theorem unmarked_context_11_105732_1424152 : frontier 10 ⟨1424152, by decide⟩
    (prefixCache 11 105732) (prefixPartial 11 105732) = false := by
  decide +kernel

theorem node_context_11_105732_1424152 : EJMOriginalGlobalDAGData.nodes 10 ⟨1424152, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1424031, by decide⟩,⟨1424096, by decide⟩,⟨1424151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105732_1424152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105732 ⟨1424152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105732
    ⟨1424152, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1424031, by decide⟩,⟨1424096, by decide⟩,⟨1424151, by decide⟩]) unmarked_context_11_105732_1424152 node_context_11_105732_1424152
  intro a
  fin_cases a
  · exact context_12_422928_1415033
  · exact context_12_422929_1424031
  · exact context_12_422930_1424096
  · exact context_12_422931_1424151

theorem selected_cut_50059 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 105733) = some ⟨11, 1, 0, 892405, 105733, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105733_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105733 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 105733 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 105733, 1, 262144⟩
    (by decide) selected_cut_50059

theorem selected_cut_50060 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 422936) = some ⟨12, 1, 0, 1415033, 422936, 1, 65536⟩ := by
  decide +kernel

theorem context_12_422936_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422936 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 422936 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 422936, 1, 65536⟩
    (by decide) selected_cut_50060

theorem selected_cut_50061 : selected 9 ⟨1424198, by decide⟩
    (prefixPartial 12 422937) = some ⟨12, 2, 0, 1424198, 422937, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_422937_1424198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422937 ⟨1424198, by decide⟩ :=
  accepted_of_selected 12 422937 ⟨1424198, by decide⟩ ⟨12, 2, 0, 1424198, 422937, 1821, 65536⟩
    (by decide) selected_cut_50061

theorem selected_cut_50062 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 422938) = some ⟨12, 1, 0, 448662, 422938, 1, 65536⟩ := by
  decide +kernel

theorem context_12_422938_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422938 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 422938 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 422938, 1, 65536⟩
    (by decide) selected_cut_50062

theorem selected_cut_50063 : selected 9 ⟨1424265, by decide⟩
    (prefixPartial 12 422939) = some ⟨12, 2, 0, 1424265, 422939, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_422939_1424265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422939 ⟨1424265, by decide⟩ :=
  accepted_of_selected 12 422939 ⟨1424265, by decide⟩ ⟨12, 2, 0, 1424265, 422939, 2389, 65536⟩
    (by decide) selected_cut_50063

theorem unmarked_context_11_105734_1424266 : frontier 10 ⟨1424266, by decide⟩
    (prefixCache 11 105734) (prefixPartial 11 105734) = false := by
  decide +kernel

theorem node_context_11_105734_1424266 : EJMOriginalGlobalDAGData.nodes 10 ⟨1424266, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1424198, by decide⟩,⟨448662, by decide⟩,⟨1424265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105734_1424266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105734 ⟨1424266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105734
    ⟨1424266, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1424198, by decide⟩,⟨448662, by decide⟩,⟨1424265, by decide⟩]) unmarked_context_11_105734_1424266 node_context_11_105734_1424266
  intro a
  fin_cases a
  · exact context_12_422936_1415033
  · exact context_12_422937_1424198
  · exact context_12_422938_448662
  · exact context_12_422939_1424265

theorem selected_cut_50064 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 422940) = some ⟨12, 1, 0, 1415033, 422940, 1, 65536⟩ := by
  decide +kernel

theorem context_12_422940_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422940 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 422940 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 422940, 1, 65536⟩
    (by decide) selected_cut_50064

theorem selected_cut_50065 : selected 9 ⟨1424309, by decide⟩
    (prefixPartial 12 422941) = some ⟨12, 2, 0, 1424309, 422941, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_422941_1424309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422941 ⟨1424309, by decide⟩ :=
  accepted_of_selected 12 422941 ⟨1424309, by decide⟩ ⟨12, 2, 0, 1424309, 422941, 1769, 65536⟩
    (by decide) selected_cut_50065

theorem selected_cut_50066 : selected 9 ⟨1424379, by decide⟩
    (prefixPartial 12 422942) = some ⟨12, 2, 0, 1424379, 422942, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_422942_1424379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422942 ⟨1424379, by decide⟩ :=
  accepted_of_selected 12 422942 ⟨1424379, by decide⟩ ⟨12, 2, 0, 1424379, 422942, 2525, 65536⟩
    (by decide) selected_cut_50066

theorem selected_cut_50067 : selected 9 ⟨517541, by decide⟩
    (prefixPartial 12 422943) = some ⟨12, 1, 0, 517541, 422943, 1, 65536⟩ := by
  decide +kernel

theorem context_12_422943_517541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422943 ⟨517541, by decide⟩ :=
  accepted_of_selected 12 422943 ⟨517541, by decide⟩ ⟨12, 1, 0, 517541, 422943, 1, 65536⟩
    (by decide) selected_cut_50067

theorem unmarked_context_11_105735_1424380 : frontier 10 ⟨1424380, by decide⟩
    (prefixCache 11 105735) (prefixPartial 11 105735) = false := by
  decide +kernel

theorem node_context_11_105735_1424380 : EJMOriginalGlobalDAGData.nodes 10 ⟨1424380, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1424309, by decide⟩,⟨1424379, by decide⟩,⟨517541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105735_1424380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105735 ⟨1424380, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105735
    ⟨1424380, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1424309, by decide⟩,⟨1424379, by decide⟩,⟨517541, by decide⟩]) unmarked_context_11_105735_1424380 node_context_11_105735_1424380
  intro a
  fin_cases a
  · exact context_12_422940_1415033
  · exact context_12_422941_1424309
  · exact context_12_422942_1424379
  · exact context_12_422943_517541

theorem unmarked_context_10_26433_1424381 : frontier 11 ⟨1424381, by decide⟩
    (prefixCache 10 26433) (prefixPartial 10 26433) = false := by
  decide +kernel

theorem node_context_10_26433_1424381 : EJMOriginalGlobalDAGData.nodes 11 ⟨1424381, by decide⟩ =
    .split (coordinate 10) (![⟨1424152, by decide⟩,⟨892405, by decide⟩,⟨1424266, by decide⟩,⟨1424380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26433_1424381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26433 ⟨1424381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26433
    ⟨1424381, by decide⟩ (by decide) (![⟨1424152, by decide⟩,⟨892405, by decide⟩,⟨1424266, by decide⟩,⟨1424380, by decide⟩]) unmarked_context_10_26433_1424381 node_context_10_26433_1424381
  intro a
  fin_cases a
  · exact context_11_105732_1424152
  · exact context_11_105733_892405
  · exact context_11_105734_1424266
  · exact context_11_105735_1424380

theorem selected_cut_50068 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 422944) = some ⟨12, 1, 0, 435160, 422944, 1, 65536⟩ := by
  decide +kernel

theorem context_12_422944_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422944 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 422944 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 422944, 1, 65536⟩
    (by decide) selected_cut_50068

theorem selected_cut_50069 : selected 9 ⟨1424445, by decide⟩
    (prefixPartial 12 422945) = some ⟨12, 2, 0, 1424445, 422945, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_422945_1424445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422945 ⟨1424445, by decide⟩ :=
  accepted_of_selected 12 422945 ⟨1424445, by decide⟩ ⟨12, 2, 0, 1424445, 422945, 1913, 65536⟩
    (by decide) selected_cut_50069

theorem selected_cut_50070 : selected 9 ⟨1424509, by decide⟩
    (prefixPartial 12 422946) = some ⟨12, 2, 0, 1424509, 422946, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_422946_1424509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422946 ⟨1424509, by decide⟩ :=
  accepted_of_selected 12 422946 ⟨1424509, by decide⟩ ⟨12, 2, 0, 1424509, 422946, 2521, 65536⟩
    (by decide) selected_cut_50070

theorem selected_cut_50071 : selected 9 ⟨1424579, by decide⟩
    (prefixPartial 12 422947) = some ⟨12, 2, 0, 1424579, 422947, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_422947_1424579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422947 ⟨1424579, by decide⟩ :=
  accepted_of_selected 12 422947 ⟨1424579, by decide⟩ ⟨12, 2, 0, 1424579, 422947, 1973, 65536⟩
    (by decide) selected_cut_50071

theorem unmarked_context_11_105736_1424580 : frontier 10 ⟨1424580, by decide⟩
    (prefixCache 11 105736) (prefixPartial 11 105736) = false := by
  decide +kernel

theorem node_context_11_105736_1424580 : EJMOriginalGlobalDAGData.nodes 10 ⟨1424580, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1424445, by decide⟩,⟨1424509, by decide⟩,⟨1424579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105736_1424580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105736 ⟨1424580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105736
    ⟨1424580, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1424445, by decide⟩,⟨1424509, by decide⟩,⟨1424579, by decide⟩]) unmarked_context_11_105736_1424580 node_context_11_105736_1424580
  intro a
  fin_cases a
  · exact context_12_422944_435160
  · exact context_12_422945_1424445
  · exact context_12_422946_1424509
  · exact context_12_422947_1424579

theorem selected_cut_50072 : selected 10 ⟨1424669, by decide⟩
    (prefixPartial 11 105737) = some ⟨11, 2, 0, 1424669, 105737, 3545, 262144⟩ := by
  decide +kernel

theorem context_11_105737_1424669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105737 ⟨1424669, by decide⟩ :=
  accepted_of_selected 11 105737 ⟨1424669, by decide⟩ ⟨11, 2, 0, 1424669, 105737, 3545, 262144⟩
    (by decide) selected_cut_50072

theorem selected_cut_50073 : selected 10 ⟨1424723, by decide⟩
    (prefixPartial 11 105738) = some ⟨11, 2, 0, 1424723, 105738, 1933, 262144⟩ := by
  decide +kernel

theorem context_11_105738_1424723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105738 ⟨1424723, by decide⟩ :=
  accepted_of_selected 11 105738 ⟨1424723, by decide⟩ ⟨11, 2, 0, 1424723, 105738, 1933, 262144⟩
    (by decide) selected_cut_50073

theorem selected_cut_50074 : selected 10 ⟨1424832, by decide⟩
    (prefixPartial 11 105739) = some ⟨11, 2, 0, 1424832, 105739, 3961, 262144⟩ := by
  decide +kernel

theorem context_11_105739_1424832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105739 ⟨1424832, by decide⟩ :=
  accepted_of_selected 11 105739 ⟨1424832, by decide⟩ ⟨11, 2, 0, 1424832, 105739, 3961, 262144⟩
    (by decide) selected_cut_50074

theorem unmarked_context_10_26434_1424833 : frontier 11 ⟨1424833, by decide⟩
    (prefixCache 10 26434) (prefixPartial 10 26434) = false := by
  decide +kernel

theorem node_context_10_26434_1424833 : EJMOriginalGlobalDAGData.nodes 11 ⟨1424833, by decide⟩ =
    .split (coordinate 10) (![⟨1424580, by decide⟩,⟨1424669, by decide⟩,⟨1424723, by decide⟩,⟨1424832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26434_1424833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26434 ⟨1424833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26434
    ⟨1424833, by decide⟩ (by decide) (![⟨1424580, by decide⟩,⟨1424669, by decide⟩,⟨1424723, by decide⟩,⟨1424832, by decide⟩]) unmarked_context_10_26434_1424833 node_context_10_26434_1424833
  intro a
  fin_cases a
  · exact context_11_105736_1424580
  · exact context_11_105737_1424669
  · exact context_11_105738_1424723
  · exact context_11_105739_1424832

theorem selected_cut_50075 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 422960) = some ⟨12, 1, 0, 1416143, 422960, 1, 65536⟩ := by
  decide +kernel

theorem context_12_422960_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422960 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 422960 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 422960, 1, 65536⟩
    (by decide) selected_cut_50075

theorem selected_cut_50076 : selected 9 ⟨1424899, by decide⟩
    (prefixPartial 12 422961) = some ⟨12, 2, 0, 1424899, 422961, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_422961_1424899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422961 ⟨1424899, by decide⟩ :=
  accepted_of_selected 12 422961 ⟨1424899, by decide⟩ ⟨12, 2, 0, 1424899, 422961, 1437, 65536⟩
    (by decide) selected_cut_50076

theorem selected_cut_50077 : selected 9 ⟨1424976, by decide⟩
    (prefixPartial 12 422962) = some ⟨12, 2, 0, 1424976, 422962, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_422962_1424976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422962 ⟨1424976, by decide⟩ :=
  accepted_of_selected 12 422962 ⟨1424976, by decide⟩ ⟨12, 2, 0, 1424976, 422962, 1753, 65536⟩
    (by decide) selected_cut_50077

theorem selected_cut_50078 : selected 9 ⟨1425030, by decide⟩
    (prefixPartial 12 422963) = some ⟨12, 2, 0, 1425030, 422963, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_422963_1425030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 422963 ⟨1425030, by decide⟩ :=
  accepted_of_selected 12 422963 ⟨1425030, by decide⟩ ⟨12, 2, 0, 1425030, 422963, 1489, 65536⟩
    (by decide) selected_cut_50078

theorem unmarked_context_11_105740_1425031 : frontier 10 ⟨1425031, by decide⟩
    (prefixCache 11 105740) (prefixPartial 11 105740) = false := by
  decide +kernel

theorem node_context_11_105740_1425031 : EJMOriginalGlobalDAGData.nodes 10 ⟨1425031, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1424899, by decide⟩,⟨1424976, by decide⟩,⟨1425030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105740_1425031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105740 ⟨1425031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105740
    ⟨1425031, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1424899, by decide⟩,⟨1424976, by decide⟩,⟨1425030, by decide⟩]) unmarked_context_11_105740_1425031 node_context_11_105740_1425031
  intro a
  fin_cases a
  · exact context_12_422960_1416143
  · exact context_12_422961_1424899
  · exact context_12_422962_1424976
  · exact context_12_422963_1425030

theorem selected_cut_50079 : selected 10 ⟨1425127, by decide⟩
    (prefixPartial 11 105741) = some ⟨11, 2, 0, 1425127, 105741, 2617, 262144⟩ := by
  decide +kernel

theorem context_11_105741_1425127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105741 ⟨1425127, by decide⟩ :=
  accepted_of_selected 11 105741 ⟨1425127, by decide⟩ ⟨11, 2, 0, 1425127, 105741, 2617, 262144⟩
    (by decide) selected_cut_50079

theorem selected_cut_50080 : selected 10 ⟨1425205, by decide⟩
    (prefixPartial 11 105742) = some ⟨11, 2, 0, 1425205, 105742, 2605, 262144⟩ := by
  decide +kernel

theorem context_11_105742_1425205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105742 ⟨1425205, by decide⟩ :=
  accepted_of_selected 11 105742 ⟨1425205, by decide⟩ ⟨11, 2, 0, 1425205, 105742, 2605, 262144⟩
    (by decide) selected_cut_50080

theorem selected_cut_50081 : selected 10 ⟨1425247, by decide⟩
    (prefixPartial 11 105743) = some ⟨11, 2, 0, 1425247, 105743, 1401, 262144⟩ := by
  decide +kernel

theorem context_11_105743_1425247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105743 ⟨1425247, by decide⟩ :=
  accepted_of_selected 11 105743 ⟨1425247, by decide⟩ ⟨11, 2, 0, 1425247, 105743, 1401, 262144⟩
    (by decide) selected_cut_50081

theorem unmarked_context_10_26435_1425248 : frontier 11 ⟨1425248, by decide⟩
    (prefixCache 10 26435) (prefixPartial 10 26435) = false := by
  decide +kernel

theorem node_context_10_26435_1425248 : EJMOriginalGlobalDAGData.nodes 11 ⟨1425248, by decide⟩ =
    .split (coordinate 10) (![⟨1425031, by decide⟩,⟨1425127, by decide⟩,⟨1425205, by decide⟩,⟨1425247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26435_1425248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26435 ⟨1425248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26435
    ⟨1425248, by decide⟩ (by decide) (![⟨1425031, by decide⟩,⟨1425127, by decide⟩,⟨1425205, by decide⟩,⟨1425247, by decide⟩]) unmarked_context_10_26435_1425248 node_context_10_26435_1425248
  intro a
  fin_cases a
  · exact context_11_105740_1425031
  · exact context_11_105741_1425127
  · exact context_11_105742_1425205
  · exact context_11_105743_1425247

theorem unmarked_context_9_6608_1425249 : frontier 12 ⟨1425249, by decide⟩
    (prefixCache 9 6608) (prefixPartial 9 6608) = false := by
  decide +kernel

theorem node_context_9_6608_1425249 : EJMOriginalGlobalDAGData.nodes 12 ⟨1425249, by decide⟩ =
    .split (coordinate 9) (![⟨1423976, by decide⟩,⟨1424381, by decide⟩,⟨1424833, by decide⟩,⟨1425248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6608_1425249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6608 ⟨1425249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6608
    ⟨1425249, by decide⟩ (by decide) (![⟨1423976, by decide⟩,⟨1424381, by decide⟩,⟨1424833, by decide⟩,⟨1425248, by decide⟩]) unmarked_context_9_6608_1425249 node_context_9_6608_1425249
  intro a
  fin_cases a
  · exact context_10_26432_1423976
  · exact context_10_26433_1424381
  · exact context_10_26434_1424833
  · exact context_10_26435_1425248

theorem selected_cut_50082 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 26436) = some ⟨10, 1, 0, 793297, 26436, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26436_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26436 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 26436 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 26436, 1, 1048576⟩
    (by decide) selected_cut_50082

theorem selected_cut_50083 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 26437) = some ⟨10, 1, 0, 893098, 26437, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_26437_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26437 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 26437 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 26437, 1, 1048576⟩
    (by decide) selected_cut_50083

theorem selected_cut_50084 : selected 10 ⟨1425335, by decide⟩
    (prefixPartial 11 105752) = some ⟨11, 2, 0, 1425335, 105752, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_105752_1425335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105752 ⟨1425335, by decide⟩ :=
  accepted_of_selected 11 105752 ⟨1425335, by decide⟩ ⟨11, 2, 0, 1425335, 105752, 2057, 262144⟩
    (by decide) selected_cut_50084

theorem selected_cut_50085 : selected 10 ⟨1425415, by decide⟩
    (prefixPartial 11 105753) = some ⟨11, 2, 0, 1425415, 105753, 2337, 262144⟩ := by
  decide +kernel

theorem context_11_105753_1425415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105753 ⟨1425415, by decide⟩ :=
  accepted_of_selected 11 105753 ⟨1425415, by decide⟩ ⟨11, 2, 0, 1425415, 105753, 2337, 262144⟩
    (by decide) selected_cut_50085

theorem selected_cut_50086 : selected 10 ⟨1369759, by decide⟩
    (prefixPartial 11 105754) = some ⟨11, 1, 0, 1369759, 105754, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105754_1369759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105754 ⟨1369759, by decide⟩ :=
  accepted_of_selected 11 105754 ⟨1369759, by decide⟩ ⟨11, 1, 0, 1369759, 105754, 1, 262144⟩
    (by decide) selected_cut_50086

theorem selected_cut_50087 : selected 10 ⟨1425493, by decide⟩
    (prefixPartial 11 105755) = some ⟨11, 2, 0, 1425493, 105755, 2401, 262144⟩ := by
  decide +kernel

theorem context_11_105755_1425493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105755 ⟨1425493, by decide⟩ :=
  accepted_of_selected 11 105755 ⟨1425493, by decide⟩ ⟨11, 2, 0, 1425493, 105755, 2401, 262144⟩
    (by decide) selected_cut_50087

theorem unmarked_context_10_26438_1425494 : frontier 11 ⟨1425494, by decide⟩
    (prefixCache 10 26438) (prefixPartial 10 26438) = false := by
  decide +kernel

theorem node_context_10_26438_1425494 : EJMOriginalGlobalDAGData.nodes 11 ⟨1425494, by decide⟩ =
    .split (coordinate 10) (![⟨1425335, by decide⟩,⟨1425415, by decide⟩,⟨1369759, by decide⟩,⟨1425493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26438_1425494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26438 ⟨1425494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26438
    ⟨1425494, by decide⟩ (by decide) (![⟨1425335, by decide⟩,⟨1425415, by decide⟩,⟨1369759, by decide⟩,⟨1425493, by decide⟩]) unmarked_context_10_26438_1425494 node_context_10_26438_1425494
  intro a
  fin_cases a
  · exact context_11_105752_1425335
  · exact context_11_105753_1425415
  · exact context_11_105754_1369759
  · exact context_11_105755_1425493

theorem selected_cut_50088 : selected 11 ⟨1425635, by decide⟩
    (prefixPartial 10 26439) = some ⟨10, 2, 0, 1425635, 26439, 3949, 1048576⟩ := by
  decide +kernel

theorem context_10_26439_1425635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26439 ⟨1425635, by decide⟩ :=
  accepted_of_selected 10 26439 ⟨1425635, by decide⟩ ⟨10, 2, 0, 1425635, 26439, 3949, 1048576⟩
    (by decide) selected_cut_50088

theorem unmarked_context_9_6609_1425636 : frontier 12 ⟨1425636, by decide⟩
    (prefixCache 9 6609) (prefixPartial 9 6609) = false := by
  decide +kernel

theorem node_context_9_6609_1425636 : EJMOriginalGlobalDAGData.nodes 12 ⟨1425636, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1425494, by decide⟩,⟨1425635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6609_1425636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6609 ⟨1425636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6609
    ⟨1425636, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1425494, by decide⟩,⟨1425635, by decide⟩]) unmarked_context_9_6609_1425636 node_context_9_6609_1425636
  intro a
  fin_cases a
  · exact context_10_26436_793297
  · exact context_10_26437_893098
  · exact context_10_26438_1425494
  · exact context_10_26439_1425635

theorem selected_cut_50089 : selected 12 ⟨1425730, by decide⟩
    (prefixPartial 9 6610) = some ⟨9, 2, 0, 1425730, 6610, 1673, 4194304⟩ := by
  decide +kernel

theorem context_9_6610_1425730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6610 ⟨1425730, by decide⟩ :=
  accepted_of_selected 9 6610 ⟨1425730, by decide⟩ ⟨9, 2, 0, 1425730, 6610, 1673, 4194304⟩
    (by decide) selected_cut_50089

theorem selected_cut_50090 : selected 12 ⟨1425763, by decide⟩
    (prefixPartial 9 6611) = some ⟨9, 2, 0, 1425763, 6611, 409, 4194304⟩ := by
  decide +kernel

theorem context_9_6611_1425763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6611 ⟨1425763, by decide⟩ :=
  accepted_of_selected 9 6611 ⟨1425763, by decide⟩ ⟨9, 2, 0, 1425763, 6611, 409, 4194304⟩
    (by decide) selected_cut_50090

theorem unmarked_context_8_1652_1425764 : frontier 13 ⟨1425764, by decide⟩
    (prefixCache 8 1652) (prefixPartial 8 1652) = false := by
  decide +kernel

theorem node_context_8_1652_1425764 : EJMOriginalGlobalDAGData.nodes 13 ⟨1425764, by decide⟩ =
    .split (coordinate 8) (![⟨1425249, by decide⟩,⟨1425636, by decide⟩,⟨1425730, by decide⟩,⟨1425763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1652_1425764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1652 ⟨1425764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1652
    ⟨1425764, by decide⟩ (by decide) (![⟨1425249, by decide⟩,⟨1425636, by decide⟩,⟨1425730, by decide⟩,⟨1425763, by decide⟩]) unmarked_context_8_1652_1425764 node_context_8_1652_1425764
  intro a
  fin_cases a
  · exact context_9_6608_1425249
  · exact context_9_6609_1425636
  · exact context_9_6610_1425730
  · exact context_9_6611_1425763

theorem selected_cut_50091 : selected 11 ⟨1425895, by decide⟩
    (prefixPartial 10 26448) = some ⟨10, 2, 0, 1425895, 26448, 2825, 1048576⟩ := by
  decide +kernel

theorem context_10_26448_1425895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26448 ⟨1425895, by decide⟩ :=
  accepted_of_selected 10 26448 ⟨1425895, by decide⟩ ⟨10, 2, 0, 1425895, 26448, 2825, 1048576⟩
    (by decide) selected_cut_50091

theorem selected_cut_50092 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 423184) = some ⟨12, 1, 0, 1415033, 423184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423184_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423184 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 423184 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 423184, 1, 65536⟩
    (by decide) selected_cut_50092

theorem selected_cut_50093 : selected 9 ⟨1425944, by decide⟩
    (prefixPartial 12 423185) = some ⟨12, 2, 0, 1425944, 423185, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_423185_1425944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423185 ⟨1425944, by decide⟩ :=
  accepted_of_selected 12 423185 ⟨1425944, by decide⟩ ⟨12, 2, 0, 1425944, 423185, 1617, 65536⟩
    (by decide) selected_cut_50093

theorem selected_cut_50094 : selected 9 ⟨1426008, by decide⟩
    (prefixPartial 12 423186) = some ⟨12, 2, 0, 1426008, 423186, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_423186_1426008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423186 ⟨1426008, by decide⟩ :=
  accepted_of_selected 12 423186 ⟨1426008, by decide⟩ ⟨12, 2, 0, 1426008, 423186, 2297, 65536⟩
    (by decide) selected_cut_50094

theorem selected_cut_50095 : selected 9 ⟨1426061, by decide⟩
    (prefixPartial 12 423187) = some ⟨12, 2, 0, 1426061, 423187, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_423187_1426061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423187 ⟨1426061, by decide⟩ :=
  accepted_of_selected 12 423187 ⟨1426061, by decide⟩ ⟨12, 2, 0, 1426061, 423187, 1941, 65536⟩
    (by decide) selected_cut_50095

theorem unmarked_context_11_105796_1426062 : frontier 10 ⟨1426062, by decide⟩
    (prefixCache 11 105796) (prefixPartial 11 105796) = false := by
  decide +kernel

theorem node_context_11_105796_1426062 : EJMOriginalGlobalDAGData.nodes 10 ⟨1426062, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1425944, by decide⟩,⟨1426008, by decide⟩,⟨1426061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105796_1426062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105796 ⟨1426062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105796
    ⟨1426062, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1425944, by decide⟩,⟨1426008, by decide⟩,⟨1426061, by decide⟩]) unmarked_context_11_105796_1426062 node_context_11_105796_1426062
  intro a
  fin_cases a
  · exact context_12_423184_1415033
  · exact context_12_423185_1425944
  · exact context_12_423186_1426008
  · exact context_12_423187_1426061

theorem selected_cut_50096 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 105797) = some ⟨11, 1, 0, 892405, 105797, 1, 262144⟩ := by
  decide +kernel

theorem context_11_105797_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105797 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 105797 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 105797, 1, 262144⟩
    (by decide) selected_cut_50096

theorem selected_cut_50097 : selected 10 ⟨1426157, by decide⟩
    (prefixPartial 11 105798) = some ⟨11, 2, 0, 1426157, 105798, 3573, 262144⟩ := by
  decide +kernel

theorem context_11_105798_1426157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105798 ⟨1426157, by decide⟩ :=
  accepted_of_selected 11 105798 ⟨1426157, by decide⟩ ⟨11, 2, 0, 1426157, 105798, 3573, 262144⟩
    (by decide) selected_cut_50097

theorem selected_cut_50098 : selected 10 ⟨1426268, by decide⟩
    (prefixPartial 11 105799) = some ⟨11, 2, 0, 1426268, 105799, 3877, 262144⟩ := by
  decide +kernel

theorem context_11_105799_1426268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105799 ⟨1426268, by decide⟩ :=
  accepted_of_selected 11 105799 ⟨1426268, by decide⟩ ⟨11, 2, 0, 1426268, 105799, 3877, 262144⟩
    (by decide) selected_cut_50098

theorem unmarked_context_10_26449_1426269 : frontier 11 ⟨1426269, by decide⟩
    (prefixCache 10 26449) (prefixPartial 10 26449) = false := by
  decide +kernel

theorem node_context_10_26449_1426269 : EJMOriginalGlobalDAGData.nodes 11 ⟨1426269, by decide⟩ =
    .split (coordinate 10) (![⟨1426062, by decide⟩,⟨892405, by decide⟩,⟨1426157, by decide⟩,⟨1426268, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26449_1426269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26449 ⟨1426269, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26449
    ⟨1426269, by decide⟩ (by decide) (![⟨1426062, by decide⟩,⟨892405, by decide⟩,⟨1426157, by decide⟩,⟨1426268, by decide⟩]) unmarked_context_10_26449_1426269 node_context_10_26449_1426269
  intro a
  fin_cases a
  · exact context_11_105796_1426062
  · exact context_11_105797_892405
  · exact context_11_105798_1426157
  · exact context_11_105799_1426268

theorem selected_cut_50099 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 423200) = some ⟨12, 1, 0, 435160, 423200, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423200_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423200 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 423200 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 423200, 1, 65536⟩
    (by decide) selected_cut_50099

theorem selected_cut_50100 : selected 9 ⟨1426347, by decide⟩
    (prefixPartial 12 423201) = some ⟨12, 2, 0, 1426347, 423201, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_423201_1426347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423201 ⟨1426347, by decide⟩ :=
  accepted_of_selected 12 423201 ⟨1426347, by decide⟩ ⟨12, 2, 0, 1426347, 423201, 2165, 65536⟩
    (by decide) selected_cut_50100

theorem selected_cut_50101 : selected 9 ⟨1426459, by decide⟩
    (prefixPartial 12 423202) = some ⟨12, 2, 0, 1426459, 423202, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_423202_1426459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423202 ⟨1426459, by decide⟩ :=
  accepted_of_selected 12 423202 ⟨1426459, by decide⟩ ⟨12, 2, 0, 1426459, 423202, 2801, 65536⟩
    (by decide) selected_cut_50101

theorem selected_cut_50102 : selected 9 ⟨1426529, by decide⟩
    (prefixPartial 12 423203) = some ⟨12, 2, 0, 1426529, 423203, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_423203_1426529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423203 ⟨1426529, by decide⟩ :=
  accepted_of_selected 12 423203 ⟨1426529, by decide⟩ ⟨12, 2, 0, 1426529, 423203, 2313, 65536⟩
    (by decide) selected_cut_50102

theorem unmarked_context_11_105800_1426530 : frontier 10 ⟨1426530, by decide⟩
    (prefixCache 11 105800) (prefixPartial 11 105800) = false := by
  decide +kernel

theorem node_context_11_105800_1426530 : EJMOriginalGlobalDAGData.nodes 10 ⟨1426530, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1426347, by decide⟩,⟨1426459, by decide⟩,⟨1426529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105800_1426530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105800 ⟨1426530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105800
    ⟨1426530, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1426347, by decide⟩,⟨1426459, by decide⟩,⟨1426529, by decide⟩]) unmarked_context_11_105800_1426530 node_context_11_105800_1426530
  intro a
  fin_cases a
  · exact context_12_423200_435160
  · exact context_12_423201_1426347
  · exact context_12_423202_1426459
  · exact context_12_423203_1426529

theorem selected_cut_50103 : selected 10 ⟨1426627, by decide⟩
    (prefixPartial 11 105801) = some ⟨11, 2, 0, 1426627, 105801, 3413, 262144⟩ := by
  decide +kernel

theorem context_11_105801_1426627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105801 ⟨1426627, by decide⟩ :=
  accepted_of_selected 11 105801 ⟨1426627, by decide⟩ ⟨11, 2, 0, 1426627, 105801, 3413, 262144⟩
    (by decide) selected_cut_50103

theorem selected_cut_50104 : selected 10 ⟨1426748, by decide⟩
    (prefixPartial 11 105802) = some ⟨11, 2, 0, 1426748, 105802, 1633, 262144⟩ := by
  decide +kernel

theorem context_11_105802_1426748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105802 ⟨1426748, by decide⟩ :=
  accepted_of_selected 11 105802 ⟨1426748, by decide⟩ ⟨11, 2, 0, 1426748, 105802, 1633, 262144⟩
    (by decide) selected_cut_50104

theorem selected_cut_50105 : selected 9 ⟨1426810, by decide⟩
    (prefixPartial 12 423212) = some ⟨12, 2, 0, 1426810, 423212, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_423212_1426810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423212 ⟨1426810, by decide⟩ :=
  accepted_of_selected 12 423212 ⟨1426810, by decide⟩ ⟨12, 2, 0, 1426810, 423212, 1145, 65536⟩
    (by decide) selected_cut_50105

theorem selected_cut_50106 : selected 9 ⟨1426865, by decide⟩
    (prefixPartial 12 423213) = some ⟨12, 2, 0, 1426865, 423213, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_423213_1426865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423213 ⟨1426865, by decide⟩ :=
  accepted_of_selected 12 423213 ⟨1426865, by decide⟩ ⟨12, 2, 0, 1426865, 423213, 1673, 65536⟩
    (by decide) selected_cut_50106

theorem selected_cut_50107 : selected 9 ⟨1426955, by decide⟩
    (prefixPartial 12 423214) = some ⟨12, 2, 0, 1426955, 423214, 2349, 65536⟩ := by
  decide +kernel

theorem context_12_423214_1426955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423214 ⟨1426955, by decide⟩ :=
  accepted_of_selected 12 423214 ⟨1426955, by decide⟩ ⟨12, 2, 0, 1426955, 423214, 2349, 65536⟩
    (by decide) selected_cut_50107

theorem selected_cut_50108 : selected 9 ⟨1427016, by decide⟩
    (prefixPartial 12 423215) = some ⟨12, 2, 0, 1427016, 423215, 817, 65536⟩ := by
  decide +kernel

theorem context_12_423215_1427016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423215 ⟨1427016, by decide⟩ :=
  accepted_of_selected 12 423215 ⟨1427016, by decide⟩ ⟨12, 2, 0, 1427016, 423215, 817, 65536⟩
    (by decide) selected_cut_50108

theorem unmarked_context_11_105803_1427017 : frontier 10 ⟨1427017, by decide⟩
    (prefixCache 11 105803) (prefixPartial 11 105803) = false := by
  decide +kernel

theorem node_context_11_105803_1427017 : EJMOriginalGlobalDAGData.nodes 10 ⟨1427017, by decide⟩ =
    .split (coordinate 11) (![⟨1426810, by decide⟩,⟨1426865, by decide⟩,⟨1426955, by decide⟩,⟨1427016, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105803_1427017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105803 ⟨1427017, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105803
    ⟨1427017, by decide⟩ (by decide) (![⟨1426810, by decide⟩,⟨1426865, by decide⟩,⟨1426955, by decide⟩,⟨1427016, by decide⟩]) unmarked_context_11_105803_1427017 node_context_11_105803_1427017
  intro a
  fin_cases a
  · exact context_12_423212_1426810
  · exact context_12_423213_1426865
  · exact context_12_423214_1426955
  · exact context_12_423215_1427016

theorem unmarked_context_10_26450_1427018 : frontier 11 ⟨1427018, by decide⟩
    (prefixCache 10 26450) (prefixPartial 10 26450) = false := by
  decide +kernel

theorem node_context_10_26450_1427018 : EJMOriginalGlobalDAGData.nodes 11 ⟨1427018, by decide⟩ =
    .split (coordinate 10) (![⟨1426530, by decide⟩,⟨1426627, by decide⟩,⟨1426748, by decide⟩,⟨1427017, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26450_1427018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26450 ⟨1427018, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26450
    ⟨1427018, by decide⟩ (by decide) (![⟨1426530, by decide⟩,⟨1426627, by decide⟩,⟨1426748, by decide⟩,⟨1427017, by decide⟩]) unmarked_context_10_26450_1427018 node_context_10_26450_1427018
  intro a
  fin_cases a
  · exact context_11_105800_1426530
  · exact context_11_105801_1426627
  · exact context_11_105802_1426748
  · exact context_11_105803_1427017

theorem selected_cut_50109 : selected 9 ⟨1416143, by decide⟩
    (prefixPartial 12 423216) = some ⟨12, 1, 0, 1416143, 423216, 1, 65536⟩ := by
  decide +kernel

theorem context_12_423216_1416143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423216 ⟨1416143, by decide⟩ :=
  accepted_of_selected 12 423216 ⟨1416143, by decide⟩ ⟨12, 1, 0, 1416143, 423216, 1, 65536⟩
    (by decide) selected_cut_50109

theorem selected_cut_50110 : selected 9 ⟨1427074, by decide⟩
    (prefixPartial 12 423217) = some ⟨12, 2, 0, 1427074, 423217, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_423217_1427074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423217 ⟨1427074, by decide⟩ :=
  accepted_of_selected 12 423217 ⟨1427074, by decide⟩ ⟨12, 2, 0, 1427074, 423217, 1361, 65536⟩
    (by decide) selected_cut_50110

theorem selected_cut_50111 : selected 9 ⟨1427141, by decide⟩
    (prefixPartial 12 423218) = some ⟨12, 2, 0, 1427141, 423218, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_423218_1427141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423218 ⟨1427141, by decide⟩ :=
  accepted_of_selected 12 423218 ⟨1427141, by decide⟩ ⟨12, 2, 0, 1427141, 423218, 1693, 65536⟩
    (by decide) selected_cut_50111

theorem selected_cut_50112 : selected 9 ⟨1427185, by decide⟩
    (prefixPartial 12 423219) = some ⟨12, 2, 0, 1427185, 423219, 1345, 65536⟩ := by
  decide +kernel

theorem context_12_423219_1427185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 423219 ⟨1427185, by decide⟩ :=
  accepted_of_selected 12 423219 ⟨1427185, by decide⟩ ⟨12, 2, 0, 1427185, 423219, 1345, 65536⟩
    (by decide) selected_cut_50112

theorem unmarked_context_11_105804_1427186 : frontier 10 ⟨1427186, by decide⟩
    (prefixCache 11 105804) (prefixPartial 11 105804) = false := by
  decide +kernel

theorem node_context_11_105804_1427186 : EJMOriginalGlobalDAGData.nodes 10 ⟨1427186, by decide⟩ =
    .split (coordinate 11) (![⟨1416143, by decide⟩,⟨1427074, by decide⟩,⟨1427141, by decide⟩,⟨1427185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_105804_1427186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105804 ⟨1427186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 105804
    ⟨1427186, by decide⟩ (by decide) (![⟨1416143, by decide⟩,⟨1427074, by decide⟩,⟨1427141, by decide⟩,⟨1427185, by decide⟩]) unmarked_context_11_105804_1427186 node_context_11_105804_1427186
  intro a
  fin_cases a
  · exact context_12_423216_1416143
  · exact context_12_423217_1427074
  · exact context_12_423218_1427141
  · exact context_12_423219_1427185

theorem selected_cut_50113 : selected 10 ⟨1427279, by decide⟩
    (prefixPartial 11 105805) = some ⟨11, 2, 0, 1427279, 105805, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_105805_1427279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105805 ⟨1427279, by decide⟩ :=
  accepted_of_selected 11 105805 ⟨1427279, by decide⟩ ⟨11, 2, 0, 1427279, 105805, 2361, 262144⟩
    (by decide) selected_cut_50113

theorem selected_cut_50114 : selected 10 ⟨1427463, by decide⟩
    (prefixPartial 11 105806) = some ⟨11, 2, 0, 1427463, 105806, 3229, 262144⟩ := by
  decide +kernel

theorem context_11_105806_1427463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105806 ⟨1427463, by decide⟩ :=
  accepted_of_selected 11 105806 ⟨1427463, by decide⟩ ⟨11, 2, 0, 1427463, 105806, 3229, 262144⟩
    (by decide) selected_cut_50114

theorem selected_cut_50115 : selected 10 ⟨1427500, by decide⟩
    (prefixPartial 11 105807) = some ⟨11, 2, 0, 1427500, 105807, 365, 262144⟩ := by
  decide +kernel

theorem context_11_105807_1427500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 105807 ⟨1427500, by decide⟩ :=
  accepted_of_selected 11 105807 ⟨1427500, by decide⟩ ⟨11, 2, 0, 1427500, 105807, 365, 262144⟩
    (by decide) selected_cut_50115

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
