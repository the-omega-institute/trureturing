/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover124
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_25922_319769 : frontier 9 ⟨319769, by decide⟩
    (prefixCache 12 25922) (prefixPartial 12 25922) = false := by
  decide +kernel

theorem node_context_12_25922_319769 : EJMOriginalGlobalDAGData.nodes 9 ⟨319769, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨319737, by decide⟩,⟨319761, by decide⟩,⟨319768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25922_319769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25922 ⟨319769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25922
    ⟨319769, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨319737, by decide⟩,⟨319761, by decide⟩,⟨319768, by decide⟩]) unmarked_context_12_25922_319769 node_context_12_25922_319769
  intro a
  fin_cases a
  · exact context_13_103688_3444
  · exact context_13_103689_319737
  · exact context_13_103690_319761
  · exact context_13_103691_319768

theorem selected_cut_12003 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103692) = some ⟨13, 1, 0, 3444, 103692, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103692_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103692 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103692 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103692, 1, 16384⟩
    (by decide) selected_cut_12003

theorem selected_cut_12004 : selected 8 ⟨319795, by decide⟩
    (prefixPartial 13 103693) = some ⟨13, 2, 0, 319795, 103693, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_103693_319795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103693 ⟨319795, by decide⟩ :=
  accepted_of_selected 13 103693 ⟨319795, by decide⟩ ⟨13, 2, 0, 319795, 103693, 2425, 16384⟩
    (by decide) selected_cut_12004

theorem selected_cut_12005 : selected 8 ⟨319823, by decide⟩
    (prefixPartial 13 103694) = some ⟨13, 2, 0, 319823, 103694, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_103694_319823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103694 ⟨319823, by decide⟩ :=
  accepted_of_selected 13 103694 ⟨319823, by decide⟩ ⟨13, 2, 0, 319823, 103694, 2501, 16384⟩
    (by decide) selected_cut_12005

theorem selected_cut_12006 : selected 8 ⟨319830, by decide⟩
    (prefixPartial 13 103695) = some ⟨13, 2, 0, 319830, 103695, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_103695_319830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103695 ⟨319830, by decide⟩ :=
  accepted_of_selected 13 103695 ⟨319830, by decide⟩ ⟨13, 2, 0, 319830, 103695, 1029, 16384⟩
    (by decide) selected_cut_12006

theorem unmarked_context_12_25923_319831 : frontier 9 ⟨319831, by decide⟩
    (prefixCache 12 25923) (prefixPartial 12 25923) = false := by
  decide +kernel

theorem node_context_12_25923_319831 : EJMOriginalGlobalDAGData.nodes 9 ⟨319831, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨319795, by decide⟩,⟨319823, by decide⟩,⟨319830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25923_319831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25923 ⟨319831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25923
    ⟨319831, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨319795, by decide⟩,⟨319823, by decide⟩,⟨319830, by decide⟩]) unmarked_context_12_25923_319831 node_context_12_25923_319831
  intro a
  fin_cases a
  · exact context_13_103692_3444
  · exact context_13_103693_319795
  · exact context_13_103694_319823
  · exact context_13_103695_319830

theorem unmarked_context_11_6480_319832 : frontier 10 ⟨319832, by decide⟩
    (prefixCache 11 6480) (prefixPartial 11 6480) = false := by
  decide +kernel

theorem node_context_11_6480_319832 : EJMOriginalGlobalDAGData.nodes 10 ⟨319832, by decide⟩ =
    .split (coordinate 11) (![⟨319590, by decide⟩,⟨319699, by decide⟩,⟨319769, by decide⟩,⟨319831, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6480_319832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6480 ⟨319832, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6480
    ⟨319832, by decide⟩ (by decide) (![⟨319590, by decide⟩,⟨319699, by decide⟩,⟨319769, by decide⟩,⟨319831, by decide⟩]) unmarked_context_11_6480_319832 node_context_11_6480_319832
  intro a
  fin_cases a
  · exact context_12_25920_319590
  · exact context_12_25921_319699
  · exact context_12_25922_319769
  · exact context_12_25923_319831

theorem selected_cut_12007 : selected 9 ⟨319886, by decide⟩
    (prefixPartial 12 25924) = some ⟨12, 2, 0, 319886, 25924, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_25924_319886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25924 ⟨319886, by decide⟩ :=
  accepted_of_selected 12 25924 ⟨319886, by decide⟩ ⟨12, 2, 0, 319886, 25924, 4037, 65536⟩
    (by decide) selected_cut_12007

theorem selected_cut_12008 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 25925) = some ⟨12, 1, 0, 126884, 25925, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25925_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25925 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 25925 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 25925, 1, 65536⟩
    (by decide) selected_cut_12008

theorem selected_cut_12009 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103704) = some ⟨13, 1, 0, 3444, 103704, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103704_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103704 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103704 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103704, 1, 16384⟩
    (by decide) selected_cut_12009

theorem selected_cut_12010 : selected 8 ⟨319906, by decide⟩
    (prefixPartial 13 103705) = some ⟨13, 2, 0, 319906, 103705, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_103705_319906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103705 ⟨319906, by decide⟩ :=
  accepted_of_selected 13 103705 ⟨319906, by decide⟩ ⟨13, 2, 0, 319906, 103705, 1497, 16384⟩
    (by decide) selected_cut_12010

theorem selected_cut_12011 : selected 8 ⟨319929, by decide⟩
    (prefixPartial 13 103706) = some ⟨13, 2, 0, 319929, 103706, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_103706_319929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103706 ⟨319929, by decide⟩ :=
  accepted_of_selected 13 103706 ⟨319929, by decide⟩ ⟨13, 2, 0, 319929, 103706, 1873, 16384⟩
    (by decide) selected_cut_12011

theorem selected_cut_12012 : selected 8 ⟨319936, by decide⟩
    (prefixPartial 13 103707) = some ⟨13, 2, 0, 319936, 103707, 909, 16384⟩ := by
  decide +kernel

theorem context_13_103707_319936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103707 ⟨319936, by decide⟩ :=
  accepted_of_selected 13 103707 ⟨319936, by decide⟩ ⟨13, 2, 0, 319936, 103707, 909, 16384⟩
    (by decide) selected_cut_12012

theorem unmarked_context_12_25926_319937 : frontier 9 ⟨319937, by decide⟩
    (prefixCache 12 25926) (prefixPartial 12 25926) = false := by
  decide +kernel

theorem node_context_12_25926_319937 : EJMOriginalGlobalDAGData.nodes 9 ⟨319937, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨319906, by decide⟩,⟨319929, by decide⟩,⟨319936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25926_319937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25926 ⟨319937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25926
    ⟨319937, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨319906, by decide⟩,⟨319929, by decide⟩,⟨319936, by decide⟩]) unmarked_context_12_25926_319937 node_context_12_25926_319937
  intro a
  fin_cases a
  · exact context_13_103704_3444
  · exact context_13_103705_319906
  · exact context_13_103706_319929
  · exact context_13_103707_319936

theorem selected_cut_12013 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103708) = some ⟨13, 1, 0, 3444, 103708, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103708_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103708 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103708 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103708, 1, 16384⟩
    (by decide) selected_cut_12013

theorem selected_cut_12014 : selected 8 ⟨319961, by decide⟩
    (prefixPartial 13 103709) = some ⟨13, 2, 0, 319961, 103709, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_103709_319961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103709 ⟨319961, by decide⟩ :=
  accepted_of_selected 13 103709 ⟨319961, by decide⟩ ⟨13, 2, 0, 319961, 103709, 1769, 16384⟩
    (by decide) selected_cut_12014

theorem selected_cut_12015 : selected 8 ⟨319985, by decide⟩
    (prefixPartial 13 103710) = some ⟨13, 2, 0, 319985, 103710, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_103710_319985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103710 ⟨319985, by decide⟩ :=
  accepted_of_selected 13 103710 ⟨319985, by decide⟩ ⟨13, 2, 0, 319985, 103710, 1929, 16384⟩
    (by decide) selected_cut_12015

theorem selected_cut_12016 : selected 8 ⟨319996, by decide⟩
    (prefixPartial 13 103711) = some ⟨13, 2, 0, 319996, 103711, 881, 16384⟩ := by
  decide +kernel

theorem context_13_103711_319996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103711 ⟨319996, by decide⟩ :=
  accepted_of_selected 13 103711 ⟨319996, by decide⟩ ⟨13, 2, 0, 319996, 103711, 881, 16384⟩
    (by decide) selected_cut_12016

theorem unmarked_context_12_25927_319997 : frontier 9 ⟨319997, by decide⟩
    (prefixCache 12 25927) (prefixPartial 12 25927) = false := by
  decide +kernel

theorem node_context_12_25927_319997 : EJMOriginalGlobalDAGData.nodes 9 ⟨319997, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨319961, by decide⟩,⟨319985, by decide⟩,⟨319996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25927_319997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25927 ⟨319997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25927
    ⟨319997, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨319961, by decide⟩,⟨319985, by decide⟩,⟨319996, by decide⟩]) unmarked_context_12_25927_319997 node_context_12_25927_319997
  intro a
  fin_cases a
  · exact context_13_103708_3444
  · exact context_13_103709_319961
  · exact context_13_103710_319985
  · exact context_13_103711_319996

theorem unmarked_context_11_6481_319998 : frontier 10 ⟨319998, by decide⟩
    (prefixCache 11 6481) (prefixPartial 11 6481) = false := by
  decide +kernel

theorem node_context_11_6481_319998 : EJMOriginalGlobalDAGData.nodes 10 ⟨319998, by decide⟩ =
    .split (coordinate 11) (![⟨319886, by decide⟩,⟨126884, by decide⟩,⟨319937, by decide⟩,⟨319997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6481_319998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6481 ⟨319998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6481
    ⟨319998, by decide⟩ (by decide) (![⟨319886, by decide⟩,⟨126884, by decide⟩,⟨319937, by decide⟩,⟨319997, by decide⟩]) unmarked_context_11_6481_319998 node_context_11_6481_319998
  intro a
  fin_cases a
  · exact context_12_25924_319886
  · exact context_12_25925_126884
  · exact context_12_25926_319937
  · exact context_12_25927_319997

theorem selected_cut_12017 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103712) = some ⟨13, 1, 0, 3444, 103712, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103712_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103712 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103712 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103712, 1, 16384⟩
    (by decide) selected_cut_12017

theorem selected_cut_12018 : selected 8 ⟨320026, by decide⟩
    (prefixPartial 13 103713) = some ⟨13, 2, 0, 320026, 103713, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_103713_320026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103713 ⟨320026, by decide⟩ :=
  accepted_of_selected 13 103713 ⟨320026, by decide⟩ ⟨13, 2, 0, 320026, 103713, 2165, 16384⟩
    (by decide) selected_cut_12018

theorem selected_cut_12019 : selected 8 ⟨320049, by decide⟩
    (prefixPartial 13 103714) = some ⟨13, 2, 0, 320049, 103714, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_103714_320049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103714 ⟨320049, by decide⟩ :=
  accepted_of_selected 13 103714 ⟨320049, by decide⟩ ⟨13, 2, 0, 320049, 103714, 2121, 16384⟩
    (by decide) selected_cut_12019

theorem selected_cut_12020 : selected 8 ⟨320058, by decide⟩
    (prefixPartial 13 103715) = some ⟨13, 2, 0, 320058, 103715, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_103715_320058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103715 ⟨320058, by decide⟩ :=
  accepted_of_selected 13 103715 ⟨320058, by decide⟩ ⟨13, 2, 0, 320058, 103715, 1013, 16384⟩
    (by decide) selected_cut_12020

theorem unmarked_context_12_25928_320059 : frontier 9 ⟨320059, by decide⟩
    (prefixCache 12 25928) (prefixPartial 12 25928) = false := by
  decide +kernel

theorem node_context_12_25928_320059 : EJMOriginalGlobalDAGData.nodes 9 ⟨320059, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320026, by decide⟩,⟨320049, by decide⟩,⟨320058, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25928_320059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25928 ⟨320059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25928
    ⟨320059, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320026, by decide⟩,⟨320049, by decide⟩,⟨320058, by decide⟩]) unmarked_context_12_25928_320059 node_context_12_25928_320059
  intro a
  fin_cases a
  · exact context_13_103712_3444
  · exact context_13_103713_320026
  · exact context_13_103714_320049
  · exact context_13_103715_320058

theorem selected_cut_12021 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103716) = some ⟨13, 1, 0, 3444, 103716, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103716_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103716 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103716 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103716, 1, 16384⟩
    (by decide) selected_cut_12021

theorem selected_cut_12022 : selected 8 ⟨320101, by decide⟩
    (prefixPartial 13 103717) = some ⟨13, 2, 0, 320101, 103717, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_103717_320101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103717 ⟨320101, by decide⟩ :=
  accepted_of_selected 13 103717 ⟨320101, by decide⟩ ⟨13, 2, 0, 320101, 103717, 2633, 16384⟩
    (by decide) selected_cut_12022

theorem selected_cut_12023 : selected 8 ⟨320142, by decide⟩
    (prefixPartial 13 103718) = some ⟨13, 2, 0, 320142, 103718, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_103718_320142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103718 ⟨320142, by decide⟩ :=
  accepted_of_selected 13 103718 ⟨320142, by decide⟩ ⟨13, 2, 0, 320142, 103718, 2761, 16384⟩
    (by decide) selected_cut_12023

theorem selected_cut_12024 : selected 8 ⟨320162, by decide⟩
    (prefixPartial 13 103719) = some ⟨13, 2, 0, 320162, 103719, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_103719_320162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103719 ⟨320162, by decide⟩ :=
  accepted_of_selected 13 103719 ⟨320162, by decide⟩ ⟨13, 2, 0, 320162, 103719, 1369, 16384⟩
    (by decide) selected_cut_12024

theorem unmarked_context_12_25929_320163 : frontier 9 ⟨320163, by decide⟩
    (prefixCache 12 25929) (prefixPartial 12 25929) = false := by
  decide +kernel

theorem node_context_12_25929_320163 : EJMOriginalGlobalDAGData.nodes 9 ⟨320163, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320101, by decide⟩,⟨320142, by decide⟩,⟨320162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25929_320163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25929 ⟨320163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25929
    ⟨320163, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320101, by decide⟩,⟨320142, by decide⟩,⟨320162, by decide⟩]) unmarked_context_12_25929_320163 node_context_12_25929_320163
  intro a
  fin_cases a
  · exact context_13_103716_3444
  · exact context_13_103717_320101
  · exact context_13_103718_320142
  · exact context_13_103719_320162

theorem selected_cut_12025 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103720) = some ⟨13, 1, 0, 3444, 103720, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103720_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103720 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103720 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103720, 1, 16384⟩
    (by decide) selected_cut_12025

theorem selected_cut_12026 : selected 8 ⟨320188, by decide⟩
    (prefixPartial 13 103721) = some ⟨13, 2, 0, 320188, 103721, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_103721_320188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103721 ⟨320188, by decide⟩ :=
  accepted_of_selected 13 103721 ⟨320188, by decide⟩ ⟨13, 2, 0, 320188, 103721, 1953, 16384⟩
    (by decide) selected_cut_12026

theorem selected_cut_12027 : selected 8 ⟨320211, by decide⟩
    (prefixPartial 13 103722) = some ⟨13, 2, 0, 320211, 103722, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_103722_320211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103722 ⟨320211, by decide⟩ :=
  accepted_of_selected 13 103722 ⟨320211, by decide⟩ ⟨13, 2, 0, 320211, 103722, 2185, 16384⟩
    (by decide) selected_cut_12027

theorem selected_cut_12028 : selected 8 ⟨320221, by decide⟩
    (prefixPartial 13 103723) = some ⟨13, 2, 0, 320221, 103723, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_103723_320221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103723 ⟨320221, by decide⟩ :=
  accepted_of_selected 13 103723 ⟨320221, by decide⟩ ⟨13, 2, 0, 320221, 103723, 1017, 16384⟩
    (by decide) selected_cut_12028

theorem unmarked_context_12_25930_320222 : frontier 9 ⟨320222, by decide⟩
    (prefixCache 12 25930) (prefixPartial 12 25930) = false := by
  decide +kernel

theorem node_context_12_25930_320222 : EJMOriginalGlobalDAGData.nodes 9 ⟨320222, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320188, by decide⟩,⟨320211, by decide⟩,⟨320221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25930_320222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25930 ⟨320222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25930
    ⟨320222, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320188, by decide⟩,⟨320211, by decide⟩,⟨320221, by decide⟩]) unmarked_context_12_25930_320222 node_context_12_25930_320222
  intro a
  fin_cases a
  · exact context_13_103720_3444
  · exact context_13_103721_320188
  · exact context_13_103722_320211
  · exact context_13_103723_320221

theorem selected_cut_12029 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103724) = some ⟨13, 1, 0, 3444, 103724, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103724_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103724 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103724 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103724, 1, 16384⟩
    (by decide) selected_cut_12029

theorem selected_cut_12030 : selected 8 ⟨320253, by decide⟩
    (prefixPartial 13 103725) = some ⟨13, 2, 0, 320253, 103725, 2185, 16384⟩ := by
  decide +kernel

theorem context_13_103725_320253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103725 ⟨320253, by decide⟩ :=
  accepted_of_selected 13 103725 ⟨320253, by decide⟩ ⟨13, 2, 0, 320253, 103725, 2185, 16384⟩
    (by decide) selected_cut_12030

theorem selected_cut_12031 : selected 8 ⟨320272, by decide⟩
    (prefixPartial 13 103726) = some ⟨13, 2, 0, 320272, 103726, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_103726_320272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103726 ⟨320272, by decide⟩ :=
  accepted_of_selected 13 103726 ⟨320272, by decide⟩ ⟨13, 2, 0, 320272, 103726, 2181, 16384⟩
    (by decide) selected_cut_12031

theorem selected_cut_12032 : selected 8 ⟨320280, by decide⟩
    (prefixPartial 13 103727) = some ⟨13, 2, 0, 320280, 103727, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_103727_320280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103727 ⟨320280, by decide⟩ :=
  accepted_of_selected 13 103727 ⟨320280, by decide⟩ ⟨13, 2, 0, 320280, 103727, 1073, 16384⟩
    (by decide) selected_cut_12032

theorem unmarked_context_12_25931_320281 : frontier 9 ⟨320281, by decide⟩
    (prefixCache 12 25931) (prefixPartial 12 25931) = false := by
  decide +kernel

theorem node_context_12_25931_320281 : EJMOriginalGlobalDAGData.nodes 9 ⟨320281, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320253, by decide⟩,⟨320272, by decide⟩,⟨320280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25931_320281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25931 ⟨320281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25931
    ⟨320281, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320253, by decide⟩,⟨320272, by decide⟩,⟨320280, by decide⟩]) unmarked_context_12_25931_320281 node_context_12_25931_320281
  intro a
  fin_cases a
  · exact context_13_103724_3444
  · exact context_13_103725_320253
  · exact context_13_103726_320272
  · exact context_13_103727_320280

theorem unmarked_context_11_6482_320282 : frontier 10 ⟨320282, by decide⟩
    (prefixCache 11 6482) (prefixPartial 11 6482) = false := by
  decide +kernel

theorem node_context_11_6482_320282 : EJMOriginalGlobalDAGData.nodes 10 ⟨320282, by decide⟩ =
    .split (coordinate 11) (![⟨320059, by decide⟩,⟨320163, by decide⟩,⟨320222, by decide⟩,⟨320281, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6482_320282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6482 ⟨320282, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6482
    ⟨320282, by decide⟩ (by decide) (![⟨320059, by decide⟩,⟨320163, by decide⟩,⟨320222, by decide⟩,⟨320281, by decide⟩]) unmarked_context_11_6482_320282 node_context_11_6482_320282
  intro a
  fin_cases a
  · exact context_12_25928_320059
  · exact context_12_25929_320163
  · exact context_12_25930_320222
  · exact context_12_25931_320281

theorem selected_cut_12033 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103728) = some ⟨13, 1, 0, 3444, 103728, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103728_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103728 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103728 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103728, 1, 16384⟩
    (by decide) selected_cut_12033

theorem selected_cut_12034 : selected 8 ⟨320307, by decide⟩
    (prefixPartial 13 103729) = some ⟨13, 2, 0, 320307, 103729, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_103729_320307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103729 ⟨320307, by decide⟩ :=
  accepted_of_selected 13 103729 ⟨320307, by decide⟩ ⟨13, 2, 0, 320307, 103729, 1937, 16384⟩
    (by decide) selected_cut_12034

theorem selected_cut_12035 : selected 8 ⟨320331, by decide⟩
    (prefixPartial 13 103730) = some ⟨13, 2, 0, 320331, 103730, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_103730_320331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103730 ⟨320331, by decide⟩ :=
  accepted_of_selected 13 103730 ⟨320331, by decide⟩ ⟨13, 2, 0, 320331, 103730, 2009, 16384⟩
    (by decide) selected_cut_12035

theorem selected_cut_12036 : selected 8 ⟨320339, by decide⟩
    (prefixPartial 13 103731) = some ⟨13, 2, 0, 320339, 103731, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_103731_320339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103731 ⟨320339, by decide⟩ :=
  accepted_of_selected 13 103731 ⟨320339, by decide⟩ ⟨13, 2, 0, 320339, 103731, 1037, 16384⟩
    (by decide) selected_cut_12036

theorem unmarked_context_12_25932_320340 : frontier 9 ⟨320340, by decide⟩
    (prefixCache 12 25932) (prefixPartial 12 25932) = false := by
  decide +kernel

theorem node_context_12_25932_320340 : EJMOriginalGlobalDAGData.nodes 9 ⟨320340, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320307, by decide⟩,⟨320331, by decide⟩,⟨320339, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25932_320340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25932 ⟨320340, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25932
    ⟨320340, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320307, by decide⟩,⟨320331, by decide⟩,⟨320339, by decide⟩]) unmarked_context_12_25932_320340 node_context_12_25932_320340
  intro a
  fin_cases a
  · exact context_13_103728_3444
  · exact context_13_103729_320307
  · exact context_13_103730_320331
  · exact context_13_103731_320339

theorem selected_cut_12037 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103732) = some ⟨13, 1, 0, 3444, 103732, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103732_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103732 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103732 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103732, 1, 16384⟩
    (by decide) selected_cut_12037

theorem selected_cut_12038 : selected 8 ⟨320374, by decide⟩
    (prefixPartial 13 103733) = some ⟨13, 2, 0, 320374, 103733, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_103733_320374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103733 ⟨320374, by decide⟩ :=
  accepted_of_selected 13 103733 ⟨320374, by decide⟩ ⟨13, 2, 0, 320374, 103733, 2337, 16384⟩
    (by decide) selected_cut_12038

theorem selected_cut_12039 : selected 8 ⟨320412, by decide⟩
    (prefixPartial 13 103734) = some ⟨13, 2, 0, 320412, 103734, 2773, 16384⟩ := by
  decide +kernel

theorem context_13_103734_320412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103734 ⟨320412, by decide⟩ :=
  accepted_of_selected 13 103734 ⟨320412, by decide⟩ ⟨13, 2, 0, 320412, 103734, 2773, 16384⟩
    (by decide) selected_cut_12039

theorem selected_cut_12040 : selected 8 ⟨320434, by decide⟩
    (prefixPartial 13 103735) = some ⟨13, 2, 0, 320434, 103735, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_103735_320434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103735 ⟨320434, by decide⟩ :=
  accepted_of_selected 13 103735 ⟨320434, by decide⟩ ⟨13, 2, 0, 320434, 103735, 1281, 16384⟩
    (by decide) selected_cut_12040

theorem unmarked_context_12_25933_320435 : frontier 9 ⟨320435, by decide⟩
    (prefixCache 12 25933) (prefixPartial 12 25933) = false := by
  decide +kernel

theorem node_context_12_25933_320435 : EJMOriginalGlobalDAGData.nodes 9 ⟨320435, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320374, by decide⟩,⟨320412, by decide⟩,⟨320434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25933_320435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25933 ⟨320435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25933
    ⟨320435, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320374, by decide⟩,⟨320412, by decide⟩,⟨320434, by decide⟩]) unmarked_context_12_25933_320435 node_context_12_25933_320435
  intro a
  fin_cases a
  · exact context_13_103732_3444
  · exact context_13_103733_320374
  · exact context_13_103734_320412
  · exact context_13_103735_320434

theorem selected_cut_12041 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103736) = some ⟨13, 1, 0, 3444, 103736, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103736_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103736 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103736 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103736, 1, 16384⟩
    (by decide) selected_cut_12041

theorem selected_cut_12042 : selected 8 ⟨320460, by decide⟩
    (prefixPartial 13 103737) = some ⟨13, 2, 0, 320460, 103737, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_103737_320460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103737 ⟨320460, by decide⟩ :=
  accepted_of_selected 13 103737 ⟨320460, by decide⟩ ⟨13, 2, 0, 320460, 103737, 1741, 16384⟩
    (by decide) selected_cut_12042

theorem selected_cut_12043 : selected 8 ⟨320483, by decide⟩
    (prefixPartial 13 103738) = some ⟨13, 2, 0, 320483, 103738, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_103738_320483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103738 ⟨320483, by decide⟩ :=
  accepted_of_selected 13 103738 ⟨320483, by decide⟩ ⟨13, 2, 0, 320483, 103738, 2145, 16384⟩
    (by decide) selected_cut_12043

theorem selected_cut_12044 : selected 8 ⟨320490, by decide⟩
    (prefixPartial 13 103739) = some ⟨13, 2, 0, 320490, 103739, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_103739_320490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103739 ⟨320490, by decide⟩ :=
  accepted_of_selected 13 103739 ⟨320490, by decide⟩ ⟨13, 2, 0, 320490, 103739, 1041, 16384⟩
    (by decide) selected_cut_12044

theorem unmarked_context_12_25934_320491 : frontier 9 ⟨320491, by decide⟩
    (prefixCache 12 25934) (prefixPartial 12 25934) = false := by
  decide +kernel

theorem node_context_12_25934_320491 : EJMOriginalGlobalDAGData.nodes 9 ⟨320491, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320460, by decide⟩,⟨320483, by decide⟩,⟨320490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25934_320491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25934 ⟨320491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25934
    ⟨320491, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320460, by decide⟩,⟨320483, by decide⟩,⟨320490, by decide⟩]) unmarked_context_12_25934_320491 node_context_12_25934_320491
  intro a
  fin_cases a
  · exact context_13_103736_3444
  · exact context_13_103737_320460
  · exact context_13_103738_320483
  · exact context_13_103739_320490

theorem selected_cut_12045 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103740) = some ⟨13, 1, 0, 3444, 103740, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103740_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103740 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103740 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103740, 1, 16384⟩
    (by decide) selected_cut_12045

theorem selected_cut_12046 : selected 8 ⟨320510, by decide⟩
    (prefixPartial 13 103741) = some ⟨13, 2, 0, 320510, 103741, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_103741_320510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103741 ⟨320510, by decide⟩ :=
  accepted_of_selected 13 103741 ⟨320510, by decide⟩ ⟨13, 2, 0, 320510, 103741, 1709, 16384⟩
    (by decide) selected_cut_12046

theorem selected_cut_12047 : selected 8 ⟨320529, by decide⟩
    (prefixPartial 13 103742) = some ⟨13, 2, 0, 320529, 103742, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_103742_320529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103742 ⟨320529, by decide⟩ :=
  accepted_of_selected 13 103742 ⟨320529, by decide⟩ ⟨13, 2, 0, 320529, 103742, 2149, 16384⟩
    (by decide) selected_cut_12047

theorem selected_cut_12048 : selected 8 ⟨320535, by decide⟩
    (prefixPartial 13 103743) = some ⟨13, 2, 0, 320535, 103743, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_103743_320535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103743 ⟨320535, by decide⟩ :=
  accepted_of_selected 13 103743 ⟨320535, by decide⟩ ⟨13, 2, 0, 320535, 103743, 1085, 16384⟩
    (by decide) selected_cut_12048

theorem unmarked_context_12_25935_320536 : frontier 9 ⟨320536, by decide⟩
    (prefixCache 12 25935) (prefixPartial 12 25935) = false := by
  decide +kernel

theorem node_context_12_25935_320536 : EJMOriginalGlobalDAGData.nodes 9 ⟨320536, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320510, by decide⟩,⟨320529, by decide⟩,⟨320535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25935_320536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25935 ⟨320536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25935
    ⟨320536, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320510, by decide⟩,⟨320529, by decide⟩,⟨320535, by decide⟩]) unmarked_context_12_25935_320536 node_context_12_25935_320536
  intro a
  fin_cases a
  · exact context_13_103740_3444
  · exact context_13_103741_320510
  · exact context_13_103742_320529
  · exact context_13_103743_320535

theorem unmarked_context_11_6483_320537 : frontier 10 ⟨320537, by decide⟩
    (prefixCache 11 6483) (prefixPartial 11 6483) = false := by
  decide +kernel

theorem node_context_11_6483_320537 : EJMOriginalGlobalDAGData.nodes 10 ⟨320537, by decide⟩ =
    .split (coordinate 11) (![⟨320340, by decide⟩,⟨320435, by decide⟩,⟨320491, by decide⟩,⟨320536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6483_320537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6483 ⟨320537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6483
    ⟨320537, by decide⟩ (by decide) (![⟨320340, by decide⟩,⟨320435, by decide⟩,⟨320491, by decide⟩,⟨320536, by decide⟩]) unmarked_context_11_6483_320537 node_context_11_6483_320537
  intro a
  fin_cases a
  · exact context_12_25932_320340
  · exact context_12_25933_320435
  · exact context_12_25934_320491
  · exact context_12_25935_320536

theorem unmarked_context_10_1620_320538 : frontier 11 ⟨320538, by decide⟩
    (prefixCache 10 1620) (prefixPartial 10 1620) = false := by
  decide +kernel

theorem node_context_10_1620_320538 : EJMOriginalGlobalDAGData.nodes 11 ⟨320538, by decide⟩ =
    .split (coordinate 10) (![⟨319832, by decide⟩,⟨319998, by decide⟩,⟨320282, by decide⟩,⟨320537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1620_320538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1620 ⟨320538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1620
    ⟨320538, by decide⟩ (by decide) (![⟨319832, by decide⟩,⟨319998, by decide⟩,⟨320282, by decide⟩,⟨320537, by decide⟩]) unmarked_context_10_1620_320538 node_context_10_1620_320538
  intro a
  fin_cases a
  · exact context_11_6480_319832
  · exact context_11_6481_319998
  · exact context_11_6482_320282
  · exact context_11_6483_320537

theorem selected_cut_12049 : selected 9 ⟨320578, by decide⟩
    (prefixPartial 12 25936) = some ⟨12, 2, 0, 320578, 25936, 3841, 65536⟩ := by
  decide +kernel

theorem context_12_25936_320578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25936 ⟨320578, by decide⟩ :=
  accepted_of_selected 12 25936 ⟨320578, by decide⟩ ⟨12, 2, 0, 320578, 25936, 3841, 65536⟩
    (by decide) selected_cut_12049

theorem selected_cut_12050 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 25937) = some ⟨12, 1, 0, 170504, 25937, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25937_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25937 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 25937 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 25937, 1, 65536⟩
    (by decide) selected_cut_12050

theorem selected_cut_12051 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103752) = some ⟨13, 1, 0, 3444, 103752, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103752_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103752 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103752 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103752, 1, 16384⟩
    (by decide) selected_cut_12051

theorem selected_cut_12052 : selected 8 ⟨320596, by decide⟩
    (prefixPartial 13 103753) = some ⟨13, 2, 0, 320596, 103753, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_103753_320596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103753 ⟨320596, by decide⟩ :=
  accepted_of_selected 13 103753 ⟨320596, by decide⟩ ⟨13, 2, 0, 320596, 103753, 1509, 16384⟩
    (by decide) selected_cut_12052

theorem selected_cut_12053 : selected 8 ⟨320621, by decide⟩
    (prefixPartial 13 103754) = some ⟨13, 2, 0, 320621, 103754, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_103754_320621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103754 ⟨320621, by decide⟩ :=
  accepted_of_selected 13 103754 ⟨320621, by decide⟩ ⟨13, 2, 0, 320621, 103754, 2045, 16384⟩
    (by decide) selected_cut_12053

theorem selected_cut_12054 : selected 8 ⟨320629, by decide⟩
    (prefixPartial 13 103755) = some ⟨13, 2, 0, 320629, 103755, 893, 16384⟩ := by
  decide +kernel

theorem context_13_103755_320629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103755 ⟨320629, by decide⟩ :=
  accepted_of_selected 13 103755 ⟨320629, by decide⟩ ⟨13, 2, 0, 320629, 103755, 893, 16384⟩
    (by decide) selected_cut_12054

theorem unmarked_context_12_25938_320630 : frontier 9 ⟨320630, by decide⟩
    (prefixCache 12 25938) (prefixPartial 12 25938) = false := by
  decide +kernel

theorem node_context_12_25938_320630 : EJMOriginalGlobalDAGData.nodes 9 ⟨320630, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320596, by decide⟩,⟨320621, by decide⟩,⟨320629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25938_320630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25938 ⟨320630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25938
    ⟨320630, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320596, by decide⟩,⟨320621, by decide⟩,⟨320629, by decide⟩]) unmarked_context_12_25938_320630 node_context_12_25938_320630
  intro a
  fin_cases a
  · exact context_13_103752_3444
  · exact context_13_103753_320596
  · exact context_13_103754_320621
  · exact context_13_103755_320629

theorem selected_cut_12055 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103756) = some ⟨13, 1, 0, 3444, 103756, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103756_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103756 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103756 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103756, 1, 16384⟩
    (by decide) selected_cut_12055

theorem selected_cut_12056 : selected 8 ⟨320646, by decide⟩
    (prefixPartial 13 103757) = some ⟨13, 2, 0, 320646, 103757, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_103757_320646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103757 ⟨320646, by decide⟩ :=
  accepted_of_selected 13 103757 ⟨320646, by decide⟩ ⟨13, 2, 0, 320646, 103757, 1605, 16384⟩
    (by decide) selected_cut_12056

theorem selected_cut_12057 : selected 8 ⟨320669, by decide⟩
    (prefixPartial 13 103758) = some ⟨13, 2, 0, 320669, 103758, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_103758_320669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103758 ⟨320669, by decide⟩ :=
  accepted_of_selected 13 103758 ⟨320669, by decide⟩ ⟨13, 2, 0, 320669, 103758, 2021, 16384⟩
    (by decide) selected_cut_12057

theorem selected_cut_12058 : selected 8 ⟨320674, by decide⟩
    (prefixPartial 13 103759) = some ⟨13, 2, 0, 320674, 103759, 897, 16384⟩ := by
  decide +kernel

theorem context_13_103759_320674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103759 ⟨320674, by decide⟩ :=
  accepted_of_selected 13 103759 ⟨320674, by decide⟩ ⟨13, 2, 0, 320674, 103759, 897, 16384⟩
    (by decide) selected_cut_12058

theorem unmarked_context_12_25939_320675 : frontier 9 ⟨320675, by decide⟩
    (prefixCache 12 25939) (prefixPartial 12 25939) = false := by
  decide +kernel

theorem node_context_12_25939_320675 : EJMOriginalGlobalDAGData.nodes 9 ⟨320675, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320646, by decide⟩,⟨320669, by decide⟩,⟨320674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25939_320675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25939 ⟨320675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25939
    ⟨320675, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320646, by decide⟩,⟨320669, by decide⟩,⟨320674, by decide⟩]) unmarked_context_12_25939_320675 node_context_12_25939_320675
  intro a
  fin_cases a
  · exact context_13_103756_3444
  · exact context_13_103757_320646
  · exact context_13_103758_320669
  · exact context_13_103759_320674

theorem unmarked_context_11_6484_320676 : frontier 10 ⟨320676, by decide⟩
    (prefixCache 11 6484) (prefixPartial 11 6484) = false := by
  decide +kernel

theorem node_context_11_6484_320676 : EJMOriginalGlobalDAGData.nodes 10 ⟨320676, by decide⟩ =
    .split (coordinate 11) (![⟨320578, by decide⟩,⟨170504, by decide⟩,⟨320630, by decide⟩,⟨320675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6484_320676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6484 ⟨320676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6484
    ⟨320676, by decide⟩ (by decide) (![⟨320578, by decide⟩,⟨170504, by decide⟩,⟨320630, by decide⟩,⟨320675, by decide⟩]) unmarked_context_11_6484_320676 node_context_11_6484_320676
  intro a
  fin_cases a
  · exact context_12_25936_320578
  · exact context_12_25937_170504
  · exact context_12_25938_320630
  · exact context_12_25939_320675

theorem selected_cut_12059 : selected 10 ⟨320678, by decide⟩
    (prefixPartial 11 6485) = some ⟨11, 2, 0, 320678, 6485, 5, 262144⟩ := by
  decide +kernel

theorem context_11_6485_320678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6485 ⟨320678, by decide⟩ :=
  accepted_of_selected 11 6485 ⟨320678, by decide⟩ ⟨11, 2, 0, 320678, 6485, 5, 262144⟩
    (by decide) selected_cut_12059

theorem selected_cut_12060 : selected 9 ⟨320723, by decide⟩
    (prefixPartial 12 25944) = some ⟨12, 2, 0, 320723, 25944, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_25944_320723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25944 ⟨320723, by decide⟩ :=
  accepted_of_selected 12 25944 ⟨320723, by decide⟩ ⟨12, 2, 0, 320723, 25944, 3953, 65536⟩
    (by decide) selected_cut_12060

theorem selected_cut_12061 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 25945) = some ⟨12, 1, 0, 126371, 25945, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25945_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25945 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 25945 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 25945, 1, 65536⟩
    (by decide) selected_cut_12061

theorem selected_cut_12062 : selected 9 ⟨320769, by decide⟩
    (prefixPartial 12 25946) = some ⟨12, 2, 0, 320769, 25946, 4053, 65536⟩ := by
  decide +kernel

theorem context_12_25946_320769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25946 ⟨320769, by decide⟩ :=
  accepted_of_selected 12 25946 ⟨320769, by decide⟩ ⟨12, 2, 0, 320769, 25946, 4053, 65536⟩
    (by decide) selected_cut_12062

theorem selected_cut_12063 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103788) = some ⟨13, 1, 0, 3444, 103788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103788, 1, 16384⟩
    (by decide) selected_cut_12063

theorem selected_cut_12064 : selected 8 ⟨320787, by decide⟩
    (prefixPartial 13 103789) = some ⟨13, 2, 0, 320787, 103789, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_103789_320787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103789 ⟨320787, by decide⟩ :=
  accepted_of_selected 13 103789 ⟨320787, by decide⟩ ⟨13, 2, 0, 320787, 103789, 1393, 16384⟩
    (by decide) selected_cut_12064

theorem selected_cut_12065 : selected 8 ⟨320809, by decide⟩
    (prefixPartial 13 103790) = some ⟨13, 2, 0, 320809, 103790, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_103790_320809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103790 ⟨320809, by decide⟩ :=
  accepted_of_selected 13 103790 ⟨320809, by decide⟩ ⟨13, 2, 0, 320809, 103790, 1853, 16384⟩
    (by decide) selected_cut_12065

theorem selected_cut_12066 : selected 8 ⟨320817, by decide⟩
    (prefixPartial 13 103791) = some ⟨13, 2, 0, 320817, 103791, 949, 16384⟩ := by
  decide +kernel

theorem context_13_103791_320817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103791 ⟨320817, by decide⟩ :=
  accepted_of_selected 13 103791 ⟨320817, by decide⟩ ⟨13, 2, 0, 320817, 103791, 949, 16384⟩
    (by decide) selected_cut_12066

theorem unmarked_context_12_25947_320818 : frontier 9 ⟨320818, by decide⟩
    (prefixCache 12 25947) (prefixPartial 12 25947) = false := by
  decide +kernel

theorem node_context_12_25947_320818 : EJMOriginalGlobalDAGData.nodes 9 ⟨320818, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320787, by decide⟩,⟨320809, by decide⟩,⟨320817, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25947_320818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25947 ⟨320818, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25947
    ⟨320818, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320787, by decide⟩,⟨320809, by decide⟩,⟨320817, by decide⟩]) unmarked_context_12_25947_320818 node_context_12_25947_320818
  intro a
  fin_cases a
  · exact context_13_103788_3444
  · exact context_13_103789_320787
  · exact context_13_103790_320809
  · exact context_13_103791_320817

theorem unmarked_context_11_6486_320819 : frontier 10 ⟨320819, by decide⟩
    (prefixCache 11 6486) (prefixPartial 11 6486) = false := by
  decide +kernel

theorem node_context_11_6486_320819 : EJMOriginalGlobalDAGData.nodes 10 ⟨320819, by decide⟩ =
    .split (coordinate 11) (![⟨320723, by decide⟩,⟨126371, by decide⟩,⟨320769, by decide⟩,⟨320818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6486_320819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6486 ⟨320819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6486
    ⟨320819, by decide⟩ (by decide) (![⟨320723, by decide⟩,⟨126371, by decide⟩,⟨320769, by decide⟩,⟨320818, by decide⟩]) unmarked_context_11_6486_320819 node_context_11_6486_320819
  intro a
  fin_cases a
  · exact context_12_25944_320723
  · exact context_12_25945_126371
  · exact context_12_25946_320769
  · exact context_12_25947_320818

theorem selected_cut_12067 : selected 9 ⟨320863, by decide⟩
    (prefixPartial 12 25948) = some ⟨12, 2, 0, 320863, 25948, 3833, 65536⟩ := by
  decide +kernel

theorem context_12_25948_320863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25948 ⟨320863, by decide⟩ :=
  accepted_of_selected 12 25948 ⟨320863, by decide⟩ ⟨12, 2, 0, 320863, 25948, 3833, 65536⟩
    (by decide) selected_cut_12067

theorem selected_cut_12068 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 25949) = some ⟨12, 1, 0, 320864, 25949, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25949_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25949 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 25949 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 25949, 1, 65536⟩
    (by decide) selected_cut_12068

theorem selected_cut_12069 : selected 9 ⟨320907, by decide⟩
    (prefixPartial 12 25950) = some ⟨12, 2, 0, 320907, 25950, 4009, 65536⟩ := by
  decide +kernel

theorem context_12_25950_320907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25950 ⟨320907, by decide⟩ :=
  accepted_of_selected 12 25950 ⟨320907, by decide⟩ ⟨12, 2, 0, 320907, 25950, 4009, 65536⟩
    (by decide) selected_cut_12069

theorem selected_cut_12070 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103804) = some ⟨13, 1, 0, 3444, 103804, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103804_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103804 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103804 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103804, 1, 16384⟩
    (by decide) selected_cut_12070

theorem selected_cut_12071 : selected 8 ⟨320921, by decide⟩
    (prefixPartial 13 103805) = some ⟨13, 2, 0, 320921, 103805, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_103805_320921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103805 ⟨320921, by decide⟩ :=
  accepted_of_selected 13 103805 ⟨320921, by decide⟩ ⟨13, 2, 0, 320921, 103805, 1301, 16384⟩
    (by decide) selected_cut_12071

theorem selected_cut_12072 : selected 8 ⟨320941, by decide⟩
    (prefixPartial 13 103806) = some ⟨13, 2, 0, 320941, 103806, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_103806_320941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103806 ⟨320941, by decide⟩ :=
  accepted_of_selected 13 103806 ⟨320941, by decide⟩ ⟨13, 2, 0, 320941, 103806, 1837, 16384⟩
    (by decide) selected_cut_12072

theorem selected_cut_12073 : selected 8 ⟨320949, by decide⟩
    (prefixPartial 13 103807) = some ⟨13, 2, 0, 320949, 103807, 969, 16384⟩ := by
  decide +kernel

theorem context_13_103807_320949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103807 ⟨320949, by decide⟩ :=
  accepted_of_selected 13 103807 ⟨320949, by decide⟩ ⟨13, 2, 0, 320949, 103807, 969, 16384⟩
    (by decide) selected_cut_12073

theorem unmarked_context_12_25951_320950 : frontier 9 ⟨320950, by decide⟩
    (prefixCache 12 25951) (prefixPartial 12 25951) = false := by
  decide +kernel

theorem node_context_12_25951_320950 : EJMOriginalGlobalDAGData.nodes 9 ⟨320950, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320921, by decide⟩,⟨320941, by decide⟩,⟨320949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25951_320950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25951 ⟨320950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25951
    ⟨320950, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320921, by decide⟩,⟨320941, by decide⟩,⟨320949, by decide⟩]) unmarked_context_12_25951_320950 node_context_12_25951_320950
  intro a
  fin_cases a
  · exact context_13_103804_3444
  · exact context_13_103805_320921
  · exact context_13_103806_320941
  · exact context_13_103807_320949

theorem unmarked_context_11_6487_320951 : frontier 10 ⟨320951, by decide⟩
    (prefixCache 11 6487) (prefixPartial 11 6487) = false := by
  decide +kernel

theorem node_context_11_6487_320951 : EJMOriginalGlobalDAGData.nodes 10 ⟨320951, by decide⟩ =
    .split (coordinate 11) (![⟨320863, by decide⟩,⟨320864, by decide⟩,⟨320907, by decide⟩,⟨320950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6487_320951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6487 ⟨320951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6487
    ⟨320951, by decide⟩ (by decide) (![⟨320863, by decide⟩,⟨320864, by decide⟩,⟨320907, by decide⟩,⟨320950, by decide⟩]) unmarked_context_11_6487_320951 node_context_11_6487_320951
  intro a
  fin_cases a
  · exact context_12_25948_320863
  · exact context_12_25949_320864
  · exact context_12_25950_320907
  · exact context_12_25951_320950

theorem unmarked_context_10_1621_320952 : frontier 11 ⟨320952, by decide⟩
    (prefixCache 10 1621) (prefixPartial 10 1621) = false := by
  decide +kernel

theorem node_context_10_1621_320952 : EJMOriginalGlobalDAGData.nodes 11 ⟨320952, by decide⟩ =
    .split (coordinate 10) (![⟨320676, by decide⟩,⟨320678, by decide⟩,⟨320819, by decide⟩,⟨320951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1621_320952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1621 ⟨320952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1621
    ⟨320952, by decide⟩ (by decide) (![⟨320676, by decide⟩,⟨320678, by decide⟩,⟨320819, by decide⟩,⟨320951, by decide⟩]) unmarked_context_10_1621_320952 node_context_10_1621_320952
  intro a
  fin_cases a
  · exact context_11_6484_320676
  · exact context_11_6485_320678
  · exact context_11_6486_320819
  · exact context_11_6487_320951

theorem selected_cut_12074 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103808) = some ⟨13, 1, 0, 3444, 103808, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103808_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103808 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103808 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103808, 1, 16384⟩
    (by decide) selected_cut_12074

theorem selected_cut_12075 : selected 8 ⟨320964, by decide⟩
    (prefixPartial 13 103809) = some ⟨13, 2, 0, 320964, 103809, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_103809_320964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103809 ⟨320964, by decide⟩ :=
  accepted_of_selected 13 103809 ⟨320964, by decide⟩ ⟨13, 2, 0, 320964, 103809, 1561, 16384⟩
    (by decide) selected_cut_12075

theorem selected_cut_12076 : selected 8 ⟨320984, by decide⟩
    (prefixPartial 13 103810) = some ⟨13, 2, 0, 320984, 103810, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_103810_320984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103810 ⟨320984, by decide⟩ :=
  accepted_of_selected 13 103810 ⟨320984, by decide⟩ ⟨13, 2, 0, 320984, 103810, 1861, 16384⟩
    (by decide) selected_cut_12076

theorem selected_cut_12077 : selected 8 ⟨320991, by decide⟩
    (prefixPartial 13 103811) = some ⟨13, 2, 0, 320991, 103811, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_103811_320991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103811 ⟨320991, by decide⟩ :=
  accepted_of_selected 13 103811 ⟨320991, by decide⟩ ⟨13, 2, 0, 320991, 103811, 1025, 16384⟩
    (by decide) selected_cut_12077

theorem unmarked_context_12_25952_320992 : frontier 9 ⟨320992, by decide⟩
    (prefixCache 12 25952) (prefixPartial 12 25952) = false := by
  decide +kernel

theorem node_context_12_25952_320992 : EJMOriginalGlobalDAGData.nodes 9 ⟨320992, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨320964, by decide⟩,⟨320984, by decide⟩,⟨320991, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25952_320992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25952 ⟨320992, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25952
    ⟨320992, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨320964, by decide⟩,⟨320984, by decide⟩,⟨320991, by decide⟩]) unmarked_context_12_25952_320992 node_context_12_25952_320992
  intro a
  fin_cases a
  · exact context_13_103808_3444
  · exact context_13_103809_320964
  · exact context_13_103810_320984
  · exact context_13_103811_320991

theorem selected_cut_12078 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103812) = some ⟨13, 1, 0, 3444, 103812, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103812_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103812 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103812 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103812, 1, 16384⟩
    (by decide) selected_cut_12078

theorem selected_cut_12079 : selected 8 ⟨321015, by decide⟩
    (prefixPartial 13 103813) = some ⟨13, 2, 0, 321015, 103813, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_103813_321015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103813 ⟨321015, by decide⟩ :=
  accepted_of_selected 13 103813 ⟨321015, by decide⟩ ⟨13, 2, 0, 321015, 103813, 1865, 16384⟩
    (by decide) selected_cut_12079

theorem selected_cut_12080 : selected 8 ⟨321064, by decide⟩
    (prefixPartial 13 103814) = some ⟨13, 2, 0, 321064, 103814, 2921, 16384⟩ := by
  decide +kernel

theorem context_13_103814_321064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103814 ⟨321064, by decide⟩ :=
  accepted_of_selected 13 103814 ⟨321064, by decide⟩ ⟨13, 2, 0, 321064, 103814, 2921, 16384⟩
    (by decide) selected_cut_12080

theorem selected_cut_12081 : selected 8 ⟨321090, by decide⟩
    (prefixPartial 13 103815) = some ⟨13, 2, 0, 321090, 103815, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_103815_321090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103815 ⟨321090, by decide⟩ :=
  accepted_of_selected 13 103815 ⟨321090, by decide⟩ ⟨13, 2, 0, 321090, 103815, 1461, 16384⟩
    (by decide) selected_cut_12081

theorem unmarked_context_12_25953_321091 : frontier 9 ⟨321091, by decide⟩
    (prefixCache 12 25953) (prefixPartial 12 25953) = false := by
  decide +kernel

theorem node_context_12_25953_321091 : EJMOriginalGlobalDAGData.nodes 9 ⟨321091, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨321015, by decide⟩,⟨321064, by decide⟩,⟨321090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25953_321091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25953 ⟨321091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25953
    ⟨321091, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨321015, by decide⟩,⟨321064, by decide⟩,⟨321090, by decide⟩]) unmarked_context_12_25953_321091 node_context_12_25953_321091
  intro a
  fin_cases a
  · exact context_13_103812_3444
  · exact context_13_103813_321015
  · exact context_13_103814_321064
  · exact context_13_103815_321090

theorem selected_cut_12082 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103816) = some ⟨13, 1, 0, 3444, 103816, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103816_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103816 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103816 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103816, 1, 16384⟩
    (by decide) selected_cut_12082

theorem selected_cut_12083 : selected 8 ⟨321115, by decide⟩
    (prefixPartial 13 103817) = some ⟨13, 2, 0, 321115, 103817, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_103817_321115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103817 ⟨321115, by decide⟩ :=
  accepted_of_selected 13 103817 ⟨321115, by decide⟩ ⟨13, 2, 0, 321115, 103817, 1561, 16384⟩
    (by decide) selected_cut_12083

theorem selected_cut_12084 : selected 8 ⟨321143, by decide⟩
    (prefixPartial 13 103818) = some ⟨13, 2, 0, 321143, 103818, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_103818_321143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103818 ⟨321143, by decide⟩ :=
  accepted_of_selected 13 103818 ⟨321143, by decide⟩ ⟨13, 2, 0, 321143, 103818, 2205, 16384⟩
    (by decide) selected_cut_12084

theorem selected_cut_12085 : selected 8 ⟨321151, by decide⟩
    (prefixPartial 13 103819) = some ⟨13, 2, 0, 321151, 103819, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_103819_321151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103819 ⟨321151, by decide⟩ :=
  accepted_of_selected 13 103819 ⟨321151, by decide⟩ ⟨13, 2, 0, 321151, 103819, 1113, 16384⟩
    (by decide) selected_cut_12085

theorem unmarked_context_12_25954_321152 : frontier 9 ⟨321152, by decide⟩
    (prefixCache 12 25954) (prefixPartial 12 25954) = false := by
  decide +kernel

theorem node_context_12_25954_321152 : EJMOriginalGlobalDAGData.nodes 9 ⟨321152, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨321115, by decide⟩,⟨321143, by decide⟩,⟨321151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25954_321152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25954 ⟨321152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25954
    ⟨321152, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨321115, by decide⟩,⟨321143, by decide⟩,⟨321151, by decide⟩]) unmarked_context_12_25954_321152 node_context_12_25954_321152
  intro a
  fin_cases a
  · exact context_13_103816_3444
  · exact context_13_103817_321115
  · exact context_13_103818_321143
  · exact context_13_103819_321151

theorem selected_cut_12086 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103820) = some ⟨13, 1, 0, 3444, 103820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103820, 1, 16384⟩
    (by decide) selected_cut_12086

theorem selected_cut_12087 : selected 8 ⟨321171, by decide⟩
    (prefixPartial 13 103821) = some ⟨13, 2, 0, 321171, 103821, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_103821_321171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103821 ⟨321171, by decide⟩ :=
  accepted_of_selected 13 103821 ⟨321171, by decide⟩ ⟨13, 2, 0, 321171, 103821, 1617, 16384⟩
    (by decide) selected_cut_12087

theorem selected_cut_12088 : selected 8 ⟨321198, by decide⟩
    (prefixPartial 13 103822) = some ⟨13, 2, 0, 321198, 103822, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_103822_321198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103822 ⟨321198, by decide⟩ :=
  accepted_of_selected 13 103822 ⟨321198, by decide⟩ ⟨13, 2, 0, 321198, 103822, 2377, 16384⟩
    (by decide) selected_cut_12088

theorem selected_cut_12089 : selected 8 ⟨321206, by decide⟩
    (prefixPartial 13 103823) = some ⟨13, 2, 0, 321206, 103823, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_103823_321206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103823 ⟨321206, by decide⟩ :=
  accepted_of_selected 13 103823 ⟨321206, by decide⟩ ⟨13, 2, 0, 321206, 103823, 1077, 16384⟩
    (by decide) selected_cut_12089

theorem unmarked_context_12_25955_321207 : frontier 9 ⟨321207, by decide⟩
    (prefixCache 12 25955) (prefixPartial 12 25955) = false := by
  decide +kernel

theorem node_context_12_25955_321207 : EJMOriginalGlobalDAGData.nodes 9 ⟨321207, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨321171, by decide⟩,⟨321198, by decide⟩,⟨321206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25955_321207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25955 ⟨321207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25955
    ⟨321207, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨321171, by decide⟩,⟨321198, by decide⟩,⟨321206, by decide⟩]) unmarked_context_12_25955_321207 node_context_12_25955_321207
  intro a
  fin_cases a
  · exact context_13_103820_3444
  · exact context_13_103821_321171
  · exact context_13_103822_321198
  · exact context_13_103823_321206

theorem unmarked_context_11_6488_321208 : frontier 10 ⟨321208, by decide⟩
    (prefixCache 11 6488) (prefixPartial 11 6488) = false := by
  decide +kernel

theorem node_context_11_6488_321208 : EJMOriginalGlobalDAGData.nodes 10 ⟨321208, by decide⟩ =
    .split (coordinate 11) (![⟨320992, by decide⟩,⟨321091, by decide⟩,⟨321152, by decide⟩,⟨321207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6488_321208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6488 ⟨321208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6488
    ⟨321208, by decide⟩ (by decide) (![⟨320992, by decide⟩,⟨321091, by decide⟩,⟨321152, by decide⟩,⟨321207, by decide⟩]) unmarked_context_11_6488_321208 node_context_11_6488_321208
  intro a
  fin_cases a
  · exact context_12_25952_320992
  · exact context_12_25953_321091
  · exact context_12_25954_321152
  · exact context_12_25955_321207

theorem selected_cut_12090 : selected 9 ⟨321243, by decide⟩
    (prefixPartial 12 25956) = some ⟨12, 2, 0, 321243, 25956, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_25956_321243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25956 ⟨321243, by decide⟩ :=
  accepted_of_selected 12 25956 ⟨321243, by decide⟩ ⟨12, 2, 0, 321243, 25956, 3121, 65536⟩
    (by decide) selected_cut_12090

theorem selected_cut_12091 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 25957) = some ⟨12, 1, 0, 126884, 25957, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25957_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25957 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 25957 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 25957, 1, 65536⟩
    (by decide) selected_cut_12091

theorem selected_cut_12092 : selected 9 ⟨321284, by decide⟩
    (prefixPartial 12 25958) = some ⟨12, 2, 0, 321284, 25958, 3421, 65536⟩ := by
  decide +kernel

theorem context_12_25958_321284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25958 ⟨321284, by decide⟩ :=
  accepted_of_selected 12 25958 ⟨321284, by decide⟩ ⟨12, 2, 0, 321284, 25958, 3421, 65536⟩
    (by decide) selected_cut_12092

theorem selected_cut_12093 : selected 9 ⟨321329, by decide⟩
    (prefixPartial 12 25959) = some ⟨12, 2, 0, 321329, 25959, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_25959_321329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25959 ⟨321329, by decide⟩ :=
  accepted_of_selected 12 25959 ⟨321329, by decide⟩ ⟨12, 2, 0, 321329, 25959, 3821, 65536⟩
    (by decide) selected_cut_12093

theorem unmarked_context_11_6489_321330 : frontier 10 ⟨321330, by decide⟩
    (prefixCache 11 6489) (prefixPartial 11 6489) = false := by
  decide +kernel

theorem node_context_11_6489_321330 : EJMOriginalGlobalDAGData.nodes 10 ⟨321330, by decide⟩ =
    .split (coordinate 11) (![⟨321243, by decide⟩,⟨126884, by decide⟩,⟨321284, by decide⟩,⟨321329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6489_321330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6489 ⟨321330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6489
    ⟨321330, by decide⟩ (by decide) (![⟨321243, by decide⟩,⟨126884, by decide⟩,⟨321284, by decide⟩,⟨321329, by decide⟩]) unmarked_context_11_6489_321330 node_context_11_6489_321330
  intro a
  fin_cases a
  · exact context_12_25956_321243
  · exact context_12_25957_126884
  · exact context_12_25958_321284
  · exact context_12_25959_321329

theorem selected_cut_12094 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103840) = some ⟨13, 1, 0, 3444, 103840, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103840_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103840 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103840 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103840, 1, 16384⟩
    (by decide) selected_cut_12094

theorem selected_cut_12095 : selected 8 ⟨321341, by decide⟩
    (prefixPartial 13 103841) = some ⟨13, 2, 0, 321341, 103841, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_103841_321341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103841 ⟨321341, by decide⟩ :=
  accepted_of_selected 13 103841 ⟨321341, by decide⟩ ⟨13, 2, 0, 321341, 103841, 1037, 16384⟩
    (by decide) selected_cut_12095

theorem selected_cut_12096 : selected 8 ⟨321363, by decide⟩
    (prefixPartial 13 103842) = some ⟨13, 2, 0, 321363, 103842, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_103842_321363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103842 ⟨321363, by decide⟩ :=
  accepted_of_selected 13 103842 ⟨321363, by decide⟩ ⟨13, 2, 0, 321363, 103842, 2097, 16384⟩
    (by decide) selected_cut_12096

theorem selected_cut_12097 : selected 8 ⟨321372, by decide⟩
    (prefixPartial 13 103843) = some ⟨13, 2, 0, 321372, 103843, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_103843_321372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103843 ⟨321372, by decide⟩ :=
  accepted_of_selected 13 103843 ⟨321372, by decide⟩ ⟨13, 2, 0, 321372, 103843, 1017, 16384⟩
    (by decide) selected_cut_12097

theorem unmarked_context_12_25960_321373 : frontier 9 ⟨321373, by decide⟩
    (prefixCache 12 25960) (prefixPartial 12 25960) = false := by
  decide +kernel

theorem node_context_12_25960_321373 : EJMOriginalGlobalDAGData.nodes 9 ⟨321373, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨321341, by decide⟩,⟨321363, by decide⟩,⟨321372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25960_321373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25960 ⟨321373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25960
    ⟨321373, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨321341, by decide⟩,⟨321363, by decide⟩,⟨321372, by decide⟩]) unmarked_context_12_25960_321373 node_context_12_25960_321373
  intro a
  fin_cases a
  · exact context_13_103840_3444
  · exact context_13_103841_321341
  · exact context_13_103842_321363
  · exact context_13_103843_321372

theorem selected_cut_12098 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 103844) = some ⟨13, 1, 0, 3444, 103844, 1, 16384⟩ := by
  decide +kernel

theorem context_13_103844_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 103844 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 103844 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 103844, 1, 16384⟩
    (by decide) selected_cut_12098

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
