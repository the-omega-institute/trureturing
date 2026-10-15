/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover158
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_15267 : selected 8 ⟨392601, by decide⟩
    (prefixPartial 13 110748) = some ⟨13, 2, 0, 392601, 110748, 957, 16384⟩ := by
  decide +kernel

theorem context_13_110748_392601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110748 ⟨392601, by decide⟩ :=
  accepted_of_selected 13 110748 ⟨392601, by decide⟩ ⟨13, 2, 0, 392601, 110748, 957, 16384⟩
    (by decide) selected_cut_15267

theorem selected_cut_15268 : selected 8 ⟨392629, by decide⟩
    (prefixPartial 13 110749) = some ⟨13, 2, 0, 392629, 110749, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_110749_392629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110749 ⟨392629, by decide⟩ :=
  accepted_of_selected 13 110749 ⟨392629, by decide⟩ ⟨13, 2, 0, 392629, 110749, 2161, 16384⟩
    (by decide) selected_cut_15268

theorem selected_cut_15269 : selected 8 ⟨392648, by decide⟩
    (prefixPartial 13 110750) = some ⟨13, 2, 0, 392648, 110750, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_110750_392648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110750 ⟨392648, by decide⟩ :=
  accepted_of_selected 13 110750 ⟨392648, by decide⟩ ⟨13, 2, 0, 392648, 110750, 1441, 16384⟩
    (by decide) selected_cut_15269

theorem selected_cut_15270 : selected 8 ⟨392658, by decide⟩
    (prefixPartial 13 110751) = some ⟨13, 2, 0, 392658, 110751, 925, 16384⟩ := by
  decide +kernel

theorem context_13_110751_392658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110751 ⟨392658, by decide⟩ :=
  accepted_of_selected 13 110751 ⟨392658, by decide⟩ ⟨13, 2, 0, 392658, 110751, 925, 16384⟩
    (by decide) selected_cut_15270

theorem unmarked_context_12_27687_392659 : frontier 9 ⟨392659, by decide⟩
    (prefixCache 12 27687) (prefixPartial 12 27687) = false := by
  decide +kernel

theorem node_context_12_27687_392659 : EJMOriginalGlobalDAGData.nodes 9 ⟨392659, by decide⟩ =
    .split (coordinate 12) (![⟨392601, by decide⟩,⟨392629, by decide⟩,⟨392648, by decide⟩,⟨392658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27687_392659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27687 ⟨392659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27687
    ⟨392659, by decide⟩ (by decide) (![⟨392601, by decide⟩,⟨392629, by decide⟩,⟨392648, by decide⟩,⟨392658, by decide⟩]) unmarked_context_12_27687_392659 node_context_12_27687_392659
  intro a
  fin_cases a
  · exact context_13_110748_392601
  · exact context_13_110749_392629
  · exact context_13_110750_392648
  · exact context_13_110751_392658

theorem unmarked_context_11_6921_392660 : frontier 10 ⟨392660, by decide⟩
    (prefixCache 11 6921) (prefixPartial 11 6921) = false := by
  decide +kernel

theorem node_context_11_6921_392660 : EJMOriginalGlobalDAGData.nodes 10 ⟨392660, by decide⟩ =
    .split (coordinate 11) (![⟨392462, by decide⟩,⟨392524, by decide⟩,⟨392586, by decide⟩,⟨392659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6921_392660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6921 ⟨392660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6921
    ⟨392660, by decide⟩ (by decide) (![⟨392462, by decide⟩,⟨392524, by decide⟩,⟨392586, by decide⟩,⟨392659, by decide⟩]) unmarked_context_11_6921_392660 node_context_11_6921_392660
  intro a
  fin_cases a
  · exact context_12_27684_392462
  · exact context_12_27685_392524
  · exact context_12_27686_392586
  · exact context_12_27687_392659

theorem selected_cut_15271 : selected 8 ⟨392668, by decide⟩
    (prefixPartial 13 110752) = some ⟨13, 2, 0, 392668, 110752, 593, 16384⟩ := by
  decide +kernel

theorem context_13_110752_392668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110752 ⟨392668, by decide⟩ :=
  accepted_of_selected 13 110752 ⟨392668, by decide⟩ ⟨13, 2, 0, 392668, 110752, 593, 16384⟩
    (by decide) selected_cut_15271

theorem selected_cut_15272 : selected 8 ⟨392696, by decide⟩
    (prefixPartial 13 110753) = some ⟨13, 2, 0, 392696, 110753, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_110753_392696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110753 ⟨392696, by decide⟩ :=
  accepted_of_selected 13 110753 ⟨392696, by decide⟩ ⟨13, 2, 0, 392696, 110753, 1957, 16384⟩
    (by decide) selected_cut_15272

theorem selected_cut_15273 : selected 8 ⟨392714, by decide⟩
    (prefixPartial 13 110754) = some ⟨13, 2, 0, 392714, 110754, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_110754_392714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110754 ⟨392714, by decide⟩ :=
  accepted_of_selected 13 110754 ⟨392714, by decide⟩ ⟨13, 2, 0, 392714, 110754, 1297, 16384⟩
    (by decide) selected_cut_15273

theorem selected_cut_15274 : selected 8 ⟨392724, by decide⟩
    (prefixPartial 13 110755) = some ⟨13, 2, 0, 392724, 110755, 717, 16384⟩ := by
  decide +kernel

theorem context_13_110755_392724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110755 ⟨392724, by decide⟩ :=
  accepted_of_selected 13 110755 ⟨392724, by decide⟩ ⟨13, 2, 0, 392724, 110755, 717, 16384⟩
    (by decide) selected_cut_15274

theorem unmarked_context_12_27688_392725 : frontier 9 ⟨392725, by decide⟩
    (prefixCache 12 27688) (prefixPartial 12 27688) = false := by
  decide +kernel

theorem node_context_12_27688_392725 : EJMOriginalGlobalDAGData.nodes 9 ⟨392725, by decide⟩ =
    .split (coordinate 12) (![⟨392668, by decide⟩,⟨392696, by decide⟩,⟨392714, by decide⟩,⟨392724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27688_392725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27688 ⟨392725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27688
    ⟨392725, by decide⟩ (by decide) (![⟨392668, by decide⟩,⟨392696, by decide⟩,⟨392714, by decide⟩,⟨392724, by decide⟩]) unmarked_context_12_27688_392725 node_context_12_27688_392725
  intro a
  fin_cases a
  · exact context_13_110752_392668
  · exact context_13_110753_392696
  · exact context_13_110754_392714
  · exact context_13_110755_392724

theorem selected_cut_15275 : selected 8 ⟨392736, by decide⟩
    (prefixPartial 13 110756) = some ⟨13, 2, 0, 392736, 110756, 745, 16384⟩ := by
  decide +kernel

theorem context_13_110756_392736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110756 ⟨392736, by decide⟩ :=
  accepted_of_selected 13 110756 ⟨392736, by decide⟩ ⟨13, 2, 0, 392736, 110756, 745, 16384⟩
    (by decide) selected_cut_15275

theorem selected_cut_15276 : selected 8 ⟨392763, by decide⟩
    (prefixPartial 13 110757) = some ⟨13, 2, 0, 392763, 110757, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_110757_392763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110757 ⟨392763, by decide⟩ :=
  accepted_of_selected 13 110757 ⟨392763, by decide⟩ ⟨13, 2, 0, 392763, 110757, 1913, 16384⟩
    (by decide) selected_cut_15276

theorem selected_cut_15277 : selected 8 ⟨392783, by decide⟩
    (prefixPartial 13 110758) = some ⟨13, 2, 0, 392783, 110758, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_110758_392783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110758 ⟨392783, by decide⟩ :=
  accepted_of_selected 13 110758 ⟨392783, by decide⟩ ⟨13, 2, 0, 392783, 110758, 1365, 16384⟩
    (by decide) selected_cut_15277

theorem selected_cut_15278 : selected 8 ⟨392793, by decide⟩
    (prefixPartial 13 110759) = some ⟨13, 2, 0, 392793, 110759, 825, 16384⟩ := by
  decide +kernel

theorem context_13_110759_392793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110759 ⟨392793, by decide⟩ :=
  accepted_of_selected 13 110759 ⟨392793, by decide⟩ ⟨13, 2, 0, 392793, 110759, 825, 16384⟩
    (by decide) selected_cut_15278

theorem unmarked_context_12_27689_392794 : frontier 9 ⟨392794, by decide⟩
    (prefixCache 12 27689) (prefixPartial 12 27689) = false := by
  decide +kernel

theorem node_context_12_27689_392794 : EJMOriginalGlobalDAGData.nodes 9 ⟨392794, by decide⟩ =
    .split (coordinate 12) (![⟨392736, by decide⟩,⟨392763, by decide⟩,⟨392783, by decide⟩,⟨392793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27689_392794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27689 ⟨392794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27689
    ⟨392794, by decide⟩ (by decide) (![⟨392736, by decide⟩,⟨392763, by decide⟩,⟨392783, by decide⟩,⟨392793, by decide⟩]) unmarked_context_12_27689_392794 node_context_12_27689_392794
  intro a
  fin_cases a
  · exact context_13_110756_392736
  · exact context_13_110757_392763
  · exact context_13_110758_392783
  · exact context_13_110759_392793

theorem selected_cut_15279 : selected 8 ⟨392803, by decide⟩
    (prefixPartial 13 110760) = some ⟨13, 2, 0, 392803, 110760, 633, 16384⟩ := by
  decide +kernel

theorem context_13_110760_392803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110760 ⟨392803, by decide⟩ :=
  accepted_of_selected 13 110760 ⟨392803, by decide⟩ ⟨13, 2, 0, 392803, 110760, 633, 16384⟩
    (by decide) selected_cut_15279

theorem selected_cut_15280 : selected 8 ⟨392833, by decide⟩
    (prefixPartial 13 110761) = some ⟨13, 2, 0, 392833, 110761, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_110761_392833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110761 ⟨392833, by decide⟩ :=
  accepted_of_selected 13 110761 ⟨392833, by decide⟩ ⟨13, 2, 0, 392833, 110761, 2073, 16384⟩
    (by decide) selected_cut_15280

theorem selected_cut_15281 : selected 8 ⟨392844, by decide⟩
    (prefixPartial 13 110762) = some ⟨13, 2, 0, 392844, 110762, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_110762_392844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110762 ⟨392844, by decide⟩ :=
  accepted_of_selected 13 110762 ⟨392844, by decide⟩ ⟨13, 2, 0, 392844, 110762, 1113, 16384⟩
    (by decide) selected_cut_15281

theorem selected_cut_15282 : selected 8 ⟨392853, by decide⟩
    (prefixPartial 13 110763) = some ⟨13, 2, 0, 392853, 110763, 861, 16384⟩ := by
  decide +kernel

theorem context_13_110763_392853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110763 ⟨392853, by decide⟩ :=
  accepted_of_selected 13 110763 ⟨392853, by decide⟩ ⟨13, 2, 0, 392853, 110763, 861, 16384⟩
    (by decide) selected_cut_15282

theorem unmarked_context_12_27690_392854 : frontier 9 ⟨392854, by decide⟩
    (prefixCache 12 27690) (prefixPartial 12 27690) = false := by
  decide +kernel

theorem node_context_12_27690_392854 : EJMOriginalGlobalDAGData.nodes 9 ⟨392854, by decide⟩ =
    .split (coordinate 12) (![⟨392803, by decide⟩,⟨392833, by decide⟩,⟨392844, by decide⟩,⟨392853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27690_392854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27690 ⟨392854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27690
    ⟨392854, by decide⟩ (by decide) (![⟨392803, by decide⟩,⟨392833, by decide⟩,⟨392844, by decide⟩,⟨392853, by decide⟩]) unmarked_context_12_27690_392854 node_context_12_27690_392854
  intro a
  fin_cases a
  · exact context_13_110760_392803
  · exact context_13_110761_392833
  · exact context_13_110762_392844
  · exact context_13_110763_392853

theorem selected_cut_15283 : selected 8 ⟨392863, by decide⟩
    (prefixPartial 13 110764) = some ⟨13, 2, 0, 392863, 110764, 729, 16384⟩ := by
  decide +kernel

theorem context_13_110764_392863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110764 ⟨392863, by decide⟩ :=
  accepted_of_selected 13 110764 ⟨392863, by decide⟩ ⟨13, 2, 0, 392863, 110764, 729, 16384⟩
    (by decide) selected_cut_15283

theorem selected_cut_15284 : selected 8 ⟨392897, by decide⟩
    (prefixPartial 13 110765) = some ⟨13, 2, 0, 392897, 110765, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_110765_392897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110765 ⟨392897, by decide⟩ :=
  accepted_of_selected 13 110765 ⟨392897, by decide⟩ ⟨13, 2, 0, 392897, 110765, 2317, 16384⟩
    (by decide) selected_cut_15284

theorem selected_cut_15285 : selected 8 ⟨392915, by decide⟩
    (prefixPartial 13 110766) = some ⟨13, 2, 0, 392915, 110766, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_110766_392915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110766 ⟨392915, by decide⟩ :=
  accepted_of_selected 13 110766 ⟨392915, by decide⟩ ⟨13, 2, 0, 392915, 110766, 1321, 16384⟩
    (by decide) selected_cut_15285

theorem selected_cut_15286 : selected 8 ⟨392924, by decide⟩
    (prefixPartial 13 110767) = some ⟨13, 2, 0, 392924, 110767, 921, 16384⟩ := by
  decide +kernel

theorem context_13_110767_392924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110767 ⟨392924, by decide⟩ :=
  accepted_of_selected 13 110767 ⟨392924, by decide⟩ ⟨13, 2, 0, 392924, 110767, 921, 16384⟩
    (by decide) selected_cut_15286

theorem unmarked_context_12_27691_392925 : frontier 9 ⟨392925, by decide⟩
    (prefixCache 12 27691) (prefixPartial 12 27691) = false := by
  decide +kernel

theorem node_context_12_27691_392925 : EJMOriginalGlobalDAGData.nodes 9 ⟨392925, by decide⟩ =
    .split (coordinate 12) (![⟨392863, by decide⟩,⟨392897, by decide⟩,⟨392915, by decide⟩,⟨392924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27691_392925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27691 ⟨392925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27691
    ⟨392925, by decide⟩ (by decide) (![⟨392863, by decide⟩,⟨392897, by decide⟩,⟨392915, by decide⟩,⟨392924, by decide⟩]) unmarked_context_12_27691_392925 node_context_12_27691_392925
  intro a
  fin_cases a
  · exact context_13_110764_392863
  · exact context_13_110765_392897
  · exact context_13_110766_392915
  · exact context_13_110767_392924

theorem unmarked_context_11_6922_392926 : frontier 10 ⟨392926, by decide⟩
    (prefixCache 11 6922) (prefixPartial 11 6922) = false := by
  decide +kernel

theorem node_context_11_6922_392926 : EJMOriginalGlobalDAGData.nodes 10 ⟨392926, by decide⟩ =
    .split (coordinate 11) (![⟨392725, by decide⟩,⟨392794, by decide⟩,⟨392854, by decide⟩,⟨392925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6922_392926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6922 ⟨392926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6922
    ⟨392926, by decide⟩ (by decide) (![⟨392725, by decide⟩,⟨392794, by decide⟩,⟨392854, by decide⟩,⟨392925, by decide⟩]) unmarked_context_11_6922_392926 node_context_11_6922_392926
  intro a
  fin_cases a
  · exact context_12_27688_392725
  · exact context_12_27689_392794
  · exact context_12_27690_392854
  · exact context_12_27691_392925

theorem selected_cut_15287 : selected 8 ⟨392935, by decide⟩
    (prefixPartial 13 110768) = some ⟨13, 2, 0, 392935, 110768, 537, 16384⟩ := by
  decide +kernel

theorem context_13_110768_392935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110768 ⟨392935, by decide⟩ :=
  accepted_of_selected 13 110768 ⟨392935, by decide⟩ ⟨13, 2, 0, 392935, 110768, 537, 16384⟩
    (by decide) selected_cut_15287

theorem selected_cut_15288 : selected 8 ⟨392964, by decide⟩
    (prefixPartial 13 110769) = some ⟨13, 2, 0, 392964, 110769, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_110769_392964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110769 ⟨392964, by decide⟩ :=
  accepted_of_selected 13 110769 ⟨392964, by decide⟩ ⟨13, 2, 0, 392964, 110769, 1989, 16384⟩
    (by decide) selected_cut_15288

theorem selected_cut_15289 : selected 8 ⟨392977, by decide⟩
    (prefixPartial 13 110770) = some ⟨13, 2, 0, 392977, 110770, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_110770_392977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110770 ⟨392977, by decide⟩ :=
  accepted_of_selected 13 110770 ⟨392977, by decide⟩ ⟨13, 2, 0, 392977, 110770, 1173, 16384⟩
    (by decide) selected_cut_15289

theorem selected_cut_15290 : selected 8 ⟨392983, by decide⟩
    (prefixPartial 13 110771) = some ⟨13, 2, 0, 392983, 110771, 713, 16384⟩ := by
  decide +kernel

theorem context_13_110771_392983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110771 ⟨392983, by decide⟩ :=
  accepted_of_selected 13 110771 ⟨392983, by decide⟩ ⟨13, 2, 0, 392983, 110771, 713, 16384⟩
    (by decide) selected_cut_15290

theorem unmarked_context_12_27692_392984 : frontier 9 ⟨392984, by decide⟩
    (prefixCache 12 27692) (prefixPartial 12 27692) = false := by
  decide +kernel

theorem node_context_12_27692_392984 : EJMOriginalGlobalDAGData.nodes 9 ⟨392984, by decide⟩ =
    .split (coordinate 12) (![⟨392935, by decide⟩,⟨392964, by decide⟩,⟨392977, by decide⟩,⟨392983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27692_392984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27692 ⟨392984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27692
    ⟨392984, by decide⟩ (by decide) (![⟨392935, by decide⟩,⟨392964, by decide⟩,⟨392977, by decide⟩,⟨392983, by decide⟩]) unmarked_context_12_27692_392984 node_context_12_27692_392984
  intro a
  fin_cases a
  · exact context_13_110768_392935
  · exact context_13_110769_392964
  · exact context_13_110770_392977
  · exact context_13_110771_392983

theorem selected_cut_15291 : selected 8 ⟨392993, by decide⟩
    (prefixPartial 13 110772) = some ⟨13, 2, 0, 392993, 110772, 649, 16384⟩ := by
  decide +kernel

theorem context_13_110772_392993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110772 ⟨392993, by decide⟩ :=
  accepted_of_selected 13 110772 ⟨392993, by decide⟩ ⟨13, 2, 0, 392993, 110772, 649, 16384⟩
    (by decide) selected_cut_15291

theorem selected_cut_15292 : selected 8 ⟨393018, by decide⟩
    (prefixPartial 13 110773) = some ⟨13, 2, 0, 393018, 110773, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_110773_393018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110773 ⟨393018, by decide⟩ :=
  accepted_of_selected 13 110773 ⟨393018, by decide⟩ ⟨13, 2, 0, 393018, 110773, 2021, 16384⟩
    (by decide) selected_cut_15292

theorem selected_cut_15293 : selected 8 ⟨393038, by decide⟩
    (prefixPartial 13 110774) = some ⟨13, 2, 0, 393038, 110774, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_110774_393038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110774 ⟨393038, by decide⟩ :=
  accepted_of_selected 13 110774 ⟨393038, by decide⟩ ⟨13, 2, 0, 393038, 110774, 1413, 16384⟩
    (by decide) selected_cut_15293

theorem selected_cut_15294 : selected 8 ⟨393046, by decide⟩
    (prefixPartial 13 110775) = some ⟨13, 2, 0, 393046, 110775, 825, 16384⟩ := by
  decide +kernel

theorem context_13_110775_393046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110775 ⟨393046, by decide⟩ :=
  accepted_of_selected 13 110775 ⟨393046, by decide⟩ ⟨13, 2, 0, 393046, 110775, 825, 16384⟩
    (by decide) selected_cut_15294

theorem unmarked_context_12_27693_393047 : frontier 9 ⟨393047, by decide⟩
    (prefixCache 12 27693) (prefixPartial 12 27693) = false := by
  decide +kernel

theorem node_context_12_27693_393047 : EJMOriginalGlobalDAGData.nodes 9 ⟨393047, by decide⟩ =
    .split (coordinate 12) (![⟨392993, by decide⟩,⟨393018, by decide⟩,⟨393038, by decide⟩,⟨393046, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27693_393047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27693 ⟨393047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27693
    ⟨393047, by decide⟩ (by decide) (![⟨392993, by decide⟩,⟨393018, by decide⟩,⟨393038, by decide⟩,⟨393046, by decide⟩]) unmarked_context_12_27693_393047 node_context_12_27693_393047
  intro a
  fin_cases a
  · exact context_13_110772_392993
  · exact context_13_110773_393018
  · exact context_13_110774_393038
  · exact context_13_110775_393046

theorem selected_cut_15295 : selected 8 ⟨393057, by decide⟩
    (prefixPartial 13 110776) = some ⟨13, 2, 0, 393057, 110776, 529, 16384⟩ := by
  decide +kernel

theorem context_13_110776_393057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110776 ⟨393057, by decide⟩ :=
  accepted_of_selected 13 110776 ⟨393057, by decide⟩ ⟨13, 2, 0, 393057, 110776, 529, 16384⟩
    (by decide) selected_cut_15295

theorem selected_cut_15296 : selected 8 ⟨393081, by decide⟩
    (prefixPartial 13 110777) = some ⟨13, 2, 0, 393081, 110777, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_110777_393081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110777 ⟨393081, by decide⟩ :=
  accepted_of_selected 13 110777 ⟨393081, by decide⟩ ⟨13, 2, 0, 393081, 110777, 2337, 16384⟩
    (by decide) selected_cut_15296

theorem selected_cut_15297 : selected 8 ⟨393097, by decide⟩
    (prefixPartial 13 110778) = some ⟨13, 2, 0, 393097, 110778, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_110778_393097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110778 ⟨393097, by decide⟩ :=
  accepted_of_selected 13 110778 ⟨393097, by decide⟩ ⟨13, 2, 0, 393097, 110778, 1277, 16384⟩
    (by decide) selected_cut_15297

theorem selected_cut_15298 : selected 8 ⟨393105, by decide⟩
    (prefixPartial 13 110779) = some ⟨13, 2, 0, 393105, 110779, 849, 16384⟩ := by
  decide +kernel

theorem context_13_110779_393105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110779 ⟨393105, by decide⟩ :=
  accepted_of_selected 13 110779 ⟨393105, by decide⟩ ⟨13, 2, 0, 393105, 110779, 849, 16384⟩
    (by decide) selected_cut_15298

theorem unmarked_context_12_27694_393106 : frontier 9 ⟨393106, by decide⟩
    (prefixCache 12 27694) (prefixPartial 12 27694) = false := by
  decide +kernel

theorem node_context_12_27694_393106 : EJMOriginalGlobalDAGData.nodes 9 ⟨393106, by decide⟩ =
    .split (coordinate 12) (![⟨393057, by decide⟩,⟨393081, by decide⟩,⟨393097, by decide⟩,⟨393105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27694_393106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27694 ⟨393106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27694
    ⟨393106, by decide⟩ (by decide) (![⟨393057, by decide⟩,⟨393081, by decide⟩,⟨393097, by decide⟩,⟨393105, by decide⟩]) unmarked_context_12_27694_393106 node_context_12_27694_393106
  intro a
  fin_cases a
  · exact context_13_110776_393057
  · exact context_13_110777_393081
  · exact context_13_110778_393097
  · exact context_13_110779_393105

theorem selected_cut_15299 : selected 8 ⟨393119, by decide⟩
    (prefixPartial 13 110780) = some ⟨13, 2, 0, 393119, 110780, 517, 16384⟩ := by
  decide +kernel

theorem context_13_110780_393119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110780 ⟨393119, by decide⟩ :=
  accepted_of_selected 13 110780 ⟨393119, by decide⟩ ⟨13, 2, 0, 393119, 110780, 517, 16384⟩
    (by decide) selected_cut_15299

theorem selected_cut_15300 : selected 8 ⟨393152, by decide⟩
    (prefixPartial 13 110781) = some ⟨13, 2, 0, 393152, 110781, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_110781_393152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110781 ⟨393152, by decide⟩ :=
  accepted_of_selected 13 110781 ⟨393152, by decide⟩ ⟨13, 2, 0, 393152, 110781, 2353, 16384⟩
    (by decide) selected_cut_15300

theorem selected_cut_15301 : selected 8 ⟨393167, by decide⟩
    (prefixPartial 13 110782) = some ⟨13, 2, 0, 393167, 110782, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_110782_393167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110782 ⟨393167, by decide⟩ :=
  accepted_of_selected 13 110782 ⟨393167, by decide⟩ ⟨13, 2, 0, 393167, 110782, 1393, 16384⟩
    (by decide) selected_cut_15301

theorem selected_cut_15302 : selected 8 ⟨393176, by decide⟩
    (prefixPartial 13 110783) = some ⟨13, 2, 0, 393176, 110783, 909, 16384⟩ := by
  decide +kernel

theorem context_13_110783_393176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110783 ⟨393176, by decide⟩ :=
  accepted_of_selected 13 110783 ⟨393176, by decide⟩ ⟨13, 2, 0, 393176, 110783, 909, 16384⟩
    (by decide) selected_cut_15302

theorem unmarked_context_12_27695_393177 : frontier 9 ⟨393177, by decide⟩
    (prefixCache 12 27695) (prefixPartial 12 27695) = false := by
  decide +kernel

theorem node_context_12_27695_393177 : EJMOriginalGlobalDAGData.nodes 9 ⟨393177, by decide⟩ =
    .split (coordinate 12) (![⟨393119, by decide⟩,⟨393152, by decide⟩,⟨393167, by decide⟩,⟨393176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27695_393177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27695 ⟨393177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27695
    ⟨393177, by decide⟩ (by decide) (![⟨393119, by decide⟩,⟨393152, by decide⟩,⟨393167, by decide⟩,⟨393176, by decide⟩]) unmarked_context_12_27695_393177 node_context_12_27695_393177
  intro a
  fin_cases a
  · exact context_13_110780_393119
  · exact context_13_110781_393152
  · exact context_13_110782_393167
  · exact context_13_110783_393176

theorem unmarked_context_11_6923_393178 : frontier 10 ⟨393178, by decide⟩
    (prefixCache 11 6923) (prefixPartial 11 6923) = false := by
  decide +kernel

theorem node_context_11_6923_393178 : EJMOriginalGlobalDAGData.nodes 10 ⟨393178, by decide⟩ =
    .split (coordinate 11) (![⟨392984, by decide⟩,⟨393047, by decide⟩,⟨393106, by decide⟩,⟨393177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6923_393178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6923 ⟨393178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6923
    ⟨393178, by decide⟩ (by decide) (![⟨392984, by decide⟩,⟨393047, by decide⟩,⟨393106, by decide⟩,⟨393177, by decide⟩]) unmarked_context_11_6923_393178 node_context_11_6923_393178
  intro a
  fin_cases a
  · exact context_12_27692_392984
  · exact context_12_27693_393047
  · exact context_12_27694_393106
  · exact context_12_27695_393177

theorem unmarked_context_10_1730_393179 : frontier 11 ⟨393179, by decide⟩
    (prefixCache 10 1730) (prefixPartial 10 1730) = false := by
  decide +kernel

theorem node_context_10_1730_393179 : EJMOriginalGlobalDAGData.nodes 11 ⟨393179, by decide⟩ =
    .split (coordinate 10) (![⟨392404, by decide⟩,⟨392660, by decide⟩,⟨392926, by decide⟩,⟨393178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1730_393179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1730 ⟨393179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1730
    ⟨393179, by decide⟩ (by decide) (![⟨392404, by decide⟩,⟨392660, by decide⟩,⟨392926, by decide⟩,⟨393178, by decide⟩]) unmarked_context_10_1730_393179 node_context_10_1730_393179
  intro a
  fin_cases a
  · exact context_11_6920_392404
  · exact context_11_6921_392660
  · exact context_11_6922_392926
  · exact context_11_6923_393178

theorem selected_cut_15303 : selected 9 ⟨393180, by decide⟩
    (prefixPartial 12 27696) = some ⟨12, 1, 0, 393180, 27696, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27696_393180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27696 ⟨393180, by decide⟩ :=
  accepted_of_selected 12 27696 ⟨393180, by decide⟩ ⟨12, 1, 0, 393180, 27696, 1, 65536⟩
    (by decide) selected_cut_15303

theorem selected_cut_15304 : selected 8 ⟨393189, by decide⟩
    (prefixPartial 13 110788) = some ⟨13, 2, 0, 393189, 110788, 621, 16384⟩ := by
  decide +kernel

theorem context_13_110788_393189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110788 ⟨393189, by decide⟩ :=
  accepted_of_selected 13 110788 ⟨393189, by decide⟩ ⟨13, 2, 0, 393189, 110788, 621, 16384⟩
    (by decide) selected_cut_15304

theorem selected_cut_15305 : selected 8 ⟨393213, by decide⟩
    (prefixPartial 13 110789) = some ⟨13, 2, 0, 393213, 110789, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_110789_393213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110789 ⟨393213, by decide⟩ :=
  accepted_of_selected 13 110789 ⟨393213, by decide⟩ ⟨13, 2, 0, 393213, 110789, 1809, 16384⟩
    (by decide) selected_cut_15305

theorem selected_cut_15306 : selected 8 ⟨393235, by decide⟩
    (prefixPartial 13 110790) = some ⟨13, 2, 0, 393235, 110790, 1561, 16384⟩ := by
  decide +kernel

theorem context_13_110790_393235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110790 ⟨393235, by decide⟩ :=
  accepted_of_selected 13 110790 ⟨393235, by decide⟩ ⟨13, 2, 0, 393235, 110790, 1561, 16384⟩
    (by decide) selected_cut_15306

theorem selected_cut_15307 : selected 8 ⟨393241, by decide⟩
    (prefixPartial 13 110791) = some ⟨13, 2, 0, 393241, 110791, 677, 16384⟩ := by
  decide +kernel

theorem context_13_110791_393241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110791 ⟨393241, by decide⟩ :=
  accepted_of_selected 13 110791 ⟨393241, by decide⟩ ⟨13, 2, 0, 393241, 110791, 677, 16384⟩
    (by decide) selected_cut_15307

theorem unmarked_context_12_27697_393242 : frontier 9 ⟨393242, by decide⟩
    (prefixCache 12 27697) (prefixPartial 12 27697) = false := by
  decide +kernel

theorem node_context_12_27697_393242 : EJMOriginalGlobalDAGData.nodes 9 ⟨393242, by decide⟩ =
    .split (coordinate 12) (![⟨393189, by decide⟩,⟨393213, by decide⟩,⟨393235, by decide⟩,⟨393241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27697_393242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27697 ⟨393242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27697
    ⟨393242, by decide⟩ (by decide) (![⟨393189, by decide⟩,⟨393213, by decide⟩,⟨393235, by decide⟩,⟨393241, by decide⟩]) unmarked_context_12_27697_393242 node_context_12_27697_393242
  intro a
  fin_cases a
  · exact context_13_110788_393189
  · exact context_13_110789_393213
  · exact context_13_110790_393235
  · exact context_13_110791_393241

theorem selected_cut_15308 : selected 8 ⟨393252, by decide⟩
    (prefixPartial 13 110792) = some ⟨13, 2, 0, 393252, 110792, 641, 16384⟩ := by
  decide +kernel

theorem context_13_110792_393252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110792 ⟨393252, by decide⟩ :=
  accepted_of_selected 13 110792 ⟨393252, by decide⟩ ⟨13, 2, 0, 393252, 110792, 641, 16384⟩
    (by decide) selected_cut_15308

theorem selected_cut_15309 : selected 8 ⟨393278, by decide⟩
    (prefixPartial 13 110793) = some ⟨13, 2, 0, 393278, 110793, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_110793_393278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110793 ⟨393278, by decide⟩ :=
  accepted_of_selected 13 110793 ⟨393278, by decide⟩ ⟨13, 2, 0, 393278, 110793, 2161, 16384⟩
    (by decide) selected_cut_15309

theorem selected_cut_15310 : selected 8 ⟨393297, by decide⟩
    (prefixPartial 13 110794) = some ⟨13, 2, 0, 393297, 110794, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_110794_393297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110794 ⟨393297, by decide⟩ :=
  accepted_of_selected 13 110794 ⟨393297, by decide⟩ ⟨13, 2, 0, 393297, 110794, 1325, 16384⟩
    (by decide) selected_cut_15310

theorem selected_cut_15311 : selected 8 ⟨393303, by decide⟩
    (prefixPartial 13 110795) = some ⟨13, 2, 0, 393303, 110795, 705, 16384⟩ := by
  decide +kernel

theorem context_13_110795_393303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110795 ⟨393303, by decide⟩ :=
  accepted_of_selected 13 110795 ⟨393303, by decide⟩ ⟨13, 2, 0, 393303, 110795, 705, 16384⟩
    (by decide) selected_cut_15311

theorem unmarked_context_12_27698_393304 : frontier 9 ⟨393304, by decide⟩
    (prefixCache 12 27698) (prefixPartial 12 27698) = false := by
  decide +kernel

theorem node_context_12_27698_393304 : EJMOriginalGlobalDAGData.nodes 9 ⟨393304, by decide⟩ =
    .split (coordinate 12) (![⟨393252, by decide⟩,⟨393278, by decide⟩,⟨393297, by decide⟩,⟨393303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27698_393304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27698 ⟨393304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27698
    ⟨393304, by decide⟩ (by decide) (![⟨393252, by decide⟩,⟨393278, by decide⟩,⟨393297, by decide⟩,⟨393303, by decide⟩]) unmarked_context_12_27698_393304 node_context_12_27698_393304
  intro a
  fin_cases a
  · exact context_13_110792_393252
  · exact context_13_110793_393278
  · exact context_13_110794_393297
  · exact context_13_110795_393303

theorem selected_cut_15312 : selected 8 ⟨393315, by decide⟩
    (prefixPartial 13 110796) = some ⟨13, 2, 0, 393315, 110796, 577, 16384⟩ := by
  decide +kernel

theorem context_13_110796_393315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110796 ⟨393315, by decide⟩ :=
  accepted_of_selected 13 110796 ⟨393315, by decide⟩ ⟨13, 2, 0, 393315, 110796, 577, 16384⟩
    (by decide) selected_cut_15312

theorem selected_cut_15313 : selected 8 ⟨393339, by decide⟩
    (prefixPartial 13 110797) = some ⟨13, 2, 0, 393339, 110797, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_110797_393339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110797 ⟨393339, by decide⟩ :=
  accepted_of_selected 13 110797 ⟨393339, by decide⟩ ⟨13, 2, 0, 393339, 110797, 2213, 16384⟩
    (by decide) selected_cut_15313

theorem selected_cut_15314 : selected 8 ⟨393356, by decide⟩
    (prefixPartial 13 110798) = some ⟨13, 2, 0, 393356, 110798, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_110798_393356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110798 ⟨393356, by decide⟩ :=
  accepted_of_selected 13 110798 ⟨393356, by decide⟩ ⟨13, 2, 0, 393356, 110798, 1565, 16384⟩
    (by decide) selected_cut_15314

theorem selected_cut_15315 : selected 8 ⟨393362, by decide⟩
    (prefixPartial 13 110799) = some ⟨13, 2, 0, 393362, 110799, 717, 16384⟩ := by
  decide +kernel

theorem context_13_110799_393362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110799 ⟨393362, by decide⟩ :=
  accepted_of_selected 13 110799 ⟨393362, by decide⟩ ⟨13, 2, 0, 393362, 110799, 717, 16384⟩
    (by decide) selected_cut_15315

theorem unmarked_context_12_27699_393363 : frontier 9 ⟨393363, by decide⟩
    (prefixCache 12 27699) (prefixPartial 12 27699) = false := by
  decide +kernel

theorem node_context_12_27699_393363 : EJMOriginalGlobalDAGData.nodes 9 ⟨393363, by decide⟩ =
    .split (coordinate 12) (![⟨393315, by decide⟩,⟨393339, by decide⟩,⟨393356, by decide⟩,⟨393362, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27699_393363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27699 ⟨393363, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27699
    ⟨393363, by decide⟩ (by decide) (![⟨393315, by decide⟩,⟨393339, by decide⟩,⟨393356, by decide⟩,⟨393362, by decide⟩]) unmarked_context_12_27699_393363 node_context_12_27699_393363
  intro a
  fin_cases a
  · exact context_13_110796_393315
  · exact context_13_110797_393339
  · exact context_13_110798_393356
  · exact context_13_110799_393362

theorem unmarked_context_11_6924_393364 : frontier 10 ⟨393364, by decide⟩
    (prefixCache 11 6924) (prefixPartial 11 6924) = false := by
  decide +kernel

theorem node_context_11_6924_393364 : EJMOriginalGlobalDAGData.nodes 10 ⟨393364, by decide⟩ =
    .split (coordinate 11) (![⟨393180, by decide⟩,⟨393242, by decide⟩,⟨393304, by decide⟩,⟨393363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6924_393364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6924 ⟨393364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6924
    ⟨393364, by decide⟩ (by decide) (![⟨393180, by decide⟩,⟨393242, by decide⟩,⟨393304, by decide⟩,⟨393363, by decide⟩]) unmarked_context_11_6924_393364 node_context_11_6924_393364
  intro a
  fin_cases a
  · exact context_12_27696_393180
  · exact context_12_27697_393242
  · exact context_12_27698_393304
  · exact context_12_27699_393363

theorem selected_cut_15316 : selected 8 ⟨393370, by decide⟩
    (prefixPartial 13 110800) = some ⟨13, 2, 0, 393370, 110800, 437, 16384⟩ := by
  decide +kernel

theorem context_13_110800_393370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110800 ⟨393370, by decide⟩ :=
  accepted_of_selected 13 110800 ⟨393370, by decide⟩ ⟨13, 2, 0, 393370, 110800, 437, 16384⟩
    (by decide) selected_cut_15316

theorem selected_cut_15317 : selected 8 ⟨393396, by decide⟩
    (prefixPartial 13 110801) = some ⟨13, 2, 0, 393396, 110801, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_110801_393396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110801 ⟨393396, by decide⟩ :=
  accepted_of_selected 13 110801 ⟨393396, by decide⟩ ⟨13, 2, 0, 393396, 110801, 2025, 16384⟩
    (by decide) selected_cut_15317

theorem selected_cut_15318 : selected 8 ⟨393413, by decide⟩
    (prefixPartial 13 110802) = some ⟨13, 2, 0, 393413, 110802, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_110802_393413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110802 ⟨393413, by decide⟩ :=
  accepted_of_selected 13 110802 ⟨393413, by decide⟩ ⟨13, 2, 0, 393413, 110802, 1293, 16384⟩
    (by decide) selected_cut_15318

theorem selected_cut_15319 : selected 8 ⟨393417, by decide⟩
    (prefixPartial 13 110803) = some ⟨13, 2, 0, 393417, 110803, 685, 16384⟩ := by
  decide +kernel

theorem context_13_110803_393417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110803 ⟨393417, by decide⟩ :=
  accepted_of_selected 13 110803 ⟨393417, by decide⟩ ⟨13, 2, 0, 393417, 110803, 685, 16384⟩
    (by decide) selected_cut_15319

theorem unmarked_context_12_27700_393418 : frontier 9 ⟨393418, by decide⟩
    (prefixCache 12 27700) (prefixPartial 12 27700) = false := by
  decide +kernel

theorem node_context_12_27700_393418 : EJMOriginalGlobalDAGData.nodes 9 ⟨393418, by decide⟩ =
    .split (coordinate 12) (![⟨393370, by decide⟩,⟨393396, by decide⟩,⟨393413, by decide⟩,⟨393417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27700_393418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27700 ⟨393418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27700
    ⟨393418, by decide⟩ (by decide) (![⟨393370, by decide⟩,⟨393396, by decide⟩,⟨393413, by decide⟩,⟨393417, by decide⟩]) unmarked_context_12_27700_393418 node_context_12_27700_393418
  intro a
  fin_cases a
  · exact context_13_110800_393370
  · exact context_13_110801_393396
  · exact context_13_110802_393413
  · exact context_13_110803_393417

theorem selected_cut_15320 : selected 8 ⟨393424, by decide⟩
    (prefixPartial 13 110804) = some ⟨13, 2, 0, 393424, 110804, 469, 16384⟩ := by
  decide +kernel

theorem context_13_110804_393424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110804 ⟨393424, by decide⟩ :=
  accepted_of_selected 13 110804 ⟨393424, by decide⟩ ⟨13, 2, 0, 393424, 110804, 469, 16384⟩
    (by decide) selected_cut_15320

theorem selected_cut_15321 : selected 8 ⟨393448, by decide⟩
    (prefixPartial 13 110805) = some ⟨13, 2, 0, 393448, 110805, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_110805_393448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110805 ⟨393448, by decide⟩ :=
  accepted_of_selected 13 110805 ⟨393448, by decide⟩ ⟨13, 2, 0, 393448, 110805, 1741, 16384⟩
    (by decide) selected_cut_15321

theorem selected_cut_15322 : selected 8 ⟨393467, by decide⟩
    (prefixPartial 13 110806) = some ⟨13, 2, 0, 393467, 110806, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_110806_393467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110806 ⟨393467, by decide⟩ :=
  accepted_of_selected 13 110806 ⟨393467, by decide⟩ ⟨13, 2, 0, 393467, 110806, 1641, 16384⟩
    (by decide) selected_cut_15322

theorem selected_cut_15323 : selected 8 ⟨393473, by decide⟩
    (prefixPartial 13 110807) = some ⟨13, 2, 0, 393473, 110807, 725, 16384⟩ := by
  decide +kernel

theorem context_13_110807_393473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110807 ⟨393473, by decide⟩ :=
  accepted_of_selected 13 110807 ⟨393473, by decide⟩ ⟨13, 2, 0, 393473, 110807, 725, 16384⟩
    (by decide) selected_cut_15323

theorem unmarked_context_12_27701_393474 : frontier 9 ⟨393474, by decide⟩
    (prefixCache 12 27701) (prefixPartial 12 27701) = false := by
  decide +kernel

theorem node_context_12_27701_393474 : EJMOriginalGlobalDAGData.nodes 9 ⟨393474, by decide⟩ =
    .split (coordinate 12) (![⟨393424, by decide⟩,⟨393448, by decide⟩,⟨393467, by decide⟩,⟨393473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27701_393474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27701 ⟨393474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27701
    ⟨393474, by decide⟩ (by decide) (![⟨393424, by decide⟩,⟨393448, by decide⟩,⟨393467, by decide⟩,⟨393473, by decide⟩]) unmarked_context_12_27701_393474 node_context_12_27701_393474
  intro a
  fin_cases a
  · exact context_13_110804_393424
  · exact context_13_110805_393448
  · exact context_13_110806_393467
  · exact context_13_110807_393473

theorem selected_cut_15324 : selected 8 ⟨393480, by decide⟩
    (prefixPartial 13 110808) = some ⟨13, 2, 0, 393480, 110808, 461, 16384⟩ := by
  decide +kernel

theorem context_13_110808_393480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110808 ⟨393480, by decide⟩ :=
  accepted_of_selected 13 110808 ⟨393480, by decide⟩ ⟨13, 2, 0, 393480, 110808, 461, 16384⟩
    (by decide) selected_cut_15324

theorem selected_cut_15325 : selected 8 ⟨393503, by decide⟩
    (prefixPartial 13 110809) = some ⟨13, 2, 0, 393503, 110809, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_110809_393503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110809 ⟨393503, by decide⟩ :=
  accepted_of_selected 13 110809 ⟨393503, by decide⟩ ⟨13, 2, 0, 393503, 110809, 2137, 16384⟩
    (by decide) selected_cut_15325

theorem selected_cut_15326 : selected 8 ⟨393525, by decide⟩
    (prefixPartial 13 110810) = some ⟨13, 2, 0, 393525, 110810, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_110810_393525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110810 ⟨393525, by decide⟩ :=
  accepted_of_selected 13 110810 ⟨393525, by decide⟩ ⟨13, 2, 0, 393525, 110810, 1409, 16384⟩
    (by decide) selected_cut_15326

theorem selected_cut_15327 : selected 8 ⟨393536, by decide⟩
    (prefixPartial 13 110811) = some ⟨13, 2, 0, 393536, 110811, 785, 16384⟩ := by
  decide +kernel

theorem context_13_110811_393536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110811 ⟨393536, by decide⟩ :=
  accepted_of_selected 13 110811 ⟨393536, by decide⟩ ⟨13, 2, 0, 393536, 110811, 785, 16384⟩
    (by decide) selected_cut_15327

theorem unmarked_context_12_27702_393537 : frontier 9 ⟨393537, by decide⟩
    (prefixCache 12 27702) (prefixPartial 12 27702) = false := by
  decide +kernel

theorem node_context_12_27702_393537 : EJMOriginalGlobalDAGData.nodes 9 ⟨393537, by decide⟩ =
    .split (coordinate 12) (![⟨393480, by decide⟩,⟨393503, by decide⟩,⟨393525, by decide⟩,⟨393536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27702_393537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27702 ⟨393537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27702
    ⟨393537, by decide⟩ (by decide) (![⟨393480, by decide⟩,⟨393503, by decide⟩,⟨393525, by decide⟩,⟨393536, by decide⟩]) unmarked_context_12_27702_393537 node_context_12_27702_393537
  intro a
  fin_cases a
  · exact context_13_110808_393480
  · exact context_13_110809_393503
  · exact context_13_110810_393525
  · exact context_13_110811_393536

theorem selected_cut_15328 : selected 8 ⟨393544, by decide⟩
    (prefixPartial 13 110812) = some ⟨13, 2, 0, 393544, 110812, 445, 16384⟩ := by
  decide +kernel

theorem context_13_110812_393544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110812 ⟨393544, by decide⟩ :=
  accepted_of_selected 13 110812 ⟨393544, by decide⟩ ⟨13, 2, 0, 393544, 110812, 445, 16384⟩
    (by decide) selected_cut_15328

theorem selected_cut_15329 : selected 8 ⟨393576, by decide⟩
    (prefixPartial 13 110813) = some ⟨13, 2, 0, 393576, 110813, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_110813_393576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110813 ⟨393576, by decide⟩ :=
  accepted_of_selected 13 110813 ⟨393576, by decide⟩ ⟨13, 2, 0, 393576, 110813, 2289, 16384⟩
    (by decide) selected_cut_15329

theorem selected_cut_15330 : selected 8 ⟨393597, by decide⟩
    (prefixPartial 13 110814) = some ⟨13, 2, 0, 393597, 110814, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_110814_393597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110814 ⟨393597, by decide⟩ :=
  accepted_of_selected 13 110814 ⟨393597, by decide⟩ ⟨13, 2, 0, 393597, 110814, 1737, 16384⟩
    (by decide) selected_cut_15330

theorem selected_cut_15331 : selected 8 ⟨393607, by decide⟩
    (prefixPartial 13 110815) = some ⟨13, 2, 0, 393607, 110815, 889, 16384⟩ := by
  decide +kernel

theorem context_13_110815_393607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110815 ⟨393607, by decide⟩ :=
  accepted_of_selected 13 110815 ⟨393607, by decide⟩ ⟨13, 2, 0, 393607, 110815, 889, 16384⟩
    (by decide) selected_cut_15331

theorem unmarked_context_12_27703_393608 : frontier 9 ⟨393608, by decide⟩
    (prefixCache 12 27703) (prefixPartial 12 27703) = false := by
  decide +kernel

theorem node_context_12_27703_393608 : EJMOriginalGlobalDAGData.nodes 9 ⟨393608, by decide⟩ =
    .split (coordinate 12) (![⟨393544, by decide⟩,⟨393576, by decide⟩,⟨393597, by decide⟩,⟨393607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27703_393608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27703 ⟨393608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27703
    ⟨393608, by decide⟩ (by decide) (![⟨393544, by decide⟩,⟨393576, by decide⟩,⟨393597, by decide⟩,⟨393607, by decide⟩]) unmarked_context_12_27703_393608 node_context_12_27703_393608
  intro a
  fin_cases a
  · exact context_13_110812_393544
  · exact context_13_110813_393576
  · exact context_13_110814_393597
  · exact context_13_110815_393607

theorem unmarked_context_11_6925_393609 : frontier 10 ⟨393609, by decide⟩
    (prefixCache 11 6925) (prefixPartial 11 6925) = false := by
  decide +kernel

theorem node_context_11_6925_393609 : EJMOriginalGlobalDAGData.nodes 10 ⟨393609, by decide⟩ =
    .split (coordinate 11) (![⟨393418, by decide⟩,⟨393474, by decide⟩,⟨393537, by decide⟩,⟨393608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6925_393609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6925 ⟨393609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6925
    ⟨393609, by decide⟩ (by decide) (![⟨393418, by decide⟩,⟨393474, by decide⟩,⟨393537, by decide⟩,⟨393608, by decide⟩]) unmarked_context_11_6925_393609 node_context_11_6925_393609
  intro a
  fin_cases a
  · exact context_12_27700_393418
  · exact context_12_27701_393474
  · exact context_12_27702_393537
  · exact context_12_27703_393608

theorem selected_cut_15332 : selected 8 ⟨393616, by decide⟩
    (prefixPartial 13 110816) = some ⟨13, 2, 0, 393616, 110816, 321, 16384⟩ := by
  decide +kernel

theorem context_13_110816_393616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110816 ⟨393616, by decide⟩ :=
  accepted_of_selected 13 110816 ⟨393616, by decide⟩ ⟨13, 2, 0, 393616, 110816, 321, 16384⟩
    (by decide) selected_cut_15332

theorem selected_cut_15333 : selected 8 ⟨393657, by decide⟩
    (prefixPartial 13 110817) = some ⟨13, 2, 0, 393657, 110817, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_110817_393657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110817 ⟨393657, by decide⟩ :=
  accepted_of_selected 13 110817 ⟨393657, by decide⟩ ⟨13, 2, 0, 393657, 110817, 2541, 16384⟩
    (by decide) selected_cut_15333

theorem selected_cut_15334 : selected 8 ⟨393674, by decide⟩
    (prefixPartial 13 110818) = some ⟨13, 2, 0, 393674, 110818, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_110818_393674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110818 ⟨393674, by decide⟩ :=
  accepted_of_selected 13 110818 ⟨393674, by decide⟩ ⟨13, 2, 0, 393674, 110818, 1517, 16384⟩
    (by decide) selected_cut_15334

theorem selected_cut_15335 : selected 8 ⟨393682, by decide⟩
    (prefixPartial 13 110819) = some ⟨13, 2, 0, 393682, 110819, 761, 16384⟩ := by
  decide +kernel

theorem context_13_110819_393682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110819 ⟨393682, by decide⟩ :=
  accepted_of_selected 13 110819 ⟨393682, by decide⟩ ⟨13, 2, 0, 393682, 110819, 761, 16384⟩
    (by decide) selected_cut_15335

theorem unmarked_context_12_27704_393683 : frontier 9 ⟨393683, by decide⟩
    (prefixCache 12 27704) (prefixPartial 12 27704) = false := by
  decide +kernel

theorem node_context_12_27704_393683 : EJMOriginalGlobalDAGData.nodes 9 ⟨393683, by decide⟩ =
    .split (coordinate 12) (![⟨393616, by decide⟩,⟨393657, by decide⟩,⟨393674, by decide⟩,⟨393682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27704_393683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27704 ⟨393683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27704
    ⟨393683, by decide⟩ (by decide) (![⟨393616, by decide⟩,⟨393657, by decide⟩,⟨393674, by decide⟩,⟨393682, by decide⟩]) unmarked_context_12_27704_393683 node_context_12_27704_393683
  intro a
  fin_cases a
  · exact context_13_110816_393616
  · exact context_13_110817_393657
  · exact context_13_110818_393674
  · exact context_13_110819_393682

theorem selected_cut_15336 : selected 8 ⟨393693, by decide⟩
    (prefixPartial 13 110820) = some ⟨13, 2, 0, 393693, 110820, 365, 16384⟩ := by
  decide +kernel

theorem context_13_110820_393693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110820 ⟨393693, by decide⟩ :=
  accepted_of_selected 13 110820 ⟨393693, by decide⟩ ⟨13, 2, 0, 393693, 110820, 365, 16384⟩
    (by decide) selected_cut_15336

theorem selected_cut_15337 : selected 8 ⟨393727, by decide⟩
    (prefixPartial 13 110821) = some ⟨13, 2, 0, 393727, 110821, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_110821_393727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110821 ⟨393727, by decide⟩ :=
  accepted_of_selected 13 110821 ⟨393727, by decide⟩ ⟨13, 2, 0, 393727, 110821, 2445, 16384⟩
    (by decide) selected_cut_15337

theorem selected_cut_15338 : selected 8 ⟨393747, by decide⟩
    (prefixPartial 13 110822) = some ⟨13, 2, 0, 393747, 110822, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_110822_393747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110822 ⟨393747, by decide⟩ :=
  accepted_of_selected 13 110822 ⟨393747, by decide⟩ ⟨13, 2, 0, 393747, 110822, 1605, 16384⟩
    (by decide) selected_cut_15338

theorem selected_cut_15339 : selected 8 ⟨393756, by decide⟩
    (prefixPartial 13 110823) = some ⟨13, 2, 0, 393756, 110823, 789, 16384⟩ := by
  decide +kernel

theorem context_13_110823_393756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110823 ⟨393756, by decide⟩ :=
  accepted_of_selected 13 110823 ⟨393756, by decide⟩ ⟨13, 2, 0, 393756, 110823, 789, 16384⟩
    (by decide) selected_cut_15339

theorem unmarked_context_12_27705_393757 : frontier 9 ⟨393757, by decide⟩
    (prefixCache 12 27705) (prefixPartial 12 27705) = false := by
  decide +kernel

theorem node_context_12_27705_393757 : EJMOriginalGlobalDAGData.nodes 9 ⟨393757, by decide⟩ =
    .split (coordinate 12) (![⟨393693, by decide⟩,⟨393727, by decide⟩,⟨393747, by decide⟩,⟨393756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27705_393757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27705 ⟨393757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27705
    ⟨393757, by decide⟩ (by decide) (![⟨393693, by decide⟩,⟨393727, by decide⟩,⟨393747, by decide⟩,⟨393756, by decide⟩]) unmarked_context_12_27705_393757 node_context_12_27705_393757
  intro a
  fin_cases a
  · exact context_13_110820_393693
  · exact context_13_110821_393727
  · exact context_13_110822_393747
  · exact context_13_110823_393756

theorem selected_cut_15340 : selected 8 ⟨393765, by decide⟩
    (prefixPartial 13 110824) = some ⟨13, 2, 0, 393765, 110824, 253, 16384⟩ := by
  decide +kernel

theorem context_13_110824_393765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110824 ⟨393765, by decide⟩ :=
  accepted_of_selected 13 110824 ⟨393765, by decide⟩ ⟨13, 2, 0, 393765, 110824, 253, 16384⟩
    (by decide) selected_cut_15340

theorem selected_cut_15341 : selected 8 ⟨393802, by decide⟩
    (prefixPartial 13 110825) = some ⟨13, 2, 0, 393802, 110825, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_110825_393802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110825 ⟨393802, by decide⟩ :=
  accepted_of_selected 13 110825 ⟨393802, by decide⟩ ⟨13, 2, 0, 393802, 110825, 2489, 16384⟩
    (by decide) selected_cut_15341

theorem selected_cut_15342 : selected 8 ⟨393819, by decide⟩
    (prefixPartial 13 110826) = some ⟨13, 2, 0, 393819, 110826, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_110826_393819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110826 ⟨393819, by decide⟩ :=
  accepted_of_selected 13 110826 ⟨393819, by decide⟩ ⟨13, 2, 0, 393819, 110826, 1345, 16384⟩
    (by decide) selected_cut_15342

theorem selected_cut_15343 : selected 8 ⟨393826, by decide⟩
    (prefixPartial 13 110827) = some ⟨13, 2, 0, 393826, 110827, 813, 16384⟩ := by
  decide +kernel

theorem context_13_110827_393826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110827 ⟨393826, by decide⟩ :=
  accepted_of_selected 13 110827 ⟨393826, by decide⟩ ⟨13, 2, 0, 393826, 110827, 813, 16384⟩
    (by decide) selected_cut_15343

theorem unmarked_context_12_27706_393827 : frontier 9 ⟨393827, by decide⟩
    (prefixCache 12 27706) (prefixPartial 12 27706) = false := by
  decide +kernel

theorem node_context_12_27706_393827 : EJMOriginalGlobalDAGData.nodes 9 ⟨393827, by decide⟩ =
    .split (coordinate 12) (![⟨393765, by decide⟩,⟨393802, by decide⟩,⟨393819, by decide⟩,⟨393826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27706_393827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27706 ⟨393827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27706
    ⟨393827, by decide⟩ (by decide) (![⟨393765, by decide⟩,⟨393802, by decide⟩,⟨393819, by decide⟩,⟨393826, by decide⟩]) unmarked_context_12_27706_393827 node_context_12_27706_393827
  intro a
  fin_cases a
  · exact context_13_110824_393765
  · exact context_13_110825_393802
  · exact context_13_110826_393819
  · exact context_13_110827_393826

theorem selected_cut_15344 : selected 8 ⟨393836, by decide⟩
    (prefixPartial 13 110828) = some ⟨13, 2, 0, 393836, 110828, 261, 16384⟩ := by
  decide +kernel

theorem context_13_110828_393836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110828 ⟨393836, by decide⟩ :=
  accepted_of_selected 13 110828 ⟨393836, by decide⟩ ⟨13, 2, 0, 393836, 110828, 261, 16384⟩
    (by decide) selected_cut_15344

theorem selected_cut_15345 : selected 8 ⟨393879, by decide⟩
    (prefixPartial 13 110829) = some ⟨13, 2, 0, 393879, 110829, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_110829_393879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110829 ⟨393879, by decide⟩ :=
  accepted_of_selected 13 110829 ⟨393879, by decide⟩ ⟨13, 2, 0, 393879, 110829, 2713, 16384⟩
    (by decide) selected_cut_15345

theorem selected_cut_15346 : selected 8 ⟨393901, by decide⟩
    (prefixPartial 13 110830) = some ⟨13, 2, 0, 393901, 110830, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_110830_393901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110830 ⟨393901, by decide⟩ :=
  accepted_of_selected 13 110830 ⟨393901, by decide⟩ ⟨13, 2, 0, 393901, 110830, 1689, 16384⟩
    (by decide) selected_cut_15346

theorem selected_cut_15347 : selected 8 ⟨393911, by decide⟩
    (prefixPartial 13 110831) = some ⟨13, 2, 0, 393911, 110831, 933, 16384⟩ := by
  decide +kernel

theorem context_13_110831_393911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110831 ⟨393911, by decide⟩ :=
  accepted_of_selected 13 110831 ⟨393911, by decide⟩ ⟨13, 2, 0, 393911, 110831, 933, 16384⟩
    (by decide) selected_cut_15347

theorem unmarked_context_12_27707_393912 : frontier 9 ⟨393912, by decide⟩
    (prefixCache 12 27707) (prefixPartial 12 27707) = false := by
  decide +kernel

theorem node_context_12_27707_393912 : EJMOriginalGlobalDAGData.nodes 9 ⟨393912, by decide⟩ =
    .split (coordinate 12) (![⟨393836, by decide⟩,⟨393879, by decide⟩,⟨393901, by decide⟩,⟨393911, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27707_393912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27707 ⟨393912, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27707
    ⟨393912, by decide⟩ (by decide) (![⟨393836, by decide⟩,⟨393879, by decide⟩,⟨393901, by decide⟩,⟨393911, by decide⟩]) unmarked_context_12_27707_393912 node_context_12_27707_393912
  intro a
  fin_cases a
  · exact context_13_110828_393836
  · exact context_13_110829_393879
  · exact context_13_110830_393901
  · exact context_13_110831_393911

theorem unmarked_context_11_6926_393913 : frontier 10 ⟨393913, by decide⟩
    (prefixCache 11 6926) (prefixPartial 11 6926) = false := by
  decide +kernel

theorem node_context_11_6926_393913 : EJMOriginalGlobalDAGData.nodes 10 ⟨393913, by decide⟩ =
    .split (coordinate 11) (![⟨393683, by decide⟩,⟨393757, by decide⟩,⟨393827, by decide⟩,⟨393912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6926_393913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6926 ⟨393913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6926
    ⟨393913, by decide⟩ (by decide) (![⟨393683, by decide⟩,⟨393757, by decide⟩,⟨393827, by decide⟩,⟨393912, by decide⟩]) unmarked_context_11_6926_393913 node_context_11_6926_393913
  intro a
  fin_cases a
  · exact context_12_27704_393683
  · exact context_12_27705_393757
  · exact context_12_27706_393827
  · exact context_12_27707_393912

theorem selected_cut_15348 : selected 8 ⟨393916, by decide⟩
    (prefixPartial 13 110832) = some ⟨13, 2, 0, 393916, 110832, 201, 16384⟩ := by
  decide +kernel

theorem context_13_110832_393916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110832 ⟨393916, by decide⟩ :=
  accepted_of_selected 13 110832 ⟨393916, by decide⟩ ⟨13, 2, 0, 393916, 110832, 201, 16384⟩
    (by decide) selected_cut_15348

theorem selected_cut_15349 : selected 8 ⟨393964, by decide⟩
    (prefixPartial 13 110833) = some ⟨13, 2, 0, 393964, 110833, 3049, 16384⟩ := by
  decide +kernel

theorem context_13_110833_393964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110833 ⟨393964, by decide⟩ :=
  accepted_of_selected 13 110833 ⟨393964, by decide⟩ ⟨13, 2, 0, 393964, 110833, 3049, 16384⟩
    (by decide) selected_cut_15349

theorem selected_cut_15350 : selected 8 ⟨393985, by decide⟩
    (prefixPartial 13 110834) = some ⟨13, 2, 0, 393985, 110834, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_110834_393985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110834 ⟨393985, by decide⟩ :=
  accepted_of_selected 13 110834 ⟨393985, by decide⟩ ⟨13, 2, 0, 393985, 110834, 1605, 16384⟩
    (by decide) selected_cut_15350

theorem selected_cut_15351 : selected 8 ⟨393994, by decide⟩
    (prefixPartial 13 110835) = some ⟨13, 2, 0, 393994, 110835, 857, 16384⟩ := by
  decide +kernel

theorem context_13_110835_393994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110835 ⟨393994, by decide⟩ :=
  accepted_of_selected 13 110835 ⟨393994, by decide⟩ ⟨13, 2, 0, 393994, 110835, 857, 16384⟩
    (by decide) selected_cut_15351

theorem unmarked_context_12_27708_393995 : frontier 9 ⟨393995, by decide⟩
    (prefixCache 12 27708) (prefixPartial 12 27708) = false := by
  decide +kernel

theorem node_context_12_27708_393995 : EJMOriginalGlobalDAGData.nodes 9 ⟨393995, by decide⟩ =
    .split (coordinate 12) (![⟨393916, by decide⟩,⟨393964, by decide⟩,⟨393985, by decide⟩,⟨393994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27708_393995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27708 ⟨393995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27708
    ⟨393995, by decide⟩ (by decide) (![⟨393916, by decide⟩,⟨393964, by decide⟩,⟨393985, by decide⟩,⟨393994, by decide⟩]) unmarked_context_12_27708_393995 node_context_12_27708_393995
  intro a
  fin_cases a
  · exact context_13_110832_393916
  · exact context_13_110833_393964
  · exact context_13_110834_393985
  · exact context_13_110835_393994

theorem selected_cut_15352 : selected 8 ⟨393999, by decide⟩
    (prefixPartial 13 110836) = some ⟨13, 2, 0, 393999, 110836, 157, 16384⟩ := by
  decide +kernel

theorem context_13_110836_393999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110836 ⟨393999, by decide⟩ :=
  accepted_of_selected 13 110836 ⟨393999, by decide⟩ ⟨13, 2, 0, 393999, 110836, 157, 16384⟩
    (by decide) selected_cut_15352

theorem selected_cut_15353 : selected 8 ⟨394049, by decide⟩
    (prefixPartial 13 110837) = some ⟨13, 2, 0, 394049, 110837, 3029, 16384⟩ := by
  decide +kernel

theorem context_13_110837_394049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110837 ⟨394049, by decide⟩ :=
  accepted_of_selected 13 110837 ⟨394049, by decide⟩ ⟨13, 2, 0, 394049, 110837, 3029, 16384⟩
    (by decide) selected_cut_15353

theorem selected_cut_15354 : selected 8 ⟨394076, by decide⟩
    (prefixPartial 13 110838) = some ⟨13, 2, 0, 394076, 110838, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_110838_394076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110838 ⟨394076, by decide⟩ :=
  accepted_of_selected 13 110838 ⟨394076, by decide⟩ ⟨13, 2, 0, 394076, 110838, 2113, 16384⟩
    (by decide) selected_cut_15354

theorem selected_cut_15355 : selected 8 ⟨394084, by decide⟩
    (prefixPartial 13 110839) = some ⟨13, 2, 0, 394084, 110839, 945, 16384⟩ := by
  decide +kernel

theorem context_13_110839_394084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110839 ⟨394084, by decide⟩ :=
  accepted_of_selected 13 110839 ⟨394084, by decide⟩ ⟨13, 2, 0, 394084, 110839, 945, 16384⟩
    (by decide) selected_cut_15355

theorem unmarked_context_12_27709_394085 : frontier 9 ⟨394085, by decide⟩
    (prefixCache 12 27709) (prefixPartial 12 27709) = false := by
  decide +kernel

theorem node_context_12_27709_394085 : EJMOriginalGlobalDAGData.nodes 9 ⟨394085, by decide⟩ =
    .split (coordinate 12) (![⟨393999, by decide⟩,⟨394049, by decide⟩,⟨394076, by decide⟩,⟨394084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27709_394085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27709 ⟨394085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27709
    ⟨394085, by decide⟩ (by decide) (![⟨393999, by decide⟩,⟨394049, by decide⟩,⟨394076, by decide⟩,⟨394084, by decide⟩]) unmarked_context_12_27709_394085 node_context_12_27709_394085
  intro a
  fin_cases a
  · exact context_13_110836_393999
  · exact context_13_110837_394049
  · exact context_13_110838_394076
  · exact context_13_110839_394084

theorem selected_cut_15356 : selected 8 ⟨394089, by decide⟩
    (prefixPartial 13 110840) = some ⟨13, 2, 0, 394089, 110840, 93, 16384⟩ := by
  decide +kernel

theorem context_13_110840_394089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110840 ⟨394089, by decide⟩ :=
  accepted_of_selected 13 110840 ⟨394089, by decide⟩ ⟨13, 2, 0, 394089, 110840, 93, 16384⟩
    (by decide) selected_cut_15356

theorem selected_cut_15357 : selected 8 ⟨394140, by decide⟩
    (prefixPartial 13 110841) = some ⟨13, 2, 0, 394140, 110841, 3137, 16384⟩ := by
  decide +kernel

theorem context_13_110841_394140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110841 ⟨394140, by decide⟩ :=
  accepted_of_selected 13 110841 ⟨394140, by decide⟩ ⟨13, 2, 0, 394140, 110841, 3137, 16384⟩
    (by decide) selected_cut_15357

theorem selected_cut_15358 : selected 8 ⟨394163, by decide⟩
    (prefixPartial 13 110842) = some ⟨13, 2, 0, 394163, 110842, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_110842_394163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110842 ⟨394163, by decide⟩ :=
  accepted_of_selected 13 110842 ⟨394163, by decide⟩ ⟨13, 2, 0, 394163, 110842, 1733, 16384⟩
    (by decide) selected_cut_15358

theorem selected_cut_15359 : selected 8 ⟨394173, by decide⟩
    (prefixPartial 13 110843) = some ⟨13, 2, 0, 394173, 110843, 941, 16384⟩ := by
  decide +kernel

theorem context_13_110843_394173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 110843 ⟨394173, by decide⟩ :=
  accepted_of_selected 13 110843 ⟨394173, by decide⟩ ⟨13, 2, 0, 394173, 110843, 941, 16384⟩
    (by decide) selected_cut_15359

theorem unmarked_context_12_27710_394174 : frontier 9 ⟨394174, by decide⟩
    (prefixCache 12 27710) (prefixPartial 12 27710) = false := by
  decide +kernel

theorem node_context_12_27710_394174 : EJMOriginalGlobalDAGData.nodes 9 ⟨394174, by decide⟩ =
    .split (coordinate 12) (![⟨394089, by decide⟩,⟨394140, by decide⟩,⟨394163, by decide⟩,⟨394173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27710_394174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27710 ⟨394174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27710
    ⟨394174, by decide⟩ (by decide) (![⟨394089, by decide⟩,⟨394140, by decide⟩,⟨394163, by decide⟩,⟨394173, by decide⟩]) unmarked_context_12_27710_394174 node_context_12_27710_394174
  intro a
  fin_cases a
  · exact context_13_110840_394089
  · exact context_13_110841_394140
  · exact context_13_110842_394163
  · exact context_13_110843_394173

theorem selected_cut_15360 : selected 9 ⟨394175, by decide⟩
    (prefixPartial 12 27711) = some ⟨12, 1, 0, 394175, 27711, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27711_394175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27711 ⟨394175, by decide⟩ :=
  accepted_of_selected 12 27711 ⟨394175, by decide⟩ ⟨12, 1, 0, 394175, 27711, 1, 65536⟩
    (by decide) selected_cut_15360

theorem unmarked_context_11_6927_394176 : frontier 10 ⟨394176, by decide⟩
    (prefixCache 11 6927) (prefixPartial 11 6927) = false := by
  decide +kernel

theorem node_context_11_6927_394176 : EJMOriginalGlobalDAGData.nodes 10 ⟨394176, by decide⟩ =
    .split (coordinate 11) (![⟨393995, by decide⟩,⟨394085, by decide⟩,⟨394174, by decide⟩,⟨394175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6927_394176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6927 ⟨394176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6927
    ⟨394176, by decide⟩ (by decide) (![⟨393995, by decide⟩,⟨394085, by decide⟩,⟨394174, by decide⟩,⟨394175, by decide⟩]) unmarked_context_11_6927_394176 node_context_11_6927_394176
  intro a
  fin_cases a
  · exact context_12_27708_393995
  · exact context_12_27709_394085
  · exact context_12_27710_394174
  · exact context_12_27711_394175

theorem unmarked_context_10_1731_394177 : frontier 11 ⟨394177, by decide⟩
    (prefixCache 10 1731) (prefixPartial 10 1731) = false := by
  decide +kernel

theorem node_context_10_1731_394177 : EJMOriginalGlobalDAGData.nodes 11 ⟨394177, by decide⟩ =
    .split (coordinate 10) (![⟨393364, by decide⟩,⟨393609, by decide⟩,⟨393913, by decide⟩,⟨394176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1731_394177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1731 ⟨394177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1731
    ⟨394177, by decide⟩ (by decide) (![⟨393364, by decide⟩,⟨393609, by decide⟩,⟨393913, by decide⟩,⟨394176, by decide⟩]) unmarked_context_10_1731_394177 node_context_10_1731_394177
  intro a
  fin_cases a
  · exact context_11_6924_393364
  · exact context_11_6925_393609
  · exact context_11_6926_393913
  · exact context_11_6927_394176

theorem unmarked_context_9_432_394178 : frontier 12 ⟨394178, by decide⟩
    (prefixCache 9 432) (prefixPartial 9 432) = false := by
  decide +kernel

theorem node_context_9_432_394178 : EJMOriginalGlobalDAGData.nodes 12 ⟨394178, by decide⟩ =
    .split (coordinate 9) (![⟨390869, by decide⟩,⟨392058, by decide⟩,⟨393179, by decide⟩,⟨394177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_432_394178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 432 ⟨394178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 432
    ⟨394178, by decide⟩ (by decide) (![⟨390869, by decide⟩,⟨392058, by decide⟩,⟨393179, by decide⟩,⟨394177, by decide⟩]) unmarked_context_9_432_394178 node_context_9_432_394178
  intro a
  fin_cases a
  · exact context_10_1728_390869
  · exact context_10_1729_392058
  · exact context_10_1730_393179
  · exact context_10_1731_394177

theorem selected_cut_15361 : selected 9 ⟨394179, by decide⟩
    (prefixPartial 12 27712) = some ⟨12, 1, 0, 394179, 27712, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27712_394179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27712 ⟨394179, by decide⟩ :=
  accepted_of_selected 12 27712 ⟨394179, by decide⟩ ⟨12, 1, 0, 394179, 27712, 1, 65536⟩
    (by decide) selected_cut_15361

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
