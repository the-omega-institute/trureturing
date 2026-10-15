/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover119
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_11522 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102692) = some ⟨13, 1, 0, 3444, 102692, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102692_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102692 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102692 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102692, 1, 16384⟩
    (by decide) selected_cut_11522

theorem selected_cut_11523 : selected 8 ⟨307997, by decide⟩
    (prefixPartial 13 102693) = some ⟨13, 2, 0, 307997, 102693, 3333, 16384⟩ := by
  decide +kernel

theorem context_13_102693_307997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102693 ⟨307997, by decide⟩ :=
  accepted_of_selected 13 102693 ⟨307997, by decide⟩ ⟨13, 2, 0, 307997, 102693, 3333, 16384⟩
    (by decide) selected_cut_11523

theorem selected_cut_11524 : selected 8 ⟨308037, by decide⟩
    (prefixPartial 13 102694) = some ⟨13, 2, 0, 308037, 102694, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_102694_308037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102694 ⟨308037, by decide⟩ :=
  accepted_of_selected 13 102694 ⟨308037, by decide⟩ ⟨13, 2, 0, 308037, 102694, 2393, 16384⟩
    (by decide) selected_cut_11524

theorem selected_cut_11525 : selected 8 ⟨308056, by decide⟩
    (prefixPartial 13 102695) = some ⟨13, 2, 0, 308056, 102695, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_102695_308056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102695 ⟨308056, by decide⟩ :=
  accepted_of_selected 13 102695 ⟨308056, by decide⟩ ⟨13, 2, 0, 308056, 102695, 1269, 16384⟩
    (by decide) selected_cut_11525

theorem unmarked_context_12_25673_308057 : frontier 9 ⟨308057, by decide⟩
    (prefixCache 12 25673) (prefixPartial 12 25673) = false := by
  decide +kernel

theorem node_context_12_25673_308057 : EJMOriginalGlobalDAGData.nodes 9 ⟨308057, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨307997, by decide⟩,⟨308037, by decide⟩,⟨308056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25673_308057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25673 ⟨308057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25673
    ⟨308057, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨307997, by decide⟩,⟨308037, by decide⟩,⟨308056, by decide⟩]) unmarked_context_12_25673_308057 node_context_12_25673_308057
  intro a
  fin_cases a
  · exact context_13_102692_3444
  · exact context_13_102693_307997
  · exact context_13_102694_308037
  · exact context_13_102695_308056

theorem selected_cut_11526 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102696) = some ⟨13, 1, 0, 3444, 102696, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102696_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102696 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102696 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102696, 1, 16384⟩
    (by decide) selected_cut_11526

theorem selected_cut_11527 : selected 8 ⟨308089, by decide⟩
    (prefixPartial 13 102697) = some ⟨13, 2, 0, 308089, 102697, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_102697_308089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102697 ⟨308089, by decide⟩ :=
  accepted_of_selected 13 102697 ⟨308089, by decide⟩ ⟨13, 2, 0, 308089, 102697, 2237, 16384⟩
    (by decide) selected_cut_11527

theorem selected_cut_11528 : selected 8 ⟨308113, by decide⟩
    (prefixPartial 13 102698) = some ⟨13, 2, 0, 308113, 102698, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_102698_308113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102698 ⟨308113, by decide⟩ :=
  accepted_of_selected 13 102698 ⟨308113, by decide⟩ ⟨13, 2, 0, 308113, 102698, 1497, 16384⟩
    (by decide) selected_cut_11528

theorem selected_cut_11529 : selected 8 ⟨308130, by decide⟩
    (prefixPartial 13 102699) = some ⟨13, 2, 0, 308130, 102699, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_102699_308130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102699 ⟨308130, by decide⟩ :=
  accepted_of_selected 13 102699 ⟨308130, by decide⟩ ⟨13, 2, 0, 308130, 102699, 1037, 16384⟩
    (by decide) selected_cut_11529

theorem unmarked_context_12_25674_308131 : frontier 9 ⟨308131, by decide⟩
    (prefixCache 12 25674) (prefixPartial 12 25674) = false := by
  decide +kernel

theorem node_context_12_25674_308131 : EJMOriginalGlobalDAGData.nodes 9 ⟨308131, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨308089, by decide⟩,⟨308113, by decide⟩,⟨308130, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25674_308131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25674 ⟨308131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25674
    ⟨308131, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨308089, by decide⟩,⟨308113, by decide⟩,⟨308130, by decide⟩]) unmarked_context_12_25674_308131 node_context_12_25674_308131
  intro a
  fin_cases a
  · exact context_13_102696_3444
  · exact context_13_102697_308089
  · exact context_13_102698_308113
  · exact context_13_102699_308130

theorem selected_cut_11530 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102700) = some ⟨13, 1, 0, 3444, 102700, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102700_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102700 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102700 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102700, 1, 16384⟩
    (by decide) selected_cut_11530

theorem selected_cut_11531 : selected 8 ⟨308166, by decide⟩
    (prefixPartial 13 102701) = some ⟨13, 2, 0, 308166, 102701, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_102701_308166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102701 ⟨308166, by decide⟩ :=
  accepted_of_selected 13 102701 ⟨308166, by decide⟩ ⟨13, 2, 0, 308166, 102701, 2445, 16384⟩
    (by decide) selected_cut_11531

theorem selected_cut_11532 : selected 8 ⟨308188, by decide⟩
    (prefixPartial 13 102702) = some ⟨13, 2, 0, 308188, 102702, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_102702_308188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102702 ⟨308188, by decide⟩ :=
  accepted_of_selected 13 102702 ⟨308188, by decide⟩ ⟨13, 2, 0, 308188, 102702, 1757, 16384⟩
    (by decide) selected_cut_11532

theorem selected_cut_11533 : selected 8 ⟨308205, by decide⟩
    (prefixPartial 13 102703) = some ⟨13, 2, 0, 308205, 102703, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_102703_308205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102703 ⟨308205, by decide⟩ :=
  accepted_of_selected 13 102703 ⟨308205, by decide⟩ ⟨13, 2, 0, 308205, 102703, 1049, 16384⟩
    (by decide) selected_cut_11533

theorem unmarked_context_12_25675_308206 : frontier 9 ⟨308206, by decide⟩
    (prefixCache 12 25675) (prefixPartial 12 25675) = false := by
  decide +kernel

theorem node_context_12_25675_308206 : EJMOriginalGlobalDAGData.nodes 9 ⟨308206, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨308166, by decide⟩,⟨308188, by decide⟩,⟨308205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25675_308206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25675 ⟨308206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25675
    ⟨308206, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨308166, by decide⟩,⟨308188, by decide⟩,⟨308205, by decide⟩]) unmarked_context_12_25675_308206 node_context_12_25675_308206
  intro a
  fin_cases a
  · exact context_13_102700_3444
  · exact context_13_102701_308166
  · exact context_13_102702_308188
  · exact context_13_102703_308205

theorem unmarked_context_11_6418_308207 : frontier 10 ⟨308207, by decide⟩
    (prefixCache 11 6418) (prefixPartial 11 6418) = false := by
  decide +kernel

theorem node_context_11_6418_308207 : EJMOriginalGlobalDAGData.nodes 10 ⟨308207, by decide⟩ =
    .split (coordinate 11) (![⟨307916, by decide⟩,⟨308057, by decide⟩,⟨308131, by decide⟩,⟨308206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6418_308207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6418 ⟨308207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6418
    ⟨308207, by decide⟩ (by decide) (![⟨307916, by decide⟩,⟨308057, by decide⟩,⟨308131, by decide⟩,⟨308206, by decide⟩]) unmarked_context_11_6418_308207 node_context_11_6418_308207
  intro a
  fin_cases a
  · exact context_12_25672_307916
  · exact context_12_25673_308057
  · exact context_12_25674_308131
  · exact context_12_25675_308206

theorem selected_cut_11534 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102704) = some ⟨13, 1, 0, 3444, 102704, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102704_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102704 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102704 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102704, 1, 16384⟩
    (by decide) selected_cut_11534

theorem selected_cut_11535 : selected 8 ⟨308234, by decide⟩
    (prefixPartial 13 102705) = some ⟨13, 2, 0, 308234, 102705, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_102705_308234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102705 ⟨308234, by decide⟩ :=
  accepted_of_selected 13 102705 ⟨308234, by decide⟩ ⟨13, 2, 0, 308234, 102705, 1873, 16384⟩
    (by decide) selected_cut_11535

theorem selected_cut_11536 : selected 8 ⟨308255, by decide⟩
    (prefixPartial 13 102706) = some ⟨13, 2, 0, 308255, 102706, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_102706_308255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102706 ⟨308255, by decide⟩ :=
  accepted_of_selected 13 102706 ⟨308255, by decide⟩ ⟨13, 2, 0, 308255, 102706, 1525, 16384⟩
    (by decide) selected_cut_11536

theorem selected_cut_11537 : selected 8 ⟨308266, by decide⟩
    (prefixPartial 13 102707) = some ⟨13, 2, 0, 308266, 102707, 897, 16384⟩ := by
  decide +kernel

theorem context_13_102707_308266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102707 ⟨308266, by decide⟩ :=
  accepted_of_selected 13 102707 ⟨308266, by decide⟩ ⟨13, 2, 0, 308266, 102707, 897, 16384⟩
    (by decide) selected_cut_11537

theorem unmarked_context_12_25676_308267 : frontier 9 ⟨308267, by decide⟩
    (prefixCache 12 25676) (prefixPartial 12 25676) = false := by
  decide +kernel

theorem node_context_12_25676_308267 : EJMOriginalGlobalDAGData.nodes 9 ⟨308267, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨308234, by decide⟩,⟨308255, by decide⟩,⟨308266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25676_308267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25676 ⟨308267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25676
    ⟨308267, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨308234, by decide⟩,⟨308255, by decide⟩,⟨308266, by decide⟩]) unmarked_context_12_25676_308267 node_context_12_25676_308267
  intro a
  fin_cases a
  · exact context_13_102704_3444
  · exact context_13_102705_308234
  · exact context_13_102706_308255
  · exact context_13_102707_308266

theorem selected_cut_11538 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102708) = some ⟨13, 1, 0, 3444, 102708, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102708_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102708 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102708 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102708, 1, 16384⟩
    (by decide) selected_cut_11538

theorem selected_cut_11539 : selected 8 ⟨308316, by decide⟩
    (prefixPartial 13 102709) = some ⟨13, 2, 0, 308316, 102709, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_102709_308316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102709 ⟨308316, by decide⟩ :=
  accepted_of_selected 13 102709 ⟨308316, by decide⟩ ⟨13, 2, 0, 308316, 102709, 2713, 16384⟩
    (by decide) selected_cut_11539

theorem selected_cut_11540 : selected 8 ⟨308348, by decide⟩
    (prefixPartial 13 102710) = some ⟨13, 2, 0, 308348, 102710, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_102710_308348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102710 ⟨308348, by decide⟩ :=
  accepted_of_selected 13 102710 ⟨308348, by decide⟩ ⟨13, 2, 0, 308348, 102710, 2265, 16384⟩
    (by decide) selected_cut_11540

theorem selected_cut_11541 : selected 8 ⟨308364, by decide⟩
    (prefixPartial 13 102711) = some ⟨13, 2, 0, 308364, 102711, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_102711_308364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102711 ⟨308364, by decide⟩ :=
  accepted_of_selected 13 102711 ⟨308364, by decide⟩ ⟨13, 2, 0, 308364, 102711, 1129, 16384⟩
    (by decide) selected_cut_11541

theorem unmarked_context_12_25677_308365 : frontier 9 ⟨308365, by decide⟩
    (prefixCache 12 25677) (prefixPartial 12 25677) = false := by
  decide +kernel

theorem node_context_12_25677_308365 : EJMOriginalGlobalDAGData.nodes 9 ⟨308365, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨308316, by decide⟩,⟨308348, by decide⟩,⟨308364, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25677_308365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25677 ⟨308365, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25677
    ⟨308365, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨308316, by decide⟩,⟨308348, by decide⟩,⟨308364, by decide⟩]) unmarked_context_12_25677_308365 node_context_12_25677_308365
  intro a
  fin_cases a
  · exact context_13_102708_3444
  · exact context_13_102709_308316
  · exact context_13_102710_308348
  · exact context_13_102711_308364

theorem selected_cut_11542 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102712) = some ⟨13, 1, 0, 3444, 102712, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102712_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102712 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102712 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102712, 1, 16384⟩
    (by decide) selected_cut_11542

theorem selected_cut_11543 : selected 8 ⟨308391, by decide⟩
    (prefixPartial 13 102713) = some ⟨13, 2, 0, 308391, 102713, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_102713_308391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102713 ⟨308391, by decide⟩ :=
  accepted_of_selected 13 102713 ⟨308391, by decide⟩ ⟨13, 2, 0, 308391, 102713, 1945, 16384⟩
    (by decide) selected_cut_11543

theorem selected_cut_11544 : selected 8 ⟨308412, by decide⟩
    (prefixPartial 13 102714) = some ⟨13, 2, 0, 308412, 102714, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_102714_308412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102714 ⟨308412, by decide⟩ :=
  accepted_of_selected 13 102714 ⟨308412, by decide⟩ ⟨13, 2, 0, 308412, 102714, 1717, 16384⟩
    (by decide) selected_cut_11544

theorem selected_cut_11545 : selected 8 ⟨308422, by decide⟩
    (prefixPartial 13 102715) = some ⟨13, 2, 0, 308422, 102715, 913, 16384⟩ := by
  decide +kernel

theorem context_13_102715_308422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102715 ⟨308422, by decide⟩ :=
  accepted_of_selected 13 102715 ⟨308422, by decide⟩ ⟨13, 2, 0, 308422, 102715, 913, 16384⟩
    (by decide) selected_cut_11545

theorem unmarked_context_12_25678_308423 : frontier 9 ⟨308423, by decide⟩
    (prefixCache 12 25678) (prefixPartial 12 25678) = false := by
  decide +kernel

theorem node_context_12_25678_308423 : EJMOriginalGlobalDAGData.nodes 9 ⟨308423, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨308391, by decide⟩,⟨308412, by decide⟩,⟨308422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25678_308423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25678 ⟨308423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25678
    ⟨308423, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨308391, by decide⟩,⟨308412, by decide⟩,⟨308422, by decide⟩]) unmarked_context_12_25678_308423 node_context_12_25678_308423
  intro a
  fin_cases a
  · exact context_13_102712_3444
  · exact context_13_102713_308391
  · exact context_13_102714_308412
  · exact context_13_102715_308422

theorem selected_cut_11546 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102716) = some ⟨13, 1, 0, 3444, 102716, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102716_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102716 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102716 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102716, 1, 16384⟩
    (by decide) selected_cut_11546

theorem selected_cut_11547 : selected 8 ⟨308446, by decide⟩
    (prefixPartial 13 102717) = some ⟨13, 2, 0, 308446, 102717, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_102717_308446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102717 ⟨308446, by decide⟩ :=
  accepted_of_selected 13 102717 ⟨308446, by decide⟩ ⟨13, 2, 0, 308446, 102717, 1973, 16384⟩
    (by decide) selected_cut_11547

theorem selected_cut_11548 : selected 8 ⟨308470, by decide⟩
    (prefixPartial 13 102718) = some ⟨13, 2, 0, 308470, 102718, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_102718_308470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102718 ⟨308470, by decide⟩ :=
  accepted_of_selected 13 102718 ⟨308470, by decide⟩ ⟨13, 2, 0, 308470, 102718, 1681, 16384⟩
    (by decide) selected_cut_11548

theorem selected_cut_11549 : selected 8 ⟨308477, by decide⟩
    (prefixPartial 13 102719) = some ⟨13, 2, 0, 308477, 102719, 845, 16384⟩ := by
  decide +kernel

theorem context_13_102719_308477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102719 ⟨308477, by decide⟩ :=
  accepted_of_selected 13 102719 ⟨308477, by decide⟩ ⟨13, 2, 0, 308477, 102719, 845, 16384⟩
    (by decide) selected_cut_11549

theorem unmarked_context_12_25679_308478 : frontier 9 ⟨308478, by decide⟩
    (prefixCache 12 25679) (prefixPartial 12 25679) = false := by
  decide +kernel

theorem node_context_12_25679_308478 : EJMOriginalGlobalDAGData.nodes 9 ⟨308478, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨308446, by decide⟩,⟨308470, by decide⟩,⟨308477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25679_308478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25679 ⟨308478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25679
    ⟨308478, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨308446, by decide⟩,⟨308470, by decide⟩,⟨308477, by decide⟩]) unmarked_context_12_25679_308478 node_context_12_25679_308478
  intro a
  fin_cases a
  · exact context_13_102716_3444
  · exact context_13_102717_308446
  · exact context_13_102718_308470
  · exact context_13_102719_308477

theorem unmarked_context_11_6419_308479 : frontier 10 ⟨308479, by decide⟩
    (prefixCache 11 6419) (prefixPartial 11 6419) = false := by
  decide +kernel

theorem node_context_11_6419_308479 : EJMOriginalGlobalDAGData.nodes 10 ⟨308479, by decide⟩ =
    .split (coordinate 11) (![⟨308267, by decide⟩,⟨308365, by decide⟩,⟨308423, by decide⟩,⟨308478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6419_308479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6419 ⟨308479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6419
    ⟨308479, by decide⟩ (by decide) (![⟨308267, by decide⟩,⟨308365, by decide⟩,⟨308423, by decide⟩,⟨308478, by decide⟩]) unmarked_context_11_6419_308479 node_context_11_6419_308479
  intro a
  fin_cases a
  · exact context_12_25676_308267
  · exact context_12_25677_308365
  · exact context_12_25678_308423
  · exact context_12_25679_308478

theorem unmarked_context_10_1604_308480 : frontier 11 ⟨308480, by decide⟩
    (prefixCache 10 1604) (prefixPartial 10 1604) = false := by
  decide +kernel

theorem node_context_10_1604_308480 : EJMOriginalGlobalDAGData.nodes 11 ⟨308480, by decide⟩ =
    .split (coordinate 10) (![⟨307617, by decide⟩,⟨307838, by decide⟩,⟨308207, by decide⟩,⟨308479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1604_308480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1604 ⟨308480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1604
    ⟨308480, by decide⟩ (by decide) (![⟨307617, by decide⟩,⟨307838, by decide⟩,⟨308207, by decide⟩,⟨308479, by decide⟩]) unmarked_context_10_1604_308480 node_context_10_1604_308480
  intro a
  fin_cases a
  · exact context_11_6416_307617
  · exact context_11_6417_307838
  · exact context_11_6418_308207
  · exact context_11_6419_308479

theorem selected_cut_11550 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102720) = some ⟨13, 1, 0, 3444, 102720, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102720_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102720 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102720 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102720, 1, 16384⟩
    (by decide) selected_cut_11550

theorem selected_cut_11551 : selected 8 ⟨308541, by decide⟩
    (prefixPartial 13 102721) = some ⟨13, 2, 0, 308541, 102721, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_102721_308541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102721 ⟨308541, by decide⟩ :=
  accepted_of_selected 13 102721 ⟨308541, by decide⟩ ⟨13, 2, 0, 308541, 102721, 2469, 16384⟩
    (by decide) selected_cut_11551

theorem selected_cut_11552 : selected 8 ⟨308595, by decide⟩
    (prefixPartial 13 102722) = some ⟨13, 2, 0, 308595, 102722, 2585, 16384⟩ := by
  decide +kernel

theorem context_13_102722_308595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102722 ⟨308595, by decide⟩ :=
  accepted_of_selected 13 102722 ⟨308595, by decide⟩ ⟨13, 2, 0, 308595, 102722, 2585, 16384⟩
    (by decide) selected_cut_11552

theorem selected_cut_11553 : selected 8 ⟨308607, by decide⟩
    (prefixPartial 13 102723) = some ⟨13, 2, 0, 308607, 102723, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_102723_308607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102723 ⟨308607, by decide⟩ :=
  accepted_of_selected 13 102723 ⟨308607, by decide⟩ ⟨13, 2, 0, 308607, 102723, 1209, 16384⟩
    (by decide) selected_cut_11553

theorem unmarked_context_12_25680_308608 : frontier 9 ⟨308608, by decide⟩
    (prefixCache 12 25680) (prefixPartial 12 25680) = false := by
  decide +kernel

theorem node_context_12_25680_308608 : EJMOriginalGlobalDAGData.nodes 9 ⟨308608, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨308541, by decide⟩,⟨308595, by decide⟩,⟨308607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25680_308608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25680 ⟨308608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25680
    ⟨308608, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨308541, by decide⟩,⟨308595, by decide⟩,⟨308607, by decide⟩]) unmarked_context_12_25680_308608 node_context_12_25680_308608
  intro a
  fin_cases a
  · exact context_13_102720_3444
  · exact context_13_102721_308541
  · exact context_13_102722_308595
  · exact context_13_102723_308607

theorem selected_cut_11554 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 25681) = some ⟨12, 1, 0, 170504, 25681, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25681_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25681 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 25681 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 25681, 1, 65536⟩
    (by decide) selected_cut_11554

theorem selected_cut_11555 : selected 9 ⟨308654, by decide⟩
    (prefixPartial 12 25682) = some ⟨12, 2, 0, 308654, 25682, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_25682_308654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25682 ⟨308654, by decide⟩ :=
  accepted_of_selected 12 25682 ⟨308654, by decide⟩ ⟨12, 2, 0, 308654, 25682, 3973, 65536⟩
    (by decide) selected_cut_11555

theorem selected_cut_11556 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102732) = some ⟨13, 1, 0, 3444, 102732, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102732_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102732 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102732 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102732, 1, 16384⟩
    (by decide) selected_cut_11556

theorem selected_cut_11557 : selected 8 ⟨308674, by decide⟩
    (prefixPartial 13 102733) = some ⟨13, 2, 0, 308674, 102733, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_102733_308674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102733 ⟨308674, by decide⟩ :=
  accepted_of_selected 13 102733 ⟨308674, by decide⟩ ⟨13, 2, 0, 308674, 102733, 1621, 16384⟩
    (by decide) selected_cut_11557

theorem selected_cut_11558 : selected 8 ⟨308696, by decide⟩
    (prefixPartial 13 102734) = some ⟨13, 2, 0, 308696, 102734, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_102734_308696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102734 ⟨308696, by decide⟩ :=
  accepted_of_selected 13 102734 ⟨308696, by decide⟩ ⟨13, 2, 0, 308696, 102734, 1725, 16384⟩
    (by decide) selected_cut_11558

theorem selected_cut_11559 : selected 8 ⟨308702, by decide⟩
    (prefixPartial 13 102735) = some ⟨13, 2, 0, 308702, 102735, 793, 16384⟩ := by
  decide +kernel

theorem context_13_102735_308702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102735 ⟨308702, by decide⟩ :=
  accepted_of_selected 13 102735 ⟨308702, by decide⟩ ⟨13, 2, 0, 308702, 102735, 793, 16384⟩
    (by decide) selected_cut_11559

theorem unmarked_context_12_25683_308703 : frontier 9 ⟨308703, by decide⟩
    (prefixCache 12 25683) (prefixPartial 12 25683) = false := by
  decide +kernel

theorem node_context_12_25683_308703 : EJMOriginalGlobalDAGData.nodes 9 ⟨308703, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨308674, by decide⟩,⟨308696, by decide⟩,⟨308702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25683_308703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25683 ⟨308703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25683
    ⟨308703, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨308674, by decide⟩,⟨308696, by decide⟩,⟨308702, by decide⟩]) unmarked_context_12_25683_308703 node_context_12_25683_308703
  intro a
  fin_cases a
  · exact context_13_102732_3444
  · exact context_13_102733_308674
  · exact context_13_102734_308696
  · exact context_13_102735_308702

theorem unmarked_context_11_6420_308704 : frontier 10 ⟨308704, by decide⟩
    (prefixCache 11 6420) (prefixPartial 11 6420) = false := by
  decide +kernel

theorem node_context_11_6420_308704 : EJMOriginalGlobalDAGData.nodes 10 ⟨308704, by decide⟩ =
    .split (coordinate 11) (![⟨308608, by decide⟩,⟨170504, by decide⟩,⟨308654, by decide⟩,⟨308703, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6420_308704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6420 ⟨308704, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6420
    ⟨308704, by decide⟩ (by decide) (![⟨308608, by decide⟩,⟨170504, by decide⟩,⟨308654, by decide⟩,⟨308703, by decide⟩]) unmarked_context_11_6420_308704 node_context_11_6420_308704
  intro a
  fin_cases a
  · exact context_12_25680_308608
  · exact context_12_25681_170504
  · exact context_12_25682_308654
  · exact context_12_25683_308703

theorem selected_cut_11560 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 25684) = some ⟨12, 1, 0, 308705, 25684, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25684_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25684 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 25684 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 25684, 1, 65536⟩
    (by decide) selected_cut_11560

theorem selected_cut_11561 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 25685) = some ⟨12, 1, 0, 170504, 25685, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25685_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25685 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 25685 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 25685, 1, 65536⟩
    (by decide) selected_cut_11561

theorem selected_cut_11562 : selected 9 ⟨308858, by decide⟩
    (prefixPartial 12 25686) = some ⟨12, 2, 0, 308858, 25686, 3849, 65536⟩ := by
  decide +kernel

theorem context_12_25686_308858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25686 ⟨308858, by decide⟩ :=
  accepted_of_selected 12 25686 ⟨308858, by decide⟩ ⟨12, 2, 0, 308858, 25686, 3849, 65536⟩
    (by decide) selected_cut_11562

theorem selected_cut_11563 : selected 9 ⟨309021, by decide⟩
    (prefixPartial 12 25687) = some ⟨12, 2, 0, 309021, 25687, 4045, 65536⟩ := by
  decide +kernel

theorem context_12_25687_309021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25687 ⟨309021, by decide⟩ :=
  accepted_of_selected 12 25687 ⟨309021, by decide⟩ ⟨12, 2, 0, 309021, 25687, 4045, 65536⟩
    (by decide) selected_cut_11563

theorem unmarked_context_11_6421_309022 : frontier 10 ⟨309022, by decide⟩
    (prefixCache 11 6421) (prefixPartial 11 6421) = false := by
  decide +kernel

theorem node_context_11_6421_309022 : EJMOriginalGlobalDAGData.nodes 10 ⟨309022, by decide⟩ =
    .split (coordinate 11) (![⟨308705, by decide⟩,⟨170504, by decide⟩,⟨308858, by decide⟩,⟨309021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6421_309022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6421 ⟨309022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6421
    ⟨309022, by decide⟩ (by decide) (![⟨308705, by decide⟩,⟨170504, by decide⟩,⟨308858, by decide⟩,⟨309021, by decide⟩]) unmarked_context_11_6421_309022 node_context_11_6421_309022
  intro a
  fin_cases a
  · exact context_12_25684_308705
  · exact context_12_25685_170504
  · exact context_12_25686_308858
  · exact context_12_25687_309021

theorem selected_cut_11564 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102752) = some ⟨13, 1, 0, 3444, 102752, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102752_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102752 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102752 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102752, 1, 16384⟩
    (by decide) selected_cut_11564

theorem selected_cut_11565 : selected 8 ⟨309044, by decide⟩
    (prefixPartial 13 102753) = some ⟨13, 2, 0, 309044, 102753, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_102753_309044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102753 ⟨309044, by decide⟩ :=
  accepted_of_selected 13 102753 ⟨309044, by decide⟩ ⟨13, 2, 0, 309044, 102753, 1289, 16384⟩
    (by decide) selected_cut_11565

theorem selected_cut_11566 : selected 8 ⟨309069, by decide⟩
    (prefixPartial 13 102754) = some ⟨13, 2, 0, 309069, 102754, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_102754_309069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102754 ⟨309069, by decide⟩ :=
  accepted_of_selected 13 102754 ⟨309069, by decide⟩ ⟨13, 2, 0, 309069, 102754, 1809, 16384⟩
    (by decide) selected_cut_11566

theorem selected_cut_11567 : selected 8 ⟨309077, by decide⟩
    (prefixPartial 13 102755) = some ⟨13, 2, 0, 309077, 102755, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_102755_309077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102755 ⟨309077, by decide⟩ :=
  accepted_of_selected 13 102755 ⟨309077, by decide⟩ ⟨13, 2, 0, 309077, 102755, 1013, 16384⟩
    (by decide) selected_cut_11567

theorem unmarked_context_12_25688_309078 : frontier 9 ⟨309078, by decide⟩
    (prefixCache 12 25688) (prefixPartial 12 25688) = false := by
  decide +kernel

theorem node_context_12_25688_309078 : EJMOriginalGlobalDAGData.nodes 9 ⟨309078, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309044, by decide⟩,⟨309069, by decide⟩,⟨309077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25688_309078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25688 ⟨309078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25688
    ⟨309078, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309044, by decide⟩,⟨309069, by decide⟩,⟨309077, by decide⟩]) unmarked_context_12_25688_309078 node_context_12_25688_309078
  intro a
  fin_cases a
  · exact context_13_102752_3444
  · exact context_13_102753_309044
  · exact context_13_102754_309069
  · exact context_13_102755_309077

theorem selected_cut_11568 : selected 9 ⟨309150, by decide⟩
    (prefixPartial 12 25689) = some ⟨12, 2, 0, 309150, 25689, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_25689_309150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25689 ⟨309150, by decide⟩ :=
  accepted_of_selected 12 25689 ⟨309150, by decide⟩ ⟨12, 2, 0, 309150, 25689, 2433, 65536⟩
    (by decide) selected_cut_11568

theorem selected_cut_11569 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102760) = some ⟨13, 1, 0, 3444, 102760, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102760_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102760 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102760 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102760, 1, 16384⟩
    (by decide) selected_cut_11569

theorem selected_cut_11570 : selected 8 ⟨309164, by decide⟩
    (prefixPartial 13 102761) = some ⟨13, 2, 0, 309164, 102761, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_102761_309164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102761 ⟨309164, by decide⟩ :=
  accepted_of_selected 13 102761 ⟨309164, by decide⟩ ⟨13, 2, 0, 309164, 102761, 1333, 16384⟩
    (by decide) selected_cut_11570

theorem selected_cut_11571 : selected 8 ⟨309188, by decide⟩
    (prefixPartial 13 102762) = some ⟨13, 2, 0, 309188, 102762, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_102762_309188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102762 ⟨309188, by decide⟩ :=
  accepted_of_selected 13 102762 ⟨309188, by decide⟩ ⟨13, 2, 0, 309188, 102762, 1729, 16384⟩
    (by decide) selected_cut_11571

theorem selected_cut_11572 : selected 8 ⟨309198, by decide⟩
    (prefixPartial 13 102763) = some ⟨13, 2, 0, 309198, 102763, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_102763_309198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102763 ⟨309198, by decide⟩ :=
  accepted_of_selected 13 102763 ⟨309198, by decide⟩ ⟨13, 2, 0, 309198, 102763, 1133, 16384⟩
    (by decide) selected_cut_11572

theorem unmarked_context_12_25690_309199 : frontier 9 ⟨309199, by decide⟩
    (prefixCache 12 25690) (prefixPartial 12 25690) = false := by
  decide +kernel

theorem node_context_12_25690_309199 : EJMOriginalGlobalDAGData.nodes 9 ⟨309199, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309164, by decide⟩,⟨309188, by decide⟩,⟨309198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25690_309199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25690 ⟨309199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25690
    ⟨309199, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309164, by decide⟩,⟨309188, by decide⟩,⟨309198, by decide⟩]) unmarked_context_12_25690_309199 node_context_12_25690_309199
  intro a
  fin_cases a
  · exact context_13_102760_3444
  · exact context_13_102761_309164
  · exact context_13_102762_309188
  · exact context_13_102763_309198

theorem selected_cut_11573 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102764) = some ⟨13, 1, 0, 3444, 102764, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102764_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102764 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102764 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102764, 1, 16384⟩
    (by decide) selected_cut_11573

theorem selected_cut_11574 : selected 8 ⟨309216, by decide⟩
    (prefixPartial 13 102765) = some ⟨13, 2, 0, 309216, 102765, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_102765_309216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102765 ⟨309216, by decide⟩ :=
  accepted_of_selected 13 102765 ⟨309216, by decide⟩ ⟨13, 2, 0, 309216, 102765, 1397, 16384⟩
    (by decide) selected_cut_11574

theorem selected_cut_11575 : selected 8 ⟨309240, by decide⟩
    (prefixPartial 13 102766) = some ⟨13, 2, 0, 309240, 102766, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_102766_309240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102766 ⟨309240, by decide⟩ :=
  accepted_of_selected 13 102766 ⟨309240, by decide⟩ ⟨13, 2, 0, 309240, 102766, 2021, 16384⟩
    (by decide) selected_cut_11575

theorem selected_cut_11576 : selected 8 ⟨309250, by decide⟩
    (prefixPartial 13 102767) = some ⟨13, 2, 0, 309250, 102767, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_102767_309250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102767 ⟨309250, by decide⟩ :=
  accepted_of_selected 13 102767 ⟨309250, by decide⟩ ⟨13, 2, 0, 309250, 102767, 1117, 16384⟩
    (by decide) selected_cut_11576

theorem unmarked_context_12_25691_309251 : frontier 9 ⟨309251, by decide⟩
    (prefixCache 12 25691) (prefixPartial 12 25691) = false := by
  decide +kernel

theorem node_context_12_25691_309251 : EJMOriginalGlobalDAGData.nodes 9 ⟨309251, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309216, by decide⟩,⟨309240, by decide⟩,⟨309250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25691_309251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25691 ⟨309251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25691
    ⟨309251, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309216, by decide⟩,⟨309240, by decide⟩,⟨309250, by decide⟩]) unmarked_context_12_25691_309251 node_context_12_25691_309251
  intro a
  fin_cases a
  · exact context_13_102764_3444
  · exact context_13_102765_309216
  · exact context_13_102766_309240
  · exact context_13_102767_309250

theorem unmarked_context_11_6422_309252 : frontier 10 ⟨309252, by decide⟩
    (prefixCache 11 6422) (prefixPartial 11 6422) = false := by
  decide +kernel

theorem node_context_11_6422_309252 : EJMOriginalGlobalDAGData.nodes 10 ⟨309252, by decide⟩ =
    .split (coordinate 11) (![⟨309078, by decide⟩,⟨309150, by decide⟩,⟨309199, by decide⟩,⟨309251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6422_309252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6422 ⟨309252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6422
    ⟨309252, by decide⟩ (by decide) (![⟨309078, by decide⟩,⟨309150, by decide⟩,⟨309199, by decide⟩,⟨309251, by decide⟩]) unmarked_context_11_6422_309252 node_context_11_6422_309252
  intro a
  fin_cases a
  · exact context_12_25688_309078
  · exact context_12_25689_309150
  · exact context_12_25690_309199
  · exact context_12_25691_309251

theorem selected_cut_11577 : selected 9 ⟨309307, by decide⟩
    (prefixPartial 12 25692) = some ⟨12, 2, 0, 309307, 25692, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_25692_309307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25692 ⟨309307, by decide⟩ :=
  accepted_of_selected 12 25692 ⟨309307, by decide⟩ ⟨12, 2, 0, 309307, 25692, 3765, 65536⟩
    (by decide) selected_cut_11577

theorem selected_cut_11578 : selected 9 ⟨309363, by decide⟩
    (prefixPartial 12 25693) = some ⟨12, 2, 0, 309363, 25693, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_25693_309363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25693 ⟨309363, by decide⟩ :=
  accepted_of_selected 12 25693 ⟨309363, by decide⟩ ⟨12, 2, 0, 309363, 25693, 2525, 65536⟩
    (by decide) selected_cut_11578

theorem selected_cut_11579 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102776) = some ⟨13, 1, 0, 3444, 102776, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102776_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102776 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102776 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102776, 1, 16384⟩
    (by decide) selected_cut_11579

theorem selected_cut_11580 : selected 8 ⟨309380, by decide⟩
    (prefixPartial 13 102777) = some ⟨13, 2, 0, 309380, 102777, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_102777_309380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102777 ⟨309380, by decide⟩ :=
  accepted_of_selected 13 102777 ⟨309380, by decide⟩ ⟨13, 2, 0, 309380, 102777, 1361, 16384⟩
    (by decide) selected_cut_11580

theorem selected_cut_11581 : selected 8 ⟨309400, by decide⟩
    (prefixPartial 13 102778) = some ⟨13, 2, 0, 309400, 102778, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_102778_309400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102778 ⟨309400, by decide⟩ :=
  accepted_of_selected 13 102778 ⟨309400, by decide⟩ ⟨13, 2, 0, 309400, 102778, 1933, 16384⟩
    (by decide) selected_cut_11581

theorem selected_cut_11582 : selected 8 ⟨309410, by decide⟩
    (prefixPartial 13 102779) = some ⟨13, 2, 0, 309410, 102779, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_102779_309410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102779 ⟨309410, by decide⟩ :=
  accepted_of_selected 13 102779 ⟨309410, by decide⟩ ⟨13, 2, 0, 309410, 102779, 1049, 16384⟩
    (by decide) selected_cut_11582

theorem unmarked_context_12_25694_309411 : frontier 9 ⟨309411, by decide⟩
    (prefixCache 12 25694) (prefixPartial 12 25694) = false := by
  decide +kernel

theorem node_context_12_25694_309411 : EJMOriginalGlobalDAGData.nodes 9 ⟨309411, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309380, by decide⟩,⟨309400, by decide⟩,⟨309410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25694_309411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25694 ⟨309411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25694
    ⟨309411, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309380, by decide⟩,⟨309400, by decide⟩,⟨309410, by decide⟩]) unmarked_context_12_25694_309411 node_context_12_25694_309411
  intro a
  fin_cases a
  · exact context_13_102776_3444
  · exact context_13_102777_309380
  · exact context_13_102778_309400
  · exact context_13_102779_309410

theorem selected_cut_11583 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102780) = some ⟨13, 1, 0, 3444, 102780, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102780_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102780 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102780 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102780, 1, 16384⟩
    (by decide) selected_cut_11583

theorem selected_cut_11584 : selected 8 ⟨309426, by decide⟩
    (prefixPartial 13 102781) = some ⟨13, 2, 0, 309426, 102781, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_102781_309426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102781 ⟨309426, by decide⟩ :=
  accepted_of_selected 13 102781 ⟨309426, by decide⟩ ⟨13, 2, 0, 309426, 102781, 1345, 16384⟩
    (by decide) selected_cut_11584

theorem selected_cut_11585 : selected 8 ⟨309448, by decide⟩
    (prefixPartial 13 102782) = some ⟨13, 2, 0, 309448, 102782, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_102782_309448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102782 ⟨309448, by decide⟩ :=
  accepted_of_selected 13 102782 ⟨309448, by decide⟩ ⟨13, 2, 0, 309448, 102782, 1925, 16384⟩
    (by decide) selected_cut_11585

theorem selected_cut_11586 : selected 8 ⟨309457, by decide⟩
    (prefixPartial 13 102783) = some ⟨13, 2, 0, 309457, 102783, 941, 16384⟩ := by
  decide +kernel

theorem context_13_102783_309457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102783 ⟨309457, by decide⟩ :=
  accepted_of_selected 13 102783 ⟨309457, by decide⟩ ⟨13, 2, 0, 309457, 102783, 941, 16384⟩
    (by decide) selected_cut_11586

theorem unmarked_context_12_25695_309458 : frontier 9 ⟨309458, by decide⟩
    (prefixCache 12 25695) (prefixPartial 12 25695) = false := by
  decide +kernel

theorem node_context_12_25695_309458 : EJMOriginalGlobalDAGData.nodes 9 ⟨309458, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309426, by decide⟩,⟨309448, by decide⟩,⟨309457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25695_309458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25695 ⟨309458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25695
    ⟨309458, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309426, by decide⟩,⟨309448, by decide⟩,⟨309457, by decide⟩]) unmarked_context_12_25695_309458 node_context_12_25695_309458
  intro a
  fin_cases a
  · exact context_13_102780_3444
  · exact context_13_102781_309426
  · exact context_13_102782_309448
  · exact context_13_102783_309457

theorem unmarked_context_11_6423_309459 : frontier 10 ⟨309459, by decide⟩
    (prefixCache 11 6423) (prefixPartial 11 6423) = false := by
  decide +kernel

theorem node_context_11_6423_309459 : EJMOriginalGlobalDAGData.nodes 10 ⟨309459, by decide⟩ =
    .split (coordinate 11) (![⟨309307, by decide⟩,⟨309363, by decide⟩,⟨309411, by decide⟩,⟨309458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6423_309459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6423 ⟨309459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6423
    ⟨309459, by decide⟩ (by decide) (![⟨309307, by decide⟩,⟨309363, by decide⟩,⟨309411, by decide⟩,⟨309458, by decide⟩]) unmarked_context_11_6423_309459 node_context_11_6423_309459
  intro a
  fin_cases a
  · exact context_12_25692_309307
  · exact context_12_25693_309363
  · exact context_12_25694_309411
  · exact context_12_25695_309458

theorem unmarked_context_10_1605_309460 : frontier 11 ⟨309460, by decide⟩
    (prefixCache 10 1605) (prefixPartial 10 1605) = false := by
  decide +kernel

theorem node_context_10_1605_309460 : EJMOriginalGlobalDAGData.nodes 11 ⟨309460, by decide⟩ =
    .split (coordinate 10) (![⟨308704, by decide⟩,⟨309022, by decide⟩,⟨309252, by decide⟩,⟨309459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1605_309460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1605 ⟨309460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1605
    ⟨309460, by decide⟩ (by decide) (![⟨308704, by decide⟩,⟨309022, by decide⟩,⟨309252, by decide⟩,⟨309459, by decide⟩]) unmarked_context_10_1605_309460 node_context_10_1605_309460
  intro a
  fin_cases a
  · exact context_11_6420_308704
  · exact context_11_6421_309022
  · exact context_11_6422_309252
  · exact context_11_6423_309459

theorem selected_cut_11587 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102784) = some ⟨13, 1, 0, 3444, 102784, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102784_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102784 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102784 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102784, 1, 16384⟩
    (by decide) selected_cut_11587

theorem selected_cut_11588 : selected 8 ⟨309523, by decide⟩
    (prefixPartial 13 102785) = some ⟨13, 2, 0, 309523, 102785, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_102785_309523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102785 ⟨309523, by decide⟩ :=
  accepted_of_selected 13 102785 ⟨309523, by decide⟩ ⟨13, 2, 0, 309523, 102785, 2265, 16384⟩
    (by decide) selected_cut_11588

theorem selected_cut_11589 : selected 8 ⟨309564, by decide⟩
    (prefixPartial 13 102786) = some ⟨13, 2, 0, 309564, 102786, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_102786_309564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102786 ⟨309564, by decide⟩ :=
  accepted_of_selected 13 102786 ⟨309564, by decide⟩ ⟨13, 2, 0, 309564, 102786, 2609, 16384⟩
    (by decide) selected_cut_11589

theorem selected_cut_11590 : selected 8 ⟨309576, by decide⟩
    (prefixPartial 13 102787) = some ⟨13, 2, 0, 309576, 102787, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_102787_309576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102787 ⟨309576, by decide⟩ :=
  accepted_of_selected 13 102787 ⟨309576, by decide⟩ ⟨13, 2, 0, 309576, 102787, 1297, 16384⟩
    (by decide) selected_cut_11590

theorem unmarked_context_12_25696_309577 : frontier 9 ⟨309577, by decide⟩
    (prefixCache 12 25696) (prefixPartial 12 25696) = false := by
  decide +kernel

theorem node_context_12_25696_309577 : EJMOriginalGlobalDAGData.nodes 9 ⟨309577, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309523, by decide⟩,⟨309564, by decide⟩,⟨309576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25696_309577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25696 ⟨309577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25696
    ⟨309577, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309523, by decide⟩,⟨309564, by decide⟩,⟨309576, by decide⟩]) unmarked_context_12_25696_309577 node_context_12_25696_309577
  intro a
  fin_cases a
  · exact context_13_102784_3444
  · exact context_13_102785_309523
  · exact context_13_102786_309564
  · exact context_13_102787_309576

theorem selected_cut_11591 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102788) = some ⟨13, 1, 0, 3444, 102788, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102788_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102788 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102788 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102788, 1, 16384⟩
    (by decide) selected_cut_11591

theorem selected_cut_11592 : selected 8 ⟨309614, by decide⟩
    (prefixPartial 13 102789) = some ⟨13, 2, 0, 309614, 102789, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_102789_309614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102789 ⟨309614, by decide⟩ :=
  accepted_of_selected 13 102789 ⟨309614, by decide⟩ ⟨13, 2, 0, 309614, 102789, 1881, 16384⟩
    (by decide) selected_cut_11592

theorem selected_cut_11593 : selected 8 ⟨309650, by decide⟩
    (prefixPartial 13 102790) = some ⟨13, 2, 0, 309650, 102790, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_102790_309650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102790 ⟨309650, by decide⟩ :=
  accepted_of_selected 13 102790 ⟨309650, by decide⟩ ⟨13, 2, 0, 309650, 102790, 2301, 16384⟩
    (by decide) selected_cut_11593

theorem selected_cut_11594 : selected 8 ⟨309676, by decide⟩
    (prefixPartial 13 102791) = some ⟨13, 2, 0, 309676, 102791, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_102791_309676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102791 ⟨309676, by decide⟩ :=
  accepted_of_selected 13 102791 ⟨309676, by decide⟩ ⟨13, 2, 0, 309676, 102791, 1353, 16384⟩
    (by decide) selected_cut_11594

theorem unmarked_context_12_25697_309677 : frontier 9 ⟨309677, by decide⟩
    (prefixCache 12 25697) (prefixPartial 12 25697) = false := by
  decide +kernel

theorem node_context_12_25697_309677 : EJMOriginalGlobalDAGData.nodes 9 ⟨309677, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309614, by decide⟩,⟨309650, by decide⟩,⟨309676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25697_309677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25697 ⟨309677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25697
    ⟨309677, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309614, by decide⟩,⟨309650, by decide⟩,⟨309676, by decide⟩]) unmarked_context_12_25697_309677 node_context_12_25697_309677
  intro a
  fin_cases a
  · exact context_13_102788_3444
  · exact context_13_102789_309614
  · exact context_13_102790_309650
  · exact context_13_102791_309676

theorem selected_cut_11595 : selected 9 ⟨309733, by decide⟩
    (prefixPartial 12 25698) = some ⟨12, 2, 0, 309733, 25698, 3717, 65536⟩ := by
  decide +kernel

theorem context_12_25698_309733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25698 ⟨309733, by decide⟩ :=
  accepted_of_selected 12 25698 ⟨309733, by decide⟩ ⟨12, 2, 0, 309733, 25698, 3717, 65536⟩
    (by decide) selected_cut_11595

theorem selected_cut_11596 : selected 9 ⟨309781, by decide⟩
    (prefixPartial 12 25699) = some ⟨12, 2, 0, 309781, 25699, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_25699_309781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25699 ⟨309781, by decide⟩ :=
  accepted_of_selected 12 25699 ⟨309781, by decide⟩ ⟨12, 2, 0, 309781, 25699, 3757, 65536⟩
    (by decide) selected_cut_11596

theorem unmarked_context_11_6424_309782 : frontier 10 ⟨309782, by decide⟩
    (prefixCache 11 6424) (prefixPartial 11 6424) = false := by
  decide +kernel

theorem node_context_11_6424_309782 : EJMOriginalGlobalDAGData.nodes 10 ⟨309782, by decide⟩ =
    .split (coordinate 11) (![⟨309577, by decide⟩,⟨309677, by decide⟩,⟨309733, by decide⟩,⟨309781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6424_309782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6424 ⟨309782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6424
    ⟨309782, by decide⟩ (by decide) (![⟨309577, by decide⟩,⟨309677, by decide⟩,⟨309733, by decide⟩,⟨309781, by decide⟩]) unmarked_context_11_6424_309782 node_context_11_6424_309782
  intro a
  fin_cases a
  · exact context_12_25696_309577
  · exact context_12_25697_309677
  · exact context_12_25698_309733
  · exact context_12_25699_309781

theorem selected_cut_11597 : selected 9 ⟨309829, by decide⟩
    (prefixPartial 12 25700) = some ⟨12, 2, 0, 309829, 25700, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_25700_309829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25700 ⟨309829, by decide⟩ :=
  accepted_of_selected 12 25700 ⟨309829, by decide⟩ ⟨12, 2, 0, 309829, 25700, 3497, 65536⟩
    (by decide) selected_cut_11597

theorem selected_cut_11598 : selected 9 ⟨309830, by decide⟩
    (prefixPartial 12 25701) = some ⟨12, 1, 0, 309830, 25701, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25701_309830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25701 ⟨309830, by decide⟩ :=
  accepted_of_selected 12 25701 ⟨309830, by decide⟩ ⟨12, 1, 0, 309830, 25701, 1, 65536⟩
    (by decide) selected_cut_11598

theorem selected_cut_11599 : selected 9 ⟨309876, by decide⟩
    (prefixPartial 12 25702) = some ⟨12, 2, 0, 309876, 25702, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_25702_309876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25702 ⟨309876, by decide⟩ :=
  accepted_of_selected 12 25702 ⟨309876, by decide⟩ ⟨12, 2, 0, 309876, 25702, 3685, 65536⟩
    (by decide) selected_cut_11599

theorem selected_cut_11600 : selected 9 ⟨309918, by decide⟩
    (prefixPartial 12 25703) = some ⟨12, 2, 0, 309918, 25703, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_25703_309918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25703 ⟨309918, by decide⟩ :=
  accepted_of_selected 12 25703 ⟨309918, by decide⟩ ⟨12, 2, 0, 309918, 25703, 3769, 65536⟩
    (by decide) selected_cut_11600

theorem unmarked_context_11_6425_309919 : frontier 10 ⟨309919, by decide⟩
    (prefixCache 11 6425) (prefixPartial 11 6425) = false := by
  decide +kernel

theorem node_context_11_6425_309919 : EJMOriginalGlobalDAGData.nodes 10 ⟨309919, by decide⟩ =
    .split (coordinate 11) (![⟨309829, by decide⟩,⟨309830, by decide⟩,⟨309876, by decide⟩,⟨309918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6425_309919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6425 ⟨309919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6425
    ⟨309919, by decide⟩ (by decide) (![⟨309829, by decide⟩,⟨309830, by decide⟩,⟨309876, by decide⟩,⟨309918, by decide⟩]) unmarked_context_11_6425_309919 node_context_11_6425_309919
  intro a
  fin_cases a
  · exact context_12_25700_309829
  · exact context_12_25701_309830
  · exact context_12_25702_309876
  · exact context_12_25703_309918

theorem selected_cut_11601 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102816) = some ⟨13, 1, 0, 3444, 102816, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102816_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102816 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102816 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102816, 1, 16384⟩
    (by decide) selected_cut_11601

theorem selected_cut_11602 : selected 8 ⟨309934, by decide⟩
    (prefixPartial 13 102817) = some ⟨13, 2, 0, 309934, 102817, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_102817_309934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102817 ⟨309934, by decide⟩ :=
  accepted_of_selected 13 102817 ⟨309934, by decide⟩ ⟨13, 2, 0, 309934, 102817, 1125, 16384⟩
    (by decide) selected_cut_11602

theorem selected_cut_11603 : selected 8 ⟨309959, by decide⟩
    (prefixPartial 13 102818) = some ⟨13, 2, 0, 309959, 102818, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_102818_309959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102818 ⟨309959, by decide⟩ :=
  accepted_of_selected 13 102818 ⟨309959, by decide⟩ ⟨13, 2, 0, 309959, 102818, 1981, 16384⟩
    (by decide) selected_cut_11603

theorem selected_cut_11604 : selected 8 ⟨309968, by decide⟩
    (prefixPartial 13 102819) = some ⟨13, 2, 0, 309968, 102819, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_102819_309968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102819 ⟨309968, by decide⟩ :=
  accepted_of_selected 13 102819 ⟨309968, by decide⟩ ⟨13, 2, 0, 309968, 102819, 1013, 16384⟩
    (by decide) selected_cut_11604

theorem unmarked_context_12_25704_309969 : frontier 9 ⟨309969, by decide⟩
    (prefixCache 12 25704) (prefixPartial 12 25704) = false := by
  decide +kernel

theorem node_context_12_25704_309969 : EJMOriginalGlobalDAGData.nodes 9 ⟨309969, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309934, by decide⟩,⟨309959, by decide⟩,⟨309968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25704_309969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25704 ⟨309969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25704
    ⟨309969, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309934, by decide⟩,⟨309959, by decide⟩,⟨309968, by decide⟩]) unmarked_context_12_25704_309969 node_context_12_25704_309969
  intro a
  fin_cases a
  · exact context_13_102816_3444
  · exact context_13_102817_309934
  · exact context_13_102818_309959
  · exact context_13_102819_309968

theorem selected_cut_11605 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102820) = some ⟨13, 1, 0, 3444, 102820, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102820_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102820 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102820 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102820, 1, 16384⟩
    (by decide) selected_cut_11605

theorem selected_cut_11606 : selected 8 ⟨309990, by decide⟩
    (prefixPartial 13 102821) = some ⟨13, 2, 0, 309990, 102821, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_102821_309990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102821 ⟨309990, by decide⟩ :=
  accepted_of_selected 13 102821 ⟨309990, by decide⟩ ⟨13, 2, 0, 309990, 102821, 1481, 16384⟩
    (by decide) selected_cut_11606

theorem selected_cut_11607 : selected 8 ⟨310031, by decide⟩
    (prefixPartial 13 102822) = some ⟨13, 2, 0, 310031, 102822, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_102822_310031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102822 ⟨310031, by decide⟩ :=
  accepted_of_selected 13 102822 ⟨310031, by decide⟩ ⟨13, 2, 0, 310031, 102822, 2617, 16384⟩
    (by decide) selected_cut_11607

theorem selected_cut_11608 : selected 8 ⟨310062, by decide⟩
    (prefixPartial 13 102823) = some ⟨13, 2, 0, 310062, 102823, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_102823_310062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102823 ⟨310062, by decide⟩ :=
  accepted_of_selected 13 102823 ⟨310062, by decide⟩ ⟨13, 2, 0, 310062, 102823, 1385, 16384⟩
    (by decide) selected_cut_11608

theorem unmarked_context_12_25705_310063 : frontier 9 ⟨310063, by decide⟩
    (prefixCache 12 25705) (prefixPartial 12 25705) = false := by
  decide +kernel

theorem node_context_12_25705_310063 : EJMOriginalGlobalDAGData.nodes 9 ⟨310063, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨309990, by decide⟩,⟨310031, by decide⟩,⟨310062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25705_310063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25705 ⟨310063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25705
    ⟨310063, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨309990, by decide⟩,⟨310031, by decide⟩,⟨310062, by decide⟩]) unmarked_context_12_25705_310063 node_context_12_25705_310063
  intro a
  fin_cases a
  · exact context_13_102820_3444
  · exact context_13_102821_309990
  · exact context_13_102822_310031
  · exact context_13_102823_310062

theorem selected_cut_11609 : selected 9 ⟨310108, by decide⟩
    (prefixPartial 12 25706) = some ⟨12, 2, 0, 310108, 25706, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_25706_310108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25706 ⟨310108, by decide⟩ :=
  accepted_of_selected 12 25706 ⟨310108, by decide⟩ ⟨12, 2, 0, 310108, 25706, 3705, 65536⟩
    (by decide) selected_cut_11609

theorem selected_cut_11610 : selected 9 ⟨310150, by decide⟩
    (prefixPartial 12 25707) = some ⟨12, 2, 0, 310150, 25707, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_25707_310150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25707 ⟨310150, by decide⟩ :=
  accepted_of_selected 12 25707 ⟨310150, by decide⟩ ⟨12, 2, 0, 310150, 25707, 3981, 65536⟩
    (by decide) selected_cut_11610

theorem unmarked_context_11_6426_310151 : frontier 10 ⟨310151, by decide⟩
    (prefixCache 11 6426) (prefixPartial 11 6426) = false := by
  decide +kernel

theorem node_context_11_6426_310151 : EJMOriginalGlobalDAGData.nodes 10 ⟨310151, by decide⟩ =
    .split (coordinate 11) (![⟨309969, by decide⟩,⟨310063, by decide⟩,⟨310108, by decide⟩,⟨310150, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6426_310151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6426 ⟨310151, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6426
    ⟨310151, by decide⟩ (by decide) (![⟨309969, by decide⟩,⟨310063, by decide⟩,⟨310108, by decide⟩,⟨310150, by decide⟩]) unmarked_context_11_6426_310151 node_context_11_6426_310151
  intro a
  fin_cases a
  · exact context_12_25704_309969
  · exact context_12_25705_310063
  · exact context_12_25706_310108
  · exact context_12_25707_310150

theorem selected_cut_11611 : selected 9 ⟨310197, by decide⟩
    (prefixPartial 12 25708) = some ⟨12, 2, 0, 310197, 25708, 3561, 65536⟩ := by
  decide +kernel

theorem context_12_25708_310197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25708 ⟨310197, by decide⟩ :=
  accepted_of_selected 12 25708 ⟨310197, by decide⟩ ⟨12, 2, 0, 310197, 25708, 3561, 65536⟩
    (by decide) selected_cut_11611

theorem selected_cut_11612 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 102836) = some ⟨13, 1, 0, 3444, 102836, 1, 16384⟩ := by
  decide +kernel

theorem context_13_102836_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102836 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 102836 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 102836, 1, 16384⟩
    (by decide) selected_cut_11612

theorem selected_cut_11613 : selected 8 ⟨310213, by decide⟩
    (prefixPartial 13 102837) = some ⟨13, 2, 0, 310213, 102837, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_102837_310213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102837 ⟨310213, by decide⟩ :=
  accepted_of_selected 13 102837 ⟨310213, by decide⟩ ⟨13, 2, 0, 310213, 102837, 1221, 16384⟩
    (by decide) selected_cut_11613

theorem selected_cut_11614 : selected 8 ⟨310259, by decide⟩
    (prefixPartial 13 102838) = some ⟨13, 2, 0, 310259, 102838, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_102838_310259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102838 ⟨310259, by decide⟩ :=
  accepted_of_selected 13 102838 ⟨310259, by decide⟩ ⟨13, 2, 0, 310259, 102838, 2685, 16384⟩
    (by decide) selected_cut_11614

theorem selected_cut_11615 : selected 8 ⟨310289, by decide⟩
    (prefixPartial 13 102839) = some ⟨13, 2, 0, 310289, 102839, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_102839_310289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102839 ⟨310289, by decide⟩ :=
  accepted_of_selected 13 102839 ⟨310289, by decide⟩ ⟨13, 2, 0, 310289, 102839, 1425, 16384⟩
    (by decide) selected_cut_11615

theorem unmarked_context_12_25709_310290 : frontier 9 ⟨310290, by decide⟩
    (prefixCache 12 25709) (prefixPartial 12 25709) = false := by
  decide +kernel

theorem node_context_12_25709_310290 : EJMOriginalGlobalDAGData.nodes 9 ⟨310290, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨310213, by decide⟩,⟨310259, by decide⟩,⟨310289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25709_310290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25709 ⟨310290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25709
    ⟨310290, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨310213, by decide⟩,⟨310259, by decide⟩,⟨310289, by decide⟩]) unmarked_context_12_25709_310290 node_context_12_25709_310290
  intro a
  fin_cases a
  · exact context_13_102836_3444
  · exact context_13_102837_310213
  · exact context_13_102838_310259
  · exact context_13_102839_310289

theorem selected_cut_11616 : selected 9 ⟨310334, by decide⟩
    (prefixPartial 12 25710) = some ⟨12, 2, 0, 310334, 25710, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_25710_310334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25710 ⟨310334, by decide⟩ :=
  accepted_of_selected 12 25710 ⟨310334, by decide⟩ ⟨12, 2, 0, 310334, 25710, 3665, 65536⟩
    (by decide) selected_cut_11616

theorem selected_cut_11617 : selected 9 ⟨310375, by decide⟩
    (prefixPartial 12 25711) = some ⟨12, 2, 0, 310375, 25711, 3513, 65536⟩ := by
  decide +kernel

theorem context_12_25711_310375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25711 ⟨310375, by decide⟩ :=
  accepted_of_selected 12 25711 ⟨310375, by decide⟩ ⟨12, 2, 0, 310375, 25711, 3513, 65536⟩
    (by decide) selected_cut_11617

theorem unmarked_context_11_6427_310376 : frontier 10 ⟨310376, by decide⟩
    (prefixCache 11 6427) (prefixPartial 11 6427) = false := by
  decide +kernel

theorem node_context_11_6427_310376 : EJMOriginalGlobalDAGData.nodes 10 ⟨310376, by decide⟩ =
    .split (coordinate 11) (![⟨310197, by decide⟩,⟨310290, by decide⟩,⟨310334, by decide⟩,⟨310375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6427_310376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6427 ⟨310376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6427
    ⟨310376, by decide⟩ (by decide) (![⟨310197, by decide⟩,⟨310290, by decide⟩,⟨310334, by decide⟩,⟨310375, by decide⟩]) unmarked_context_11_6427_310376 node_context_11_6427_310376
  intro a
  fin_cases a
  · exact context_12_25708_310197
  · exact context_12_25709_310290
  · exact context_12_25710_310334
  · exact context_12_25711_310375

theorem unmarked_context_10_1606_310377 : frontier 11 ⟨310377, by decide⟩
    (prefixCache 10 1606) (prefixPartial 10 1606) = false := by
  decide +kernel

theorem node_context_10_1606_310377 : EJMOriginalGlobalDAGData.nodes 11 ⟨310377, by decide⟩ =
    .split (coordinate 10) (![⟨309782, by decide⟩,⟨309919, by decide⟩,⟨310151, by decide⟩,⟨310376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1606_310377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1606 ⟨310377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1606
    ⟨310377, by decide⟩ (by decide) (![⟨309782, by decide⟩,⟨309919, by decide⟩,⟨310151, by decide⟩,⟨310376, by decide⟩]) unmarked_context_10_1606_310377 node_context_10_1606_310377
  intro a
  fin_cases a
  · exact context_11_6424_309782
  · exact context_11_6425_309919
  · exact context_11_6426_310151
  · exact context_11_6427_310376

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
