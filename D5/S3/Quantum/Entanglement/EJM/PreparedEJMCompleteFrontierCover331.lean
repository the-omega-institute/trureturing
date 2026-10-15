/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover330
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_107537_815429 : frontier 9 ⟨815429, by decide⟩
    (prefixCache 12 107537) (prefixPartial 12 107537) = false := by
  decide +kernel

theorem node_context_12_107537_815429 : EJMOriginalGlobalDAGData.nodes 9 ⟨815429, by decide⟩ =
    .split (coordinate 12) (![⟨815370, by decide⟩,⟨815400, by decide⟩,⟨815420, by decide⟩,⟨815428, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107537_815429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107537 ⟨815429, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107537
    ⟨815429, by decide⟩ (by decide) (![⟨815370, by decide⟩,⟨815400, by decide⟩,⟨815420, by decide⟩,⟨815428, by decide⟩]) unmarked_context_12_107537_815429 node_context_12_107537_815429
  intro a
  fin_cases a
  · exact context_13_430148_815370
  · exact context_13_430149_815400
  · exact context_13_430150_815420
  · exact context_13_430151_815428

theorem selected_cut_31779 : selected 8 ⟨815456, by decide⟩
    (prefixPartial 13 430152) = some ⟨13, 2, 0, 815456, 430152, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_430152_815456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430152 ⟨815456, by decide⟩ :=
  accepted_of_selected 13 430152 ⟨815456, by decide⟩ ⟨13, 2, 0, 815456, 430152, 1505, 16384⟩
    (by decide) selected_cut_31779

theorem selected_cut_31780 : selected 8 ⟨815489, by decide⟩
    (prefixPartial 13 430153) = some ⟨13, 2, 0, 815489, 430153, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_430153_815489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430153 ⟨815489, by decide⟩ :=
  accepted_of_selected 13 430153 ⟨815489, by decide⟩ ⟨13, 2, 0, 815489, 430153, 2029, 16384⟩
    (by decide) selected_cut_31780

theorem selected_cut_31781 : selected 8 ⟨815509, by decide⟩
    (prefixPartial 13 430154) = some ⟨13, 2, 0, 815509, 430154, 857, 16384⟩ := by
  decide +kernel

theorem context_13_430154_815509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430154 ⟨815509, by decide⟩ :=
  accepted_of_selected 13 430154 ⟨815509, by decide⟩ ⟨13, 2, 0, 815509, 430154, 857, 16384⟩
    (by decide) selected_cut_31781

theorem selected_cut_31782 : selected 8 ⟨815516, by decide⟩
    (prefixPartial 13 430155) = some ⟨13, 2, 0, 815516, 430155, 797, 16384⟩ := by
  decide +kernel

theorem context_13_430155_815516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430155 ⟨815516, by decide⟩ :=
  accepted_of_selected 13 430155 ⟨815516, by decide⟩ ⟨13, 2, 0, 815516, 430155, 797, 16384⟩
    (by decide) selected_cut_31782

theorem unmarked_context_12_107538_815517 : frontier 9 ⟨815517, by decide⟩
    (prefixCache 12 107538) (prefixPartial 12 107538) = false := by
  decide +kernel

theorem node_context_12_107538_815517 : EJMOriginalGlobalDAGData.nodes 9 ⟨815517, by decide⟩ =
    .split (coordinate 12) (![⟨815456, by decide⟩,⟨815489, by decide⟩,⟨815509, by decide⟩,⟨815516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107538_815517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107538 ⟨815517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107538
    ⟨815517, by decide⟩ (by decide) (![⟨815456, by decide⟩,⟨815489, by decide⟩,⟨815509, by decide⟩,⟨815516, by decide⟩]) unmarked_context_12_107538_815517 node_context_12_107538_815517
  intro a
  fin_cases a
  · exact context_13_430152_815456
  · exact context_13_430153_815489
  · exact context_13_430154_815509
  · exact context_13_430155_815516

theorem selected_cut_31783 : selected 8 ⟨815547, by decide⟩
    (prefixPartial 13 430156) = some ⟨13, 2, 0, 815547, 430156, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_430156_815547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430156 ⟨815547, by decide⟩ :=
  accepted_of_selected 13 430156 ⟨815547, by decide⟩ ⟨13, 2, 0, 815547, 430156, 1825, 16384⟩
    (by decide) selected_cut_31783

theorem selected_cut_31784 : selected 8 ⟨815590, by decide⟩
    (prefixPartial 13 430157) = some ⟨13, 2, 0, 815590, 430157, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_430157_815590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430157 ⟨815590, by decide⟩ :=
  accepted_of_selected 13 430157 ⟨815590, by decide⟩ ⟨13, 2, 0, 815590, 430157, 2633, 16384⟩
    (by decide) selected_cut_31784

theorem selected_cut_31785 : selected 8 ⟨815612, by decide⟩
    (prefixPartial 13 430158) = some ⟨13, 2, 0, 815612, 430158, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_430158_815612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430158 ⟨815612, by decide⟩ :=
  accepted_of_selected 13 430158 ⟨815612, by decide⟩ ⟨13, 2, 0, 815612, 430158, 1185, 16384⟩
    (by decide) selected_cut_31785

theorem selected_cut_31786 : selected 8 ⟨815617, by decide⟩
    (prefixPartial 13 430159) = some ⟨13, 2, 0, 815617, 430159, 705, 16384⟩ := by
  decide +kernel

theorem context_13_430159_815617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430159 ⟨815617, by decide⟩ :=
  accepted_of_selected 13 430159 ⟨815617, by decide⟩ ⟨13, 2, 0, 815617, 430159, 705, 16384⟩
    (by decide) selected_cut_31786

theorem unmarked_context_12_107539_815618 : frontier 9 ⟨815618, by decide⟩
    (prefixCache 12 107539) (prefixPartial 12 107539) = false := by
  decide +kernel

theorem node_context_12_107539_815618 : EJMOriginalGlobalDAGData.nodes 9 ⟨815618, by decide⟩ =
    .split (coordinate 12) (![⟨815547, by decide⟩,⟨815590, by decide⟩,⟨815612, by decide⟩,⟨815617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107539_815618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107539 ⟨815618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107539
    ⟨815618, by decide⟩ (by decide) (![⟨815547, by decide⟩,⟨815590, by decide⟩,⟨815612, by decide⟩,⟨815617, by decide⟩]) unmarked_context_12_107539_815618 node_context_12_107539_815618
  intro a
  fin_cases a
  · exact context_13_430156_815547
  · exact context_13_430157_815590
  · exact context_13_430158_815612
  · exact context_13_430159_815617

theorem unmarked_context_11_26884_815619 : frontier 10 ⟨815619, by decide⟩
    (prefixCache 11 26884) (prefixPartial 11 26884) = false := by
  decide +kernel

theorem node_context_11_26884_815619 : EJMOriginalGlobalDAGData.nodes 10 ⟨815619, by decide⟩ =
    .split (coordinate 11) (![⟨815337, by decide⟩,⟨815429, by decide⟩,⟨815517, by decide⟩,⟨815618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26884_815619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26884 ⟨815619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26884
    ⟨815619, by decide⟩ (by decide) (![⟨815337, by decide⟩,⟨815429, by decide⟩,⟨815517, by decide⟩,⟨815618, by decide⟩]) unmarked_context_11_26884_815619 node_context_11_26884_815619
  intro a
  fin_cases a
  · exact context_12_107536_815337
  · exact context_12_107537_815429
  · exact context_12_107538_815517
  · exact context_12_107539_815618

theorem selected_cut_31787 : selected 10 ⟨815620, by decide⟩
    (prefixPartial 11 26885) = some ⟨11, 1, 0, 815620, 26885, 1, 262144⟩ := by
  decide +kernel

theorem context_11_26885_815620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26885 ⟨815620, by decide⟩ :=
  accepted_of_selected 11 26885 ⟨815620, by decide⟩ ⟨11, 1, 0, 815620, 26885, 1, 262144⟩
    (by decide) selected_cut_31787

theorem selected_cut_31788 : selected 8 ⟨815638, by decide⟩
    (prefixPartial 13 430176) = some ⟨13, 2, 0, 815638, 430176, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_430176_815638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430176 ⟨815638, by decide⟩ :=
  accepted_of_selected 13 430176 ⟨815638, by decide⟩ ⟨13, 2, 0, 815638, 430176, 1221, 16384⟩
    (by decide) selected_cut_31788

theorem selected_cut_31789 : selected 8 ⟨815679, by decide⟩
    (prefixPartial 13 430177) = some ⟨13, 2, 0, 815679, 430177, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_430177_815679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430177 ⟨815679, by decide⟩ :=
  accepted_of_selected 13 430177 ⟨815679, by decide⟩ ⟨13, 2, 0, 815679, 430177, 2505, 16384⟩
    (by decide) selected_cut_31789

theorem selected_cut_31790 : selected 8 ⟨815708, by decide⟩
    (prefixPartial 13 430178) = some ⟨13, 2, 0, 815708, 430178, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_430178_815708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430178 ⟨815708, by decide⟩ :=
  accepted_of_selected 13 430178 ⟨815708, by decide⟩ ⟨13, 2, 0, 815708, 430178, 1145, 16384⟩
    (by decide) selected_cut_31790

theorem selected_cut_31791 : selected 8 ⟨815716, by decide⟩
    (prefixPartial 13 430179) = some ⟨13, 2, 0, 815716, 430179, 769, 16384⟩ := by
  decide +kernel

theorem context_13_430179_815716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430179 ⟨815716, by decide⟩ :=
  accepted_of_selected 13 430179 ⟨815716, by decide⟩ ⟨13, 2, 0, 815716, 430179, 769, 16384⟩
    (by decide) selected_cut_31791

theorem unmarked_context_12_107544_815717 : frontier 9 ⟨815717, by decide⟩
    (prefixCache 12 107544) (prefixPartial 12 107544) = false := by
  decide +kernel

theorem node_context_12_107544_815717 : EJMOriginalGlobalDAGData.nodes 9 ⟨815717, by decide⟩ =
    .split (coordinate 12) (![⟨815638, by decide⟩,⟨815679, by decide⟩,⟨815708, by decide⟩,⟨815716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107544_815717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107544 ⟨815717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107544
    ⟨815717, by decide⟩ (by decide) (![⟨815638, by decide⟩,⟨815679, by decide⟩,⟨815708, by decide⟩,⟨815716, by decide⟩]) unmarked_context_12_107544_815717 node_context_12_107544_815717
  intro a
  fin_cases a
  · exact context_13_430176_815638
  · exact context_13_430177_815679
  · exact context_13_430178_815708
  · exact context_13_430179_815716

theorem selected_cut_31792 : selected 8 ⟨815745, by decide⟩
    (prefixPartial 13 430180) = some ⟨13, 2, 0, 815745, 430180, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_430180_815745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430180 ⟨815745, by decide⟩ :=
  accepted_of_selected 13 430180 ⟨815745, by decide⟩ ⟨13, 2, 0, 815745, 430180, 1765, 16384⟩
    (by decide) selected_cut_31792

theorem selected_cut_31793 : selected 8 ⟨815781, by decide⟩
    (prefixPartial 13 430181) = some ⟨13, 2, 0, 815781, 430181, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_430181_815781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430181 ⟨815781, by decide⟩ :=
  accepted_of_selected 13 430181 ⟨815781, by decide⟩ ⟨13, 2, 0, 815781, 430181, 2497, 16384⟩
    (by decide) selected_cut_31793

theorem selected_cut_31794 : selected 8 ⟨815806, by decide⟩
    (prefixPartial 13 430182) = some ⟨13, 2, 0, 815806, 430182, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_430182_815806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430182 ⟨815806, by decide⟩ :=
  accepted_of_selected 13 430182 ⟨815806, by decide⟩ ⟨13, 2, 0, 815806, 430182, 1221, 16384⟩
    (by decide) selected_cut_31794

theorem selected_cut_31795 : selected 8 ⟨815813, by decide⟩
    (prefixPartial 13 430183) = some ⟨13, 2, 0, 815813, 430183, 825, 16384⟩ := by
  decide +kernel

theorem context_13_430183_815813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430183 ⟨815813, by decide⟩ :=
  accepted_of_selected 13 430183 ⟨815813, by decide⟩ ⟨13, 2, 0, 815813, 430183, 825, 16384⟩
    (by decide) selected_cut_31795

theorem unmarked_context_12_107545_815814 : frontier 9 ⟨815814, by decide⟩
    (prefixCache 12 107545) (prefixPartial 12 107545) = false := by
  decide +kernel

theorem node_context_12_107545_815814 : EJMOriginalGlobalDAGData.nodes 9 ⟨815814, by decide⟩ =
    .split (coordinate 12) (![⟨815745, by decide⟩,⟨815781, by decide⟩,⟨815806, by decide⟩,⟨815813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107545_815814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107545 ⟨815814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107545
    ⟨815814, by decide⟩ (by decide) (![⟨815745, by decide⟩,⟨815781, by decide⟩,⟨815806, by decide⟩,⟨815813, by decide⟩]) unmarked_context_12_107545_815814 node_context_12_107545_815814
  intro a
  fin_cases a
  · exact context_13_430180_815745
  · exact context_13_430181_815781
  · exact context_13_430182_815806
  · exact context_13_430183_815813

theorem selected_cut_31796 : selected 8 ⟨815840, by decide⟩
    (prefixPartial 13 430184) = some ⟨13, 2, 0, 815840, 430184, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_430184_815840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430184 ⟨815840, by decide⟩ :=
  accepted_of_selected 13 430184 ⟨815840, by decide⟩ ⟨13, 2, 0, 815840, 430184, 1413, 16384⟩
    (by decide) selected_cut_31796

theorem selected_cut_31797 : selected 8 ⟨815864, by decide⟩
    (prefixPartial 13 430185) = some ⟨13, 2, 0, 815864, 430185, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_430185_815864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430185 ⟨815864, by decide⟩ :=
  accepted_of_selected 13 430185 ⟨815864, by decide⟩ ⟨13, 2, 0, 815864, 430185, 2109, 16384⟩
    (by decide) selected_cut_31797

theorem selected_cut_31798 : selected 8 ⟨815884, by decide⟩
    (prefixPartial 13 430186) = some ⟨13, 2, 0, 815884, 430186, 945, 16384⟩ := by
  decide +kernel

theorem context_13_430186_815884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430186 ⟨815884, by decide⟩ :=
  accepted_of_selected 13 430186 ⟨815884, by decide⟩ ⟨13, 2, 0, 815884, 430186, 945, 16384⟩
    (by decide) selected_cut_31798

theorem selected_cut_31799 : selected 8 ⟨815890, by decide⟩
    (prefixPartial 13 430187) = some ⟨13, 2, 0, 815890, 430187, 797, 16384⟩ := by
  decide +kernel

theorem context_13_430187_815890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430187 ⟨815890, by decide⟩ :=
  accepted_of_selected 13 430187 ⟨815890, by decide⟩ ⟨13, 2, 0, 815890, 430187, 797, 16384⟩
    (by decide) selected_cut_31799

theorem unmarked_context_12_107546_815891 : frontier 9 ⟨815891, by decide⟩
    (prefixCache 12 107546) (prefixPartial 12 107546) = false := by
  decide +kernel

theorem node_context_12_107546_815891 : EJMOriginalGlobalDAGData.nodes 9 ⟨815891, by decide⟩ =
    .split (coordinate 12) (![⟨815840, by decide⟩,⟨815864, by decide⟩,⟨815884, by decide⟩,⟨815890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107546_815891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107546 ⟨815891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107546
    ⟨815891, by decide⟩ (by decide) (![⟨815840, by decide⟩,⟨815864, by decide⟩,⟨815884, by decide⟩,⟨815890, by decide⟩]) unmarked_context_12_107546_815891 node_context_12_107546_815891
  intro a
  fin_cases a
  · exact context_13_430184_815840
  · exact context_13_430185_815864
  · exact context_13_430186_815884
  · exact context_13_430187_815890

theorem selected_cut_31800 : selected 8 ⟨815928, by decide⟩
    (prefixPartial 13 430188) = some ⟨13, 2, 0, 815928, 430188, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_430188_815928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430188 ⟨815928, by decide⟩ :=
  accepted_of_selected 13 430188 ⟨815928, by decide⟩ ⟨13, 2, 0, 815928, 430188, 1829, 16384⟩
    (by decide) selected_cut_31800

theorem selected_cut_31801 : selected 8 ⟨815997, by decide⟩
    (prefixPartial 13 430189) = some ⟨13, 2, 0, 815997, 430189, 2957, 16384⟩ := by
  decide +kernel

theorem context_13_430189_815997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430189 ⟨815997, by decide⟩ :=
  accepted_of_selected 13 430189 ⟨815997, by decide⟩ ⟨13, 2, 0, 815997, 430189, 2957, 16384⟩
    (by decide) selected_cut_31801

theorem selected_cut_31802 : selected 8 ⟨816022, by decide⟩
    (prefixPartial 13 430190) = some ⟨13, 2, 0, 816022, 430190, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_430190_816022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430190 ⟨816022, by decide⟩ :=
  accepted_of_selected 13 430190 ⟨816022, by decide⟩ ⟨13, 2, 0, 816022, 430190, 1245, 16384⟩
    (by decide) selected_cut_31802

theorem selected_cut_31803 : selected 8 ⟨816028, by decide⟩
    (prefixPartial 13 430191) = some ⟨13, 2, 0, 816028, 430191, 765, 16384⟩ := by
  decide +kernel

theorem context_13_430191_816028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430191 ⟨816028, by decide⟩ :=
  accepted_of_selected 13 430191 ⟨816028, by decide⟩ ⟨13, 2, 0, 816028, 430191, 765, 16384⟩
    (by decide) selected_cut_31803

theorem unmarked_context_12_107547_816029 : frontier 9 ⟨816029, by decide⟩
    (prefixCache 12 107547) (prefixPartial 12 107547) = false := by
  decide +kernel

theorem node_context_12_107547_816029 : EJMOriginalGlobalDAGData.nodes 9 ⟨816029, by decide⟩ =
    .split (coordinate 12) (![⟨815928, by decide⟩,⟨815997, by decide⟩,⟨816022, by decide⟩,⟨816028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107547_816029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107547 ⟨816029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107547
    ⟨816029, by decide⟩ (by decide) (![⟨815928, by decide⟩,⟨815997, by decide⟩,⟨816022, by decide⟩,⟨816028, by decide⟩]) unmarked_context_12_107547_816029 node_context_12_107547_816029
  intro a
  fin_cases a
  · exact context_13_430188_815928
  · exact context_13_430189_815997
  · exact context_13_430190_816022
  · exact context_13_430191_816028

theorem unmarked_context_11_26886_816030 : frontier 10 ⟨816030, by decide⟩
    (prefixCache 11 26886) (prefixPartial 11 26886) = false := by
  decide +kernel

theorem node_context_11_26886_816030 : EJMOriginalGlobalDAGData.nodes 10 ⟨816030, by decide⟩ =
    .split (coordinate 11) (![⟨815717, by decide⟩,⟨815814, by decide⟩,⟨815891, by decide⟩,⟨816029, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26886_816030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26886 ⟨816030, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26886
    ⟨816030, by decide⟩ (by decide) (![⟨815717, by decide⟩,⟨815814, by decide⟩,⟨815891, by decide⟩,⟨816029, by decide⟩]) unmarked_context_11_26886_816030 node_context_11_26886_816030
  intro a
  fin_cases a
  · exact context_12_107544_815717
  · exact context_12_107545_815814
  · exact context_12_107546_815891
  · exact context_12_107547_816029

theorem selected_cut_31804 : selected 8 ⟨816045, by decide⟩
    (prefixPartial 13 430192) = some ⟨13, 2, 0, 816045, 430192, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_430192_816045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430192 ⟨816045, by decide⟩ :=
  accepted_of_selected 13 430192 ⟨816045, by decide⟩ ⟨13, 2, 0, 816045, 430192, 1205, 16384⟩
    (by decide) selected_cut_31804

theorem selected_cut_31805 : selected 8 ⟨816111, by decide⟩
    (prefixPartial 13 430193) = some ⟨13, 2, 0, 816111, 430193, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_430193_816111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430193 ⟨816111, by decide⟩ :=
  accepted_of_selected 13 430193 ⟨816111, by decide⟩ ⟨13, 2, 0, 816111, 430193, 2933, 16384⟩
    (by decide) selected_cut_31805

theorem selected_cut_31806 : selected 8 ⟨816130, by decide⟩
    (prefixPartial 13 430194) = some ⟨13, 2, 0, 816130, 430194, 913, 16384⟩ := by
  decide +kernel

theorem context_13_430194_816130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430194 ⟨816130, by decide⟩ :=
  accepted_of_selected 13 430194 ⟨816130, by decide⟩ ⟨13, 2, 0, 816130, 430194, 913, 16384⟩
    (by decide) selected_cut_31806

theorem selected_cut_31807 : selected 8 ⟨816135, by decide⟩
    (prefixPartial 13 430195) = some ⟨13, 2, 0, 816135, 430195, 809, 16384⟩ := by
  decide +kernel

theorem context_13_430195_816135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430195 ⟨816135, by decide⟩ :=
  accepted_of_selected 13 430195 ⟨816135, by decide⟩ ⟨13, 2, 0, 816135, 430195, 809, 16384⟩
    (by decide) selected_cut_31807

theorem unmarked_context_12_107548_816136 : frontier 9 ⟨816136, by decide⟩
    (prefixCache 12 107548) (prefixPartial 12 107548) = false := by
  decide +kernel

theorem node_context_12_107548_816136 : EJMOriginalGlobalDAGData.nodes 9 ⟨816136, by decide⟩ =
    .split (coordinate 12) (![⟨816045, by decide⟩,⟨816111, by decide⟩,⟨816130, by decide⟩,⟨816135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107548_816136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107548 ⟨816136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107548
    ⟨816136, by decide⟩ (by decide) (![⟨816045, by decide⟩,⟨816111, by decide⟩,⟨816130, by decide⟩,⟨816135, by decide⟩]) unmarked_context_12_107548_816136 node_context_12_107548_816136
  intro a
  fin_cases a
  · exact context_13_430192_816045
  · exact context_13_430193_816111
  · exact context_13_430194_816130
  · exact context_13_430195_816135

theorem selected_cut_31808 : selected 8 ⟨816165, by decide⟩
    (prefixPartial 13 430196) = some ⟨13, 2, 0, 816165, 430196, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_430196_816165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430196 ⟨816165, by decide⟩ :=
  accepted_of_selected 13 430196 ⟨816165, by decide⟩ ⟨13, 2, 0, 816165, 430196, 1549, 16384⟩
    (by decide) selected_cut_31808

theorem selected_cut_31809 : selected 8 ⟨816246, by decide⟩
    (prefixPartial 13 430197) = some ⟨13, 2, 0, 816246, 430197, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_430197_816246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430197 ⟨816246, by decide⟩ :=
  accepted_of_selected 13 430197 ⟨816246, by decide⟩ ⟨13, 2, 0, 816246, 430197, 3117, 16384⟩
    (by decide) selected_cut_31809

theorem selected_cut_31810 : selected 8 ⟨816268, by decide⟩
    (prefixPartial 13 430198) = some ⟨13, 2, 0, 816268, 430198, 997, 16384⟩ := by
  decide +kernel

theorem context_13_430198_816268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430198 ⟨816268, by decide⟩ :=
  accepted_of_selected 13 430198 ⟨816268, by decide⟩ ⟨13, 2, 0, 816268, 430198, 997, 16384⟩
    (by decide) selected_cut_31810

theorem selected_cut_31811 : selected 8 ⟨816275, by decide⟩
    (prefixPartial 13 430199) = some ⟨13, 2, 0, 816275, 430199, 785, 16384⟩ := by
  decide +kernel

theorem context_13_430199_816275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430199 ⟨816275, by decide⟩ :=
  accepted_of_selected 13 430199 ⟨816275, by decide⟩ ⟨13, 2, 0, 816275, 430199, 785, 16384⟩
    (by decide) selected_cut_31811

theorem unmarked_context_12_107549_816276 : frontier 9 ⟨816276, by decide⟩
    (prefixCache 12 107549) (prefixPartial 12 107549) = false := by
  decide +kernel

theorem node_context_12_107549_816276 : EJMOriginalGlobalDAGData.nodes 9 ⟨816276, by decide⟩ =
    .split (coordinate 12) (![⟨816165, by decide⟩,⟨816246, by decide⟩,⟨816268, by decide⟩,⟨816275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107549_816276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107549 ⟨816276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107549
    ⟨816276, by decide⟩ (by decide) (![⟨816165, by decide⟩,⟨816246, by decide⟩,⟨816268, by decide⟩,⟨816275, by decide⟩]) unmarked_context_12_107549_816276 node_context_12_107549_816276
  intro a
  fin_cases a
  · exact context_13_430196_816165
  · exact context_13_430197_816246
  · exact context_13_430198_816268
  · exact context_13_430199_816275

theorem selected_cut_31812 : selected 8 ⟨816297, by decide⟩
    (prefixPartial 13 430200) = some ⟨13, 2, 0, 816297, 430200, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_430200_816297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430200 ⟨816297, by decide⟩ :=
  accepted_of_selected 13 430200 ⟨816297, by decide⟩ ⟨13, 2, 0, 816297, 430200, 1397, 16384⟩
    (by decide) selected_cut_31812

theorem selected_cut_31813 : selected 8 ⟨816355, by decide⟩
    (prefixPartial 13 430201) = some ⟨13, 2, 0, 816355, 430201, 2785, 16384⟩ := by
  decide +kernel

theorem context_13_430201_816355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430201 ⟨816355, by decide⟩ :=
  accepted_of_selected 13 430201 ⟨816355, by decide⟩ ⟨13, 2, 0, 816355, 430201, 2785, 16384⟩
    (by decide) selected_cut_31813

theorem selected_cut_31814 : selected 8 ⟨816374, by decide⟩
    (prefixPartial 13 430202) = some ⟨13, 2, 0, 816374, 430202, 853, 16384⟩ := by
  decide +kernel

theorem context_13_430202_816374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430202 ⟨816374, by decide⟩ :=
  accepted_of_selected 13 430202 ⟨816374, by decide⟩ ⟨13, 2, 0, 816374, 430202, 853, 16384⟩
    (by decide) selected_cut_31814

theorem selected_cut_31815 : selected 8 ⟨816382, by decide⟩
    (prefixPartial 13 430203) = some ⟨13, 2, 0, 816382, 430203, 925, 16384⟩ := by
  decide +kernel

theorem context_13_430203_816382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430203 ⟨816382, by decide⟩ :=
  accepted_of_selected 13 430203 ⟨816382, by decide⟩ ⟨13, 2, 0, 816382, 430203, 925, 16384⟩
    (by decide) selected_cut_31815

theorem unmarked_context_12_107550_816383 : frontier 9 ⟨816383, by decide⟩
    (prefixCache 12 107550) (prefixPartial 12 107550) = false := by
  decide +kernel

theorem node_context_12_107550_816383 : EJMOriginalGlobalDAGData.nodes 9 ⟨816383, by decide⟩ =
    .split (coordinate 12) (![⟨816297, by decide⟩,⟨816355, by decide⟩,⟨816374, by decide⟩,⟨816382, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107550_816383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107550 ⟨816383, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107550
    ⟨816383, by decide⟩ (by decide) (![⟨816297, by decide⟩,⟨816355, by decide⟩,⟨816374, by decide⟩,⟨816382, by decide⟩]) unmarked_context_12_107550_816383 node_context_12_107550_816383
  intro a
  fin_cases a
  · exact context_13_430200_816297
  · exact context_13_430201_816355
  · exact context_13_430202_816374
  · exact context_13_430203_816382

theorem selected_cut_31816 : selected 8 ⟨816414, by decide⟩
    (prefixPartial 13 430204) = some ⟨13, 2, 0, 816414, 430204, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_430204_816414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430204 ⟨816414, by decide⟩ :=
  accepted_of_selected 13 430204 ⟨816414, by decide⟩ ⟨13, 2, 0, 816414, 430204, 1533, 16384⟩
    (by decide) selected_cut_31816

theorem selected_cut_31817 : selected 8 ⟨816499, by decide⟩
    (prefixPartial 13 430205) = some ⟨13, 2, 0, 816499, 430205, 3253, 16384⟩ := by
  decide +kernel

theorem context_13_430205_816499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430205 ⟨816499, by decide⟩ :=
  accepted_of_selected 13 430205 ⟨816499, by decide⟩ ⟨13, 2, 0, 816499, 430205, 3253, 16384⟩
    (by decide) selected_cut_31817

theorem selected_cut_31818 : selected 8 ⟨816522, by decide⟩
    (prefixPartial 13 430206) = some ⟨13, 2, 0, 816522, 430206, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_430206_816522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430206 ⟨816522, by decide⟩ :=
  accepted_of_selected 13 430206 ⟨816522, by decide⟩ ⟨13, 2, 0, 816522, 430206, 1005, 16384⟩
    (by decide) selected_cut_31818

theorem selected_cut_31819 : selected 8 ⟨816529, by decide⟩
    (prefixPartial 13 430207) = some ⟨13, 2, 0, 816529, 430207, 769, 16384⟩ := by
  decide +kernel

theorem context_13_430207_816529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430207 ⟨816529, by decide⟩ :=
  accepted_of_selected 13 430207 ⟨816529, by decide⟩ ⟨13, 2, 0, 816529, 430207, 769, 16384⟩
    (by decide) selected_cut_31819

theorem unmarked_context_12_107551_816530 : frontier 9 ⟨816530, by decide⟩
    (prefixCache 12 107551) (prefixPartial 12 107551) = false := by
  decide +kernel

theorem node_context_12_107551_816530 : EJMOriginalGlobalDAGData.nodes 9 ⟨816530, by decide⟩ =
    .split (coordinate 12) (![⟨816414, by decide⟩,⟨816499, by decide⟩,⟨816522, by decide⟩,⟨816529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107551_816530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107551 ⟨816530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107551
    ⟨816530, by decide⟩ (by decide) (![⟨816414, by decide⟩,⟨816499, by decide⟩,⟨816522, by decide⟩,⟨816529, by decide⟩]) unmarked_context_12_107551_816530 node_context_12_107551_816530
  intro a
  fin_cases a
  · exact context_13_430204_816414
  · exact context_13_430205_816499
  · exact context_13_430206_816522
  · exact context_13_430207_816529

theorem unmarked_context_11_26887_816531 : frontier 10 ⟨816531, by decide⟩
    (prefixCache 11 26887) (prefixPartial 11 26887) = false := by
  decide +kernel

theorem node_context_11_26887_816531 : EJMOriginalGlobalDAGData.nodes 10 ⟨816531, by decide⟩ =
    .split (coordinate 11) (![⟨816136, by decide⟩,⟨816276, by decide⟩,⟨816383, by decide⟩,⟨816530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26887_816531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26887 ⟨816531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26887
    ⟨816531, by decide⟩ (by decide) (![⟨816136, by decide⟩,⟨816276, by decide⟩,⟨816383, by decide⟩,⟨816530, by decide⟩]) unmarked_context_11_26887_816531 node_context_11_26887_816531
  intro a
  fin_cases a
  · exact context_12_107548_816136
  · exact context_12_107549_816276
  · exact context_12_107550_816383
  · exact context_12_107551_816530

theorem unmarked_context_10_6721_816532 : frontier 11 ⟨816532, by decide⟩
    (prefixCache 10 6721) (prefixPartial 10 6721) = false := by
  decide +kernel

theorem node_context_10_6721_816532 : EJMOriginalGlobalDAGData.nodes 11 ⟨816532, by decide⟩ =
    .split (coordinate 10) (![⟨815619, by decide⟩,⟨815620, by decide⟩,⟨816030, by decide⟩,⟨816531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6721_816532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6721 ⟨816532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6721
    ⟨816532, by decide⟩ (by decide) (![⟨815619, by decide⟩,⟨815620, by decide⟩,⟨816030, by decide⟩,⟨816531, by decide⟩]) unmarked_context_10_6721_816532 node_context_10_6721_816532
  intro a
  fin_cases a
  · exact context_11_26884_815619
  · exact context_11_26885_815620
  · exact context_11_26886_816030
  · exact context_11_26887_816531

theorem selected_cut_31820 : selected 9 ⟨355612, by decide⟩
    (prefixPartial 12 107552) = some ⟨12, 1, 0, 355612, 107552, 1, 65536⟩ := by
  decide +kernel

theorem context_12_107552_355612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107552 ⟨355612, by decide⟩ :=
  accepted_of_selected 12 107552 ⟨355612, by decide⟩ ⟨12, 1, 0, 355612, 107552, 1, 65536⟩
    (by decide) selected_cut_31820

theorem selected_cut_31821 : selected 8 ⟨816571, by decide⟩
    (prefixPartial 13 430212) = some ⟨13, 2, 0, 816571, 430212, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_430212_816571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430212 ⟨816571, by decide⟩ :=
  accepted_of_selected 13 430212 ⟨816571, by decide⟩ ⟨13, 2, 0, 816571, 430212, 1233, 16384⟩
    (by decide) selected_cut_31821

theorem selected_cut_31822 : selected 8 ⟨816633, by decide⟩
    (prefixPartial 13 430213) = some ⟨13, 2, 0, 816633, 430213, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_430213_816633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430213 ⟨816633, by decide⟩ :=
  accepted_of_selected 13 430213 ⟨816633, by decide⟩ ⟨13, 2, 0, 816633, 430213, 2273, 16384⟩
    (by decide) selected_cut_31822

theorem selected_cut_31823 : selected 8 ⟨816647, by decide⟩
    (prefixPartial 13 430214) = some ⟨13, 2, 0, 816647, 430214, 789, 16384⟩ := by
  decide +kernel

theorem context_13_430214_816647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430214 ⟨816647, by decide⟩ :=
  accepted_of_selected 13 430214 ⟨816647, by decide⟩ ⟨13, 2, 0, 816647, 430214, 789, 16384⟩
    (by decide) selected_cut_31823

theorem selected_cut_31824 : selected 8 ⟨816654, by decide⟩
    (prefixPartial 13 430215) = some ⟨13, 2, 0, 816654, 430215, 777, 16384⟩ := by
  decide +kernel

theorem context_13_430215_816654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430215 ⟨816654, by decide⟩ :=
  accepted_of_selected 13 430215 ⟨816654, by decide⟩ ⟨13, 2, 0, 816654, 430215, 777, 16384⟩
    (by decide) selected_cut_31824

theorem unmarked_context_12_107553_816655 : frontier 9 ⟨816655, by decide⟩
    (prefixCache 12 107553) (prefixPartial 12 107553) = false := by
  decide +kernel

theorem node_context_12_107553_816655 : EJMOriginalGlobalDAGData.nodes 9 ⟨816655, by decide⟩ =
    .split (coordinate 12) (![⟨816571, by decide⟩,⟨816633, by decide⟩,⟨816647, by decide⟩,⟨816654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107553_816655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107553 ⟨816655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107553
    ⟨816655, by decide⟩ (by decide) (![⟨816571, by decide⟩,⟨816633, by decide⟩,⟨816647, by decide⟩,⟨816654, by decide⟩]) unmarked_context_12_107553_816655 node_context_12_107553_816655
  intro a
  fin_cases a
  · exact context_13_430212_816571
  · exact context_13_430213_816633
  · exact context_13_430214_816647
  · exact context_13_430215_816654

theorem selected_cut_31825 : selected 8 ⟨816687, by decide⟩
    (prefixPartial 13 430216) = some ⟨13, 2, 0, 816687, 430216, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_430216_816687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430216 ⟨816687, by decide⟩ :=
  accepted_of_selected 13 430216 ⟨816687, by decide⟩ ⟨13, 2, 0, 816687, 430216, 1125, 16384⟩
    (by decide) selected_cut_31825

theorem selected_cut_31826 : selected 8 ⟨816731, by decide⟩
    (prefixPartial 13 430217) = some ⟨13, 2, 0, 816731, 430217, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_430217_816731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430217 ⟨816731, by decide⟩ :=
  accepted_of_selected 13 430217 ⟨816731, by decide⟩ ⟨13, 2, 0, 816731, 430217, 1965, 16384⟩
    (by decide) selected_cut_31826

theorem selected_cut_31827 : selected 8 ⟨816743, by decide⟩
    (prefixPartial 13 430218) = some ⟨13, 2, 0, 816743, 430218, 737, 16384⟩ := by
  decide +kernel

theorem context_13_430218_816743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430218 ⟨816743, by decide⟩ :=
  accepted_of_selected 13 430218 ⟨816743, by decide⟩ ⟨13, 2, 0, 816743, 430218, 737, 16384⟩
    (by decide) selected_cut_31827

theorem selected_cut_31828 : selected 8 ⟨816750, by decide⟩
    (prefixPartial 13 430219) = some ⟨13, 2, 0, 816750, 430219, 781, 16384⟩ := by
  decide +kernel

theorem context_13_430219_816750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430219 ⟨816750, by decide⟩ :=
  accepted_of_selected 13 430219 ⟨816750, by decide⟩ ⟨13, 2, 0, 816750, 430219, 781, 16384⟩
    (by decide) selected_cut_31828

theorem unmarked_context_12_107554_816751 : frontier 9 ⟨816751, by decide⟩
    (prefixCache 12 107554) (prefixPartial 12 107554) = false := by
  decide +kernel

theorem node_context_12_107554_816751 : EJMOriginalGlobalDAGData.nodes 9 ⟨816751, by decide⟩ =
    .split (coordinate 12) (![⟨816687, by decide⟩,⟨816731, by decide⟩,⟨816743, by decide⟩,⟨816750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107554_816751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107554 ⟨816751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107554
    ⟨816751, by decide⟩ (by decide) (![⟨816687, by decide⟩,⟨816731, by decide⟩,⟨816743, by decide⟩,⟨816750, by decide⟩]) unmarked_context_12_107554_816751 node_context_12_107554_816751
  intro a
  fin_cases a
  · exact context_13_430216_816687
  · exact context_13_430217_816731
  · exact context_13_430218_816743
  · exact context_13_430219_816750

theorem selected_cut_31829 : selected 8 ⟨816781, by decide⟩
    (prefixPartial 13 430220) = some ⟨13, 2, 0, 816781, 430220, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_430220_816781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430220 ⟨816781, by decide⟩ :=
  accepted_of_selected 13 430220 ⟨816781, by decide⟩ ⟨13, 2, 0, 816781, 430220, 1261, 16384⟩
    (by decide) selected_cut_31829

theorem selected_cut_31830 : selected 8 ⟨816828, by decide⟩
    (prefixPartial 13 430221) = some ⟨13, 2, 0, 816828, 430221, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_430221_816828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430221 ⟨816828, by decide⟩ :=
  accepted_of_selected 13 430221 ⟨816828, by decide⟩ ⟨13, 2, 0, 816828, 430221, 2425, 16384⟩
    (by decide) selected_cut_31830

theorem selected_cut_31831 : selected 8 ⟨816846, by decide⟩
    (prefixPartial 13 430222) = some ⟨13, 2, 0, 816846, 430222, 877, 16384⟩ := by
  decide +kernel

theorem context_13_430222_816846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430222 ⟨816846, by decide⟩ :=
  accepted_of_selected 13 430222 ⟨816846, by decide⟩ ⟨13, 2, 0, 816846, 430222, 877, 16384⟩
    (by decide) selected_cut_31831

theorem selected_cut_31832 : selected 8 ⟨816850, by decide⟩
    (prefixPartial 13 430223) = some ⟨13, 2, 0, 816850, 430223, 721, 16384⟩ := by
  decide +kernel

theorem context_13_430223_816850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430223 ⟨816850, by decide⟩ :=
  accepted_of_selected 13 430223 ⟨816850, by decide⟩ ⟨13, 2, 0, 816850, 430223, 721, 16384⟩
    (by decide) selected_cut_31832

theorem unmarked_context_12_107555_816851 : frontier 9 ⟨816851, by decide⟩
    (prefixCache 12 107555) (prefixPartial 12 107555) = false := by
  decide +kernel

theorem node_context_12_107555_816851 : EJMOriginalGlobalDAGData.nodes 9 ⟨816851, by decide⟩ =
    .split (coordinate 12) (![⟨816781, by decide⟩,⟨816828, by decide⟩,⟨816846, by decide⟩,⟨816850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107555_816851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107555 ⟨816851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107555
    ⟨816851, by decide⟩ (by decide) (![⟨816781, by decide⟩,⟨816828, by decide⟩,⟨816846, by decide⟩,⟨816850, by decide⟩]) unmarked_context_12_107555_816851 node_context_12_107555_816851
  intro a
  fin_cases a
  · exact context_13_430220_816781
  · exact context_13_430221_816828
  · exact context_13_430222_816846
  · exact context_13_430223_816850

theorem unmarked_context_11_26888_816852 : frontier 10 ⟨816852, by decide⟩
    (prefixCache 11 26888) (prefixPartial 11 26888) = false := by
  decide +kernel

theorem node_context_11_26888_816852 : EJMOriginalGlobalDAGData.nodes 10 ⟨816852, by decide⟩ =
    .split (coordinate 11) (![⟨355612, by decide⟩,⟨816655, by decide⟩,⟨816751, by decide⟩,⟨816851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26888_816852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26888 ⟨816852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26888
    ⟨816852, by decide⟩ (by decide) (![⟨355612, by decide⟩,⟨816655, by decide⟩,⟨816751, by decide⟩,⟨816851, by decide⟩]) unmarked_context_11_26888_816852 node_context_11_26888_816852
  intro a
  fin_cases a
  · exact context_12_107552_355612
  · exact context_12_107553_816655
  · exact context_12_107554_816751
  · exact context_12_107555_816851

theorem selected_cut_31833 : selected 8 ⟨816876, by decide⟩
    (prefixPartial 13 430224) = some ⟨13, 2, 0, 816876, 430224, 941, 16384⟩ := by
  decide +kernel

theorem context_13_430224_816876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430224 ⟨816876, by decide⟩ :=
  accepted_of_selected 13 430224 ⟨816876, by decide⟩ ⟨13, 2, 0, 816876, 430224, 941, 16384⟩
    (by decide) selected_cut_31833

theorem selected_cut_31834 : selected 8 ⟨816930, by decide⟩
    (prefixPartial 13 430225) = some ⟨13, 2, 0, 816930, 430225, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_430225_816930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430225 ⟨816930, by decide⟩ :=
  accepted_of_selected 13 430225 ⟨816930, by decide⟩ ⟨13, 2, 0, 816930, 430225, 2517, 16384⟩
    (by decide) selected_cut_31834

theorem selected_cut_31835 : selected 8 ⟨816948, by decide⟩
    (prefixPartial 13 430226) = some ⟨13, 2, 0, 816948, 430226, 933, 16384⟩ := by
  decide +kernel

theorem context_13_430226_816948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430226 ⟨816948, by decide⟩ :=
  accepted_of_selected 13 430226 ⟨816948, by decide⟩ ⟨13, 2, 0, 816948, 430226, 933, 16384⟩
    (by decide) selected_cut_31835

theorem selected_cut_31836 : selected 8 ⟨816956, by decide⟩
    (prefixPartial 13 430227) = some ⟨13, 2, 0, 816956, 430227, 921, 16384⟩ := by
  decide +kernel

theorem context_13_430227_816956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430227 ⟨816956, by decide⟩ :=
  accepted_of_selected 13 430227 ⟨816956, by decide⟩ ⟨13, 2, 0, 816956, 430227, 921, 16384⟩
    (by decide) selected_cut_31836

theorem unmarked_context_12_107556_816957 : frontier 9 ⟨816957, by decide⟩
    (prefixCache 12 107556) (prefixPartial 12 107556) = false := by
  decide +kernel

theorem node_context_12_107556_816957 : EJMOriginalGlobalDAGData.nodes 9 ⟨816957, by decide⟩ =
    .split (coordinate 12) (![⟨816876, by decide⟩,⟨816930, by decide⟩,⟨816948, by decide⟩,⟨816956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107556_816957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107556 ⟨816957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107556
    ⟨816957, by decide⟩ (by decide) (![⟨816876, by decide⟩,⟨816930, by decide⟩,⟨816948, by decide⟩,⟨816956, by decide⟩]) unmarked_context_12_107556_816957 node_context_12_107556_816957
  intro a
  fin_cases a
  · exact context_13_430224_816876
  · exact context_13_430225_816930
  · exact context_13_430226_816948
  · exact context_13_430227_816956

theorem selected_cut_31837 : selected 8 ⟨816987, by decide⟩
    (prefixPartial 13 430228) = some ⟨13, 2, 0, 816987, 430228, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_430228_816987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430228 ⟨816987, by decide⟩ :=
  accepted_of_selected 13 430228 ⟨816987, by decide⟩ ⟨13, 2, 0, 816987, 430228, 1061, 16384⟩
    (by decide) selected_cut_31837

theorem selected_cut_31838 : selected 8 ⟨817044, by decide⟩
    (prefixPartial 13 430229) = some ⟨13, 2, 0, 817044, 430229, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_430229_817044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430229 ⟨817044, by decide⟩ :=
  accepted_of_selected 13 430229 ⟨817044, by decide⟩ ⟨13, 2, 0, 817044, 430229, 2373, 16384⟩
    (by decide) selected_cut_31838

theorem selected_cut_31839 : selected 8 ⟨817061, by decide⟩
    (prefixPartial 13 430230) = some ⟨13, 2, 0, 817061, 430230, 873, 16384⟩ := by
  decide +kernel

theorem context_13_430230_817061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430230 ⟨817061, by decide⟩ :=
  accepted_of_selected 13 430230 ⟨817061, by decide⟩ ⟨13, 2, 0, 817061, 430230, 873, 16384⟩
    (by decide) selected_cut_31839

theorem selected_cut_31840 : selected 8 ⟨817072, by decide⟩
    (prefixPartial 13 430231) = some ⟨13, 2, 0, 817072, 430231, 869, 16384⟩ := by
  decide +kernel

theorem context_13_430231_817072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430231 ⟨817072, by decide⟩ :=
  accepted_of_selected 13 430231 ⟨817072, by decide⟩ ⟨13, 2, 0, 817072, 430231, 869, 16384⟩
    (by decide) selected_cut_31840

theorem unmarked_context_12_107557_817073 : frontier 9 ⟨817073, by decide⟩
    (prefixCache 12 107557) (prefixPartial 12 107557) = false := by
  decide +kernel

theorem node_context_12_107557_817073 : EJMOriginalGlobalDAGData.nodes 9 ⟨817073, by decide⟩ =
    .split (coordinate 12) (![⟨816987, by decide⟩,⟨817044, by decide⟩,⟨817061, by decide⟩,⟨817072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107557_817073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107557 ⟨817073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107557
    ⟨817073, by decide⟩ (by decide) (![⟨816987, by decide⟩,⟨817044, by decide⟩,⟨817061, by decide⟩,⟨817072, by decide⟩]) unmarked_context_12_107557_817073 node_context_12_107557_817073
  intro a
  fin_cases a
  · exact context_13_430228_816987
  · exact context_13_430229_817044
  · exact context_13_430230_817061
  · exact context_13_430231_817072

theorem selected_cut_31841 : selected 8 ⟨817099, by decide⟩
    (prefixPartial 13 430232) = some ⟨13, 2, 0, 817099, 430232, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_430232_817099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430232 ⟨817099, by decide⟩ :=
  accepted_of_selected 13 430232 ⟨817099, by decide⟩ ⟨13, 2, 0, 817099, 430232, 1133, 16384⟩
    (by decide) selected_cut_31841

theorem selected_cut_31842 : selected 8 ⟨817159, by decide⟩
    (prefixPartial 13 430233) = some ⟨13, 2, 0, 817159, 430233, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_430233_817159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430233 ⟨817159, by decide⟩ :=
  accepted_of_selected 13 430233 ⟨817159, by decide⟩ ⟨13, 2, 0, 817159, 430233, 2461, 16384⟩
    (by decide) selected_cut_31842

theorem selected_cut_31843 : selected 8 ⟨817173, by decide⟩
    (prefixPartial 13 430234) = some ⟨13, 2, 0, 817173, 430234, 853, 16384⟩ := by
  decide +kernel

theorem context_13_430234_817173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430234 ⟨817173, by decide⟩ :=
  accepted_of_selected 13 430234 ⟨817173, by decide⟩ ⟨13, 2, 0, 817173, 430234, 853, 16384⟩
    (by decide) selected_cut_31843

theorem selected_cut_31844 : selected 8 ⟨817182, by decide⟩
    (prefixPartial 13 430235) = some ⟨13, 2, 0, 817182, 430235, 877, 16384⟩ := by
  decide +kernel

theorem context_13_430235_817182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430235 ⟨817182, by decide⟩ :=
  accepted_of_selected 13 430235 ⟨817182, by decide⟩ ⟨13, 2, 0, 817182, 430235, 877, 16384⟩
    (by decide) selected_cut_31844

theorem unmarked_context_12_107558_817183 : frontier 9 ⟨817183, by decide⟩
    (prefixCache 12 107558) (prefixPartial 12 107558) = false := by
  decide +kernel

theorem node_context_12_107558_817183 : EJMOriginalGlobalDAGData.nodes 9 ⟨817183, by decide⟩ =
    .split (coordinate 12) (![⟨817099, by decide⟩,⟨817159, by decide⟩,⟨817173, by decide⟩,⟨817182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107558_817183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107558 ⟨817183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107558
    ⟨817183, by decide⟩ (by decide) (![⟨817099, by decide⟩,⟨817159, by decide⟩,⟨817173, by decide⟩,⟨817182, by decide⟩]) unmarked_context_12_107558_817183 node_context_12_107558_817183
  intro a
  fin_cases a
  · exact context_13_430232_817099
  · exact context_13_430233_817159
  · exact context_13_430234_817173
  · exact context_13_430235_817182

theorem selected_cut_31845 : selected 8 ⟨817208, by decide⟩
    (prefixPartial 13 430236) = some ⟨13, 2, 0, 817208, 430236, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_430236_817208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430236 ⟨817208, by decide⟩ :=
  accepted_of_selected 13 430236 ⟨817208, by decide⟩ ⟨13, 2, 0, 817208, 430236, 1297, 16384⟩
    (by decide) selected_cut_31845

theorem selected_cut_31846 : selected 8 ⟨817262, by decide⟩
    (prefixPartial 13 430237) = some ⟨13, 2, 0, 817262, 430237, 2709, 16384⟩ := by
  decide +kernel

theorem context_13_430237_817262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430237 ⟨817262, by decide⟩ :=
  accepted_of_selected 13 430237 ⟨817262, by decide⟩ ⟨13, 2, 0, 817262, 430237, 2709, 16384⟩
    (by decide) selected_cut_31846

theorem selected_cut_31847 : selected 8 ⟨817280, by decide⟩
    (prefixPartial 13 430238) = some ⟨13, 2, 0, 817280, 430238, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_430238_817280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430238 ⟨817280, by decide⟩ :=
  accepted_of_selected 13 430238 ⟨817280, by decide⟩ ⟨13, 2, 0, 817280, 430238, 1097, 16384⟩
    (by decide) selected_cut_31847

theorem selected_cut_31848 : selected 8 ⟨817288, by decide⟩
    (prefixPartial 13 430239) = some ⟨13, 2, 0, 817288, 430239, 885, 16384⟩ := by
  decide +kernel

theorem context_13_430239_817288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430239 ⟨817288, by decide⟩ :=
  accepted_of_selected 13 430239 ⟨817288, by decide⟩ ⟨13, 2, 0, 817288, 430239, 885, 16384⟩
    (by decide) selected_cut_31848

theorem unmarked_context_12_107559_817289 : frontier 9 ⟨817289, by decide⟩
    (prefixCache 12 107559) (prefixPartial 12 107559) = false := by
  decide +kernel

theorem node_context_12_107559_817289 : EJMOriginalGlobalDAGData.nodes 9 ⟨817289, by decide⟩ =
    .split (coordinate 12) (![⟨817208, by decide⟩,⟨817262, by decide⟩,⟨817280, by decide⟩,⟨817288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107559_817289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107559 ⟨817289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107559
    ⟨817289, by decide⟩ (by decide) (![⟨817208, by decide⟩,⟨817262, by decide⟩,⟨817280, by decide⟩,⟨817288, by decide⟩]) unmarked_context_12_107559_817289 node_context_12_107559_817289
  intro a
  fin_cases a
  · exact context_13_430236_817208
  · exact context_13_430237_817262
  · exact context_13_430238_817280
  · exact context_13_430239_817288

theorem unmarked_context_11_26889_817290 : frontier 10 ⟨817290, by decide⟩
    (prefixCache 11 26889) (prefixPartial 11 26889) = false := by
  decide +kernel

theorem node_context_11_26889_817290 : EJMOriginalGlobalDAGData.nodes 10 ⟨817290, by decide⟩ =
    .split (coordinate 11) (![⟨816957, by decide⟩,⟨817073, by decide⟩,⟨817183, by decide⟩,⟨817289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26889_817290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26889 ⟨817290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26889
    ⟨817290, by decide⟩ (by decide) (![⟨816957, by decide⟩,⟨817073, by decide⟩,⟨817183, by decide⟩,⟨817289, by decide⟩]) unmarked_context_11_26889_817290 node_context_11_26889_817290
  intro a
  fin_cases a
  · exact context_12_107556_816957
  · exact context_12_107557_817073
  · exact context_12_107558_817183
  · exact context_12_107559_817289

theorem selected_cut_31849 : selected 8 ⟨817306, by decide⟩
    (prefixPartial 13 430240) = some ⟨13, 2, 0, 817306, 430240, 797, 16384⟩ := by
  decide +kernel

theorem context_13_430240_817306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430240 ⟨817306, by decide⟩ :=
  accepted_of_selected 13 430240 ⟨817306, by decide⟩ ⟨13, 2, 0, 817306, 430240, 797, 16384⟩
    (by decide) selected_cut_31849

theorem selected_cut_31850 : selected 8 ⟨817344, by decide⟩
    (prefixPartial 13 430241) = some ⟨13, 2, 0, 817344, 430241, 2125, 16384⟩ := by
  decide +kernel

theorem context_13_430241_817344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430241 ⟨817344, by decide⟩ :=
  accepted_of_selected 13 430241 ⟨817344, by decide⟩ ⟨13, 2, 0, 817344, 430241, 2125, 16384⟩
    (by decide) selected_cut_31850

theorem selected_cut_31851 : selected 8 ⟨817361, by decide⟩
    (prefixPartial 13 430242) = some ⟨13, 2, 0, 817361, 430242, 957, 16384⟩ := by
  decide +kernel

theorem context_13_430242_817361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430242 ⟨817361, by decide⟩ :=
  accepted_of_selected 13 430242 ⟨817361, by decide⟩ ⟨13, 2, 0, 817361, 430242, 957, 16384⟩
    (by decide) selected_cut_31851

theorem selected_cut_31852 : selected 8 ⟨817369, by decide⟩
    (prefixPartial 13 430243) = some ⟨13, 2, 0, 817369, 430243, 933, 16384⟩ := by
  decide +kernel

theorem context_13_430243_817369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430243 ⟨817369, by decide⟩ :=
  accepted_of_selected 13 430243 ⟨817369, by decide⟩ ⟨13, 2, 0, 817369, 430243, 933, 16384⟩
    (by decide) selected_cut_31852

theorem unmarked_context_12_107560_817370 : frontier 9 ⟨817370, by decide⟩
    (prefixCache 12 107560) (prefixPartial 12 107560) = false := by
  decide +kernel

theorem node_context_12_107560_817370 : EJMOriginalGlobalDAGData.nodes 9 ⟨817370, by decide⟩ =
    .split (coordinate 12) (![⟨817306, by decide⟩,⟨817344, by decide⟩,⟨817361, by decide⟩,⟨817369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107560_817370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107560 ⟨817370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107560
    ⟨817370, by decide⟩ (by decide) (![⟨817306, by decide⟩,⟨817344, by decide⟩,⟨817361, by decide⟩,⟨817369, by decide⟩]) unmarked_context_12_107560_817370 node_context_12_107560_817370
  intro a
  fin_cases a
  · exact context_13_430240_817306
  · exact context_13_430241_817344
  · exact context_13_430242_817361
  · exact context_13_430243_817369

theorem selected_cut_31853 : selected 8 ⟨817389, by decide⟩
    (prefixPartial 13 430244) = some ⟨13, 2, 0, 817389, 430244, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_430244_817389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430244 ⟨817389, by decide⟩ :=
  accepted_of_selected 13 430244 ⟨817389, by decide⟩ ⟨13, 2, 0, 817389, 430244, 1061, 16384⟩
    (by decide) selected_cut_31853

theorem selected_cut_31854 : selected 8 ⟨817421, by decide⟩
    (prefixPartial 13 430245) = some ⟨13, 2, 0, 817421, 430245, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_430245_817421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430245 ⟨817421, by decide⟩ :=
  accepted_of_selected 13 430245 ⟨817421, by decide⟩ ⟨13, 2, 0, 817421, 430245, 2025, 16384⟩
    (by decide) selected_cut_31854

theorem selected_cut_31855 : selected 8 ⟨817437, by decide⟩
    (prefixPartial 13 430246) = some ⟨13, 2, 0, 817437, 430246, 973, 16384⟩ := by
  decide +kernel

theorem context_13_430246_817437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430246 ⟨817437, by decide⟩ :=
  accepted_of_selected 13 430246 ⟨817437, by decide⟩ ⟨13, 2, 0, 817437, 430246, 973, 16384⟩
    (by decide) selected_cut_31855

theorem selected_cut_31856 : selected 8 ⟨817450, by decide⟩
    (prefixPartial 13 430247) = some ⟨13, 2, 0, 817450, 430247, 961, 16384⟩ := by
  decide +kernel

theorem context_13_430247_817450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430247 ⟨817450, by decide⟩ :=
  accepted_of_selected 13 430247 ⟨817450, by decide⟩ ⟨13, 2, 0, 817450, 430247, 961, 16384⟩
    (by decide) selected_cut_31856

theorem unmarked_context_12_107561_817451 : frontier 9 ⟨817451, by decide⟩
    (prefixCache 12 107561) (prefixPartial 12 107561) = false := by
  decide +kernel

theorem node_context_12_107561_817451 : EJMOriginalGlobalDAGData.nodes 9 ⟨817451, by decide⟩ =
    .split (coordinate 12) (![⟨817389, by decide⟩,⟨817421, by decide⟩,⟨817437, by decide⟩,⟨817450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107561_817451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107561 ⟨817451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107561
    ⟨817451, by decide⟩ (by decide) (![⟨817389, by decide⟩,⟨817421, by decide⟩,⟨817437, by decide⟩,⟨817450, by decide⟩]) unmarked_context_12_107561_817451 node_context_12_107561_817451
  intro a
  fin_cases a
  · exact context_13_430244_817389
  · exact context_13_430245_817421
  · exact context_13_430246_817437
  · exact context_13_430247_817450

theorem selected_cut_31857 : selected 8 ⟨817465, by decide⟩
    (prefixPartial 13 430248) = some ⟨13, 2, 0, 817465, 430248, 829, 16384⟩ := by
  decide +kernel

theorem context_13_430248_817465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430248 ⟨817465, by decide⟩ :=
  accepted_of_selected 13 430248 ⟨817465, by decide⟩ ⟨13, 2, 0, 817465, 430248, 829, 16384⟩
    (by decide) selected_cut_31857

theorem selected_cut_31858 : selected 8 ⟨817491, by decide⟩
    (prefixPartial 13 430249) = some ⟨13, 2, 0, 817491, 430249, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_430249_817491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430249 ⟨817491, by decide⟩ :=
  accepted_of_selected 13 430249 ⟨817491, by decide⟩ ⟨13, 2, 0, 817491, 430249, 1705, 16384⟩
    (by decide) selected_cut_31858

theorem selected_cut_31859 : selected 8 ⟨817507, by decide⟩
    (prefixPartial 13 430250) = some ⟨13, 2, 0, 817507, 430250, 877, 16384⟩ := by
  decide +kernel

theorem context_13_430250_817507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430250 ⟨817507, by decide⟩ :=
  accepted_of_selected 13 430250 ⟨817507, by decide⟩ ⟨13, 2, 0, 817507, 430250, 877, 16384⟩
    (by decide) selected_cut_31859

theorem selected_cut_31860 : selected 8 ⟨817514, by decide⟩
    (prefixPartial 13 430251) = some ⟨13, 2, 0, 817514, 430251, 849, 16384⟩ := by
  decide +kernel

theorem context_13_430251_817514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430251 ⟨817514, by decide⟩ :=
  accepted_of_selected 13 430251 ⟨817514, by decide⟩ ⟨13, 2, 0, 817514, 430251, 849, 16384⟩
    (by decide) selected_cut_31860

theorem unmarked_context_12_107562_817515 : frontier 9 ⟨817515, by decide⟩
    (prefixCache 12 107562) (prefixPartial 12 107562) = false := by
  decide +kernel

theorem node_context_12_107562_817515 : EJMOriginalGlobalDAGData.nodes 9 ⟨817515, by decide⟩ =
    .split (coordinate 12) (![⟨817465, by decide⟩,⟨817491, by decide⟩,⟨817507, by decide⟩,⟨817514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107562_817515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107562 ⟨817515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107562
    ⟨817515, by decide⟩ (by decide) (![⟨817465, by decide⟩,⟨817491, by decide⟩,⟨817507, by decide⟩,⟨817514, by decide⟩]) unmarked_context_12_107562_817515 node_context_12_107562_817515
  intro a
  fin_cases a
  · exact context_13_430248_817465
  · exact context_13_430249_817491
  · exact context_13_430250_817507
  · exact context_13_430251_817514

theorem selected_cut_31861 : selected 8 ⟨817532, by decide⟩
    (prefixPartial 13 430252) = some ⟨13, 2, 0, 817532, 430252, 937, 16384⟩ := by
  decide +kernel

theorem context_13_430252_817532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430252 ⟨817532, by decide⟩ :=
  accepted_of_selected 13 430252 ⟨817532, by decide⟩ ⟨13, 2, 0, 817532, 430252, 937, 16384⟩
    (by decide) selected_cut_31861

theorem selected_cut_31862 : selected 8 ⟨817561, by decide⟩
    (prefixPartial 13 430253) = some ⟨13, 2, 0, 817561, 430253, 2113, 16384⟩ := by
  decide +kernel

theorem context_13_430253_817561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430253 ⟨817561, by decide⟩ :=
  accepted_of_selected 13 430253 ⟨817561, by decide⟩ ⟨13, 2, 0, 817561, 430253, 2113, 16384⟩
    (by decide) selected_cut_31862

theorem selected_cut_31863 : selected 8 ⟨817580, by decide⟩
    (prefixPartial 13 430254) = some ⟨13, 2, 0, 817580, 430254, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_430254_817580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430254 ⟨817580, by decide⟩ :=
  accepted_of_selected 13 430254 ⟨817580, by decide⟩ ⟨13, 2, 0, 817580, 430254, 1033, 16384⟩
    (by decide) selected_cut_31863

theorem selected_cut_31864 : selected 8 ⟨817588, by decide⟩
    (prefixPartial 13 430255) = some ⟨13, 2, 0, 817588, 430255, 869, 16384⟩ := by
  decide +kernel

theorem context_13_430255_817588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430255 ⟨817588, by decide⟩ :=
  accepted_of_selected 13 430255 ⟨817588, by decide⟩ ⟨13, 2, 0, 817588, 430255, 869, 16384⟩
    (by decide) selected_cut_31864

theorem unmarked_context_12_107563_817589 : frontier 9 ⟨817589, by decide⟩
    (prefixCache 12 107563) (prefixPartial 12 107563) = false := by
  decide +kernel

theorem node_context_12_107563_817589 : EJMOriginalGlobalDAGData.nodes 9 ⟨817589, by decide⟩ =
    .split (coordinate 12) (![⟨817532, by decide⟩,⟨817561, by decide⟩,⟨817580, by decide⟩,⟨817588, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107563_817589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107563 ⟨817589, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107563
    ⟨817589, by decide⟩ (by decide) (![⟨817532, by decide⟩,⟨817561, by decide⟩,⟨817580, by decide⟩,⟨817588, by decide⟩]) unmarked_context_12_107563_817589 node_context_12_107563_817589
  intro a
  fin_cases a
  · exact context_13_430252_817532
  · exact context_13_430253_817561
  · exact context_13_430254_817580
  · exact context_13_430255_817588

theorem unmarked_context_11_26890_817590 : frontier 10 ⟨817590, by decide⟩
    (prefixCache 11 26890) (prefixPartial 11 26890) = false := by
  decide +kernel

theorem node_context_11_26890_817590 : EJMOriginalGlobalDAGData.nodes 10 ⟨817590, by decide⟩ =
    .split (coordinate 11) (![⟨817370, by decide⟩,⟨817451, by decide⟩,⟨817515, by decide⟩,⟨817589, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26890_817590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26890 ⟨817590, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26890
    ⟨817590, by decide⟩ (by decide) (![⟨817370, by decide⟩,⟨817451, by decide⟩,⟨817515, by decide⟩,⟨817589, by decide⟩]) unmarked_context_11_26890_817590 node_context_11_26890_817590
  intro a
  fin_cases a
  · exact context_12_107560_817370
  · exact context_12_107561_817451
  · exact context_12_107562_817515
  · exact context_12_107563_817589

theorem selected_cut_31865 : selected 8 ⟨817607, by decide⟩
    (prefixPartial 13 430256) = some ⟨13, 2, 0, 817607, 430256, 645, 16384⟩ := by
  decide +kernel

theorem context_13_430256_817607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430256 ⟨817607, by decide⟩ :=
  accepted_of_selected 13 430256 ⟨817607, by decide⟩ ⟨13, 2, 0, 817607, 430256, 645, 16384⟩
    (by decide) selected_cut_31865

theorem selected_cut_31866 : selected 8 ⟨817657, by decide⟩
    (prefixPartial 13 430257) = some ⟨13, 2, 0, 817657, 430257, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_430257_817657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430257 ⟨817657, by decide⟩ :=
  accepted_of_selected 13 430257 ⟨817657, by decide⟩ ⟨13, 2, 0, 817657, 430257, 2369, 16384⟩
    (by decide) selected_cut_31866

theorem selected_cut_31867 : selected 8 ⟨817677, by decide⟩
    (prefixPartial 13 430258) = some ⟨13, 2, 0, 817677, 430258, 857, 16384⟩ := by
  decide +kernel

theorem context_13_430258_817677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430258 ⟨817677, by decide⟩ :=
  accepted_of_selected 13 430258 ⟨817677, by decide⟩ ⟨13, 2, 0, 817677, 430258, 857, 16384⟩
    (by decide) selected_cut_31867

theorem selected_cut_31868 : selected 8 ⟨817686, by decide⟩
    (prefixPartial 13 430259) = some ⟨13, 2, 0, 817686, 430259, 833, 16384⟩ := by
  decide +kernel

theorem context_13_430259_817686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430259 ⟨817686, by decide⟩ :=
  accepted_of_selected 13 430259 ⟨817686, by decide⟩ ⟨13, 2, 0, 817686, 430259, 833, 16384⟩
    (by decide) selected_cut_31868

theorem unmarked_context_12_107564_817687 : frontier 9 ⟨817687, by decide⟩
    (prefixCache 12 107564) (prefixPartial 12 107564) = false := by
  decide +kernel

theorem node_context_12_107564_817687 : EJMOriginalGlobalDAGData.nodes 9 ⟨817687, by decide⟩ =
    .split (coordinate 12) (![⟨817607, by decide⟩,⟨817657, by decide⟩,⟨817677, by decide⟩,⟨817686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107564_817687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107564 ⟨817687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107564
    ⟨817687, by decide⟩ (by decide) (![⟨817607, by decide⟩,⟨817657, by decide⟩,⟨817677, by decide⟩,⟨817686, by decide⟩]) unmarked_context_12_107564_817687 node_context_12_107564_817687
  intro a
  fin_cases a
  · exact context_13_430256_817607
  · exact context_13_430257_817657
  · exact context_13_430258_817677
  · exact context_13_430259_817686

theorem selected_cut_31869 : selected 8 ⟨817702, by decide⟩
    (prefixPartial 13 430260) = some ⟨13, 2, 0, 817702, 430260, 789, 16384⟩ := by
  decide +kernel

theorem context_13_430260_817702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430260 ⟨817702, by decide⟩ :=
  accepted_of_selected 13 430260 ⟨817702, by decide⟩ ⟨13, 2, 0, 817702, 430260, 789, 16384⟩
    (by decide) selected_cut_31869

theorem selected_cut_31870 : selected 8 ⟨817757, by decide⟩
    (prefixPartial 13 430261) = some ⟨13, 2, 0, 817757, 430261, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_430261_817757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430261 ⟨817757, by decide⟩ :=
  accepted_of_selected 13 430261 ⟨817757, by decide⟩ ⟨13, 2, 0, 817757, 430261, 2325, 16384⟩
    (by decide) selected_cut_31870

theorem selected_cut_31871 : selected 8 ⟨817774, by decide⟩
    (prefixPartial 13 430262) = some ⟨13, 2, 0, 817774, 430262, 857, 16384⟩ := by
  decide +kernel

theorem context_13_430262_817774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430262 ⟨817774, by decide⟩ :=
  accepted_of_selected 13 430262 ⟨817774, by decide⟩ ⟨13, 2, 0, 817774, 430262, 857, 16384⟩
    (by decide) selected_cut_31871

theorem selected_cut_31872 : selected 8 ⟨817781, by decide⟩
    (prefixPartial 13 430263) = some ⟨13, 2, 0, 817781, 430263, 789, 16384⟩ := by
  decide +kernel

theorem context_13_430263_817781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430263 ⟨817781, by decide⟩ :=
  accepted_of_selected 13 430263 ⟨817781, by decide⟩ ⟨13, 2, 0, 817781, 430263, 789, 16384⟩
    (by decide) selected_cut_31872

theorem unmarked_context_12_107565_817782 : frontier 9 ⟨817782, by decide⟩
    (prefixCache 12 107565) (prefixPartial 12 107565) = false := by
  decide +kernel

theorem node_context_12_107565_817782 : EJMOriginalGlobalDAGData.nodes 9 ⟨817782, by decide⟩ =
    .split (coordinate 12) (![⟨817702, by decide⟩,⟨817757, by decide⟩,⟨817774, by decide⟩,⟨817781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_107565_817782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 107565 ⟨817782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 107565
    ⟨817782, by decide⟩ (by decide) (![⟨817702, by decide⟩,⟨817757, by decide⟩,⟨817774, by decide⟩,⟨817781, by decide⟩]) unmarked_context_12_107565_817782 node_context_12_107565_817782
  intro a
  fin_cases a
  · exact context_13_430260_817702
  · exact context_13_430261_817757
  · exact context_13_430262_817774
  · exact context_13_430263_817781

theorem selected_cut_31873 : selected 8 ⟨817796, by decide⟩
    (prefixPartial 13 430264) = some ⟨13, 2, 0, 817796, 430264, 645, 16384⟩ := by
  decide +kernel

theorem context_13_430264_817796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430264 ⟨817796, by decide⟩ :=
  accepted_of_selected 13 430264 ⟨817796, by decide⟩ ⟨13, 2, 0, 817796, 430264, 645, 16384⟩
    (by decide) selected_cut_31873

theorem selected_cut_31874 : selected 8 ⟨817845, by decide⟩
    (prefixPartial 13 430265) = some ⟨13, 2, 0, 817845, 430265, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_430265_817845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430265 ⟨817845, by decide⟩ :=
  accepted_of_selected 13 430265 ⟨817845, by decide⟩ ⟨13, 2, 0, 817845, 430265, 2229, 16384⟩
    (by decide) selected_cut_31874

theorem selected_cut_31875 : selected 8 ⟨817859, by decide⟩
    (prefixPartial 13 430266) = some ⟨13, 2, 0, 817859, 430266, 857, 16384⟩ := by
  decide +kernel

theorem context_13_430266_817859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 430266 ⟨817859, by decide⟩ :=
  accepted_of_selected 13 430266 ⟨817859, by decide⟩ ⟨13, 2, 0, 817859, 430266, 857, 16384⟩
    (by decide) selected_cut_31875

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
