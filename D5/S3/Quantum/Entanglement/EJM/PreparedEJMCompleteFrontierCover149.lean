/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover148
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14307 : selected 8 ⟨370644, by decide⟩
    (prefixPartial 13 108696) = some ⟨13, 2, 0, 370644, 108696, 897, 16384⟩ := by
  decide +kernel

theorem context_13_108696_370644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108696 ⟨370644, by decide⟩ :=
  accepted_of_selected 13 108696 ⟨370644, by decide⟩ ⟨13, 2, 0, 370644, 108696, 897, 16384⟩
    (by decide) selected_cut_14307

theorem selected_cut_14308 : selected 8 ⟨370665, by decide⟩
    (prefixPartial 13 108697) = some ⟨13, 2, 0, 370665, 108697, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_108697_370665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108697 ⟨370665, by decide⟩ :=
  accepted_of_selected 13 108697 ⟨370665, by decide⟩ ⟨13, 2, 0, 370665, 108697, 1593, 16384⟩
    (by decide) selected_cut_14308

theorem selected_cut_14309 : selected 8 ⟨370677, by decide⟩
    (prefixPartial 13 108698) = some ⟨13, 2, 0, 370677, 108698, 981, 16384⟩ := by
  decide +kernel

theorem context_13_108698_370677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108698 ⟨370677, by decide⟩ :=
  accepted_of_selected 13 108698 ⟨370677, by decide⟩ ⟨13, 2, 0, 370677, 108698, 981, 16384⟩
    (by decide) selected_cut_14309

theorem selected_cut_14310 : selected 8 ⟨370683, by decide⟩
    (prefixPartial 13 108699) = some ⟨13, 2, 0, 370683, 108699, 817, 16384⟩ := by
  decide +kernel

theorem context_13_108699_370683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108699 ⟨370683, by decide⟩ :=
  accepted_of_selected 13 108699 ⟨370683, by decide⟩ ⟨13, 2, 0, 370683, 108699, 817, 16384⟩
    (by decide) selected_cut_14310

theorem unmarked_context_12_27174_370684 : frontier 9 ⟨370684, by decide⟩
    (prefixCache 12 27174) (prefixPartial 12 27174) = false := by
  decide +kernel

theorem node_context_12_27174_370684 : EJMOriginalGlobalDAGData.nodes 9 ⟨370684, by decide⟩ =
    .split (coordinate 12) (![⟨370644, by decide⟩,⟨370665, by decide⟩,⟨370677, by decide⟩,⟨370683, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27174_370684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27174 ⟨370684, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27174
    ⟨370684, by decide⟩ (by decide) (![⟨370644, by decide⟩,⟨370665, by decide⟩,⟨370677, by decide⟩,⟨370683, by decide⟩]) unmarked_context_12_27174_370684 node_context_12_27174_370684
  intro a
  fin_cases a
  · exact context_13_108696_370644
  · exact context_13_108697_370665
  · exact context_13_108698_370677
  · exact context_13_108699_370683

theorem selected_cut_14311 : selected 8 ⟨370696, by decide⟩
    (prefixPartial 13 108700) = some ⟨13, 2, 0, 370696, 108700, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_108700_370696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108700 ⟨370696, by decide⟩ :=
  accepted_of_selected 13 108700 ⟨370696, by decide⟩ ⟨13, 2, 0, 370696, 108700, 1089, 16384⟩
    (by decide) selected_cut_14311

theorem selected_cut_14312 : selected 8 ⟨370719, by decide⟩
    (prefixPartial 13 108701) = some ⟨13, 2, 0, 370719, 108701, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_108701_370719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108701 ⟨370719, by decide⟩ :=
  accepted_of_selected 13 108701 ⟨370719, by decide⟩ ⟨13, 2, 0, 370719, 108701, 2081, 16384⟩
    (by decide) selected_cut_14312

theorem selected_cut_14313 : selected 8 ⟨370740, by decide⟩
    (prefixPartial 13 108702) = some ⟨13, 2, 0, 370740, 108702, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_108702_370740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108702 ⟨370740, by decide⟩ :=
  accepted_of_selected 13 108702 ⟨370740, by decide⟩ ⟨13, 2, 0, 370740, 108702, 1281, 16384⟩
    (by decide) selected_cut_14313

theorem selected_cut_14314 : selected 8 ⟨370747, by decide⟩
    (prefixPartial 13 108703) = some ⟨13, 2, 0, 370747, 108703, 981, 16384⟩ := by
  decide +kernel

theorem context_13_108703_370747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108703 ⟨370747, by decide⟩ :=
  accepted_of_selected 13 108703 ⟨370747, by decide⟩ ⟨13, 2, 0, 370747, 108703, 981, 16384⟩
    (by decide) selected_cut_14314

theorem unmarked_context_12_27175_370748 : frontier 9 ⟨370748, by decide⟩
    (prefixCache 12 27175) (prefixPartial 12 27175) = false := by
  decide +kernel

theorem node_context_12_27175_370748 : EJMOriginalGlobalDAGData.nodes 9 ⟨370748, by decide⟩ =
    .split (coordinate 12) (![⟨370696, by decide⟩,⟨370719, by decide⟩,⟨370740, by decide⟩,⟨370747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27175_370748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27175 ⟨370748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27175
    ⟨370748, by decide⟩ (by decide) (![⟨370696, by decide⟩,⟨370719, by decide⟩,⟨370740, by decide⟩,⟨370747, by decide⟩]) unmarked_context_12_27175_370748 node_context_12_27175_370748
  intro a
  fin_cases a
  · exact context_13_108700_370696
  · exact context_13_108701_370719
  · exact context_13_108702_370740
  · exact context_13_108703_370747

theorem unmarked_context_11_6793_370749 : frontier 10 ⟨370749, by decide⟩
    (prefixCache 11 6793) (prefixPartial 11 6793) = false := by
  decide +kernel

theorem node_context_11_6793_370749 : EJMOriginalGlobalDAGData.nodes 10 ⟨370749, by decide⟩ =
    .split (coordinate 11) (![⟨370569, by decide⟩,⟨370632, by decide⟩,⟨370684, by decide⟩,⟨370748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6793_370749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6793 ⟨370749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6793
    ⟨370749, by decide⟩ (by decide) (![⟨370569, by decide⟩,⟨370632, by decide⟩,⟨370684, by decide⟩,⟨370748, by decide⟩]) unmarked_context_11_6793_370749 node_context_11_6793_370749
  intro a
  fin_cases a
  · exact context_12_27172_370569
  · exact context_12_27173_370632
  · exact context_12_27174_370684
  · exact context_12_27175_370748

theorem selected_cut_14315 : selected 8 ⟨370760, by decide⟩
    (prefixPartial 13 108704) = some ⟨13, 2, 0, 370760, 108704, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_108704_370760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108704 ⟨370760, by decide⟩ :=
  accepted_of_selected 13 108704 ⟨370760, by decide⟩ ⟨13, 2, 0, 370760, 108704, 1077, 16384⟩
    (by decide) selected_cut_14315

theorem selected_cut_14316 : selected 8 ⟨370809, by decide⟩
    (prefixPartial 13 108705) = some ⟨13, 2, 0, 370809, 108705, 3001, 16384⟩ := by
  decide +kernel

theorem context_13_108705_370809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108705 ⟨370809, by decide⟩ :=
  accepted_of_selected 13 108705 ⟨370809, by decide⟩ ⟨13, 2, 0, 370809, 108705, 3001, 16384⟩
    (by decide) selected_cut_14316

theorem selected_cut_14317 : selected 8 ⟨370831, by decide⟩
    (prefixPartial 13 108706) = some ⟨13, 2, 0, 370831, 108706, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_108706_370831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108706 ⟨370831, by decide⟩ :=
  accepted_of_selected 13 108706 ⟨370831, by decide⟩ ⟨13, 2, 0, 370831, 108706, 1477, 16384⟩
    (by decide) selected_cut_14317

theorem selected_cut_14318 : selected 8 ⟨370838, by decide⟩
    (prefixPartial 13 108707) = some ⟨13, 2, 0, 370838, 108707, 949, 16384⟩ := by
  decide +kernel

theorem context_13_108707_370838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108707 ⟨370838, by decide⟩ :=
  accepted_of_selected 13 108707 ⟨370838, by decide⟩ ⟨13, 2, 0, 370838, 108707, 949, 16384⟩
    (by decide) selected_cut_14318

theorem unmarked_context_12_27176_370839 : frontier 9 ⟨370839, by decide⟩
    (prefixCache 12 27176) (prefixPartial 12 27176) = false := by
  decide +kernel

theorem node_context_12_27176_370839 : EJMOriginalGlobalDAGData.nodes 9 ⟨370839, by decide⟩ =
    .split (coordinate 12) (![⟨370760, by decide⟩,⟨370809, by decide⟩,⟨370831, by decide⟩,⟨370838, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27176_370839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27176 ⟨370839, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27176
    ⟨370839, by decide⟩ (by decide) (![⟨370760, by decide⟩,⟨370809, by decide⟩,⟨370831, by decide⟩,⟨370838, by decide⟩]) unmarked_context_12_27176_370839 node_context_12_27176_370839
  intro a
  fin_cases a
  · exact context_13_108704_370760
  · exact context_13_108705_370809
  · exact context_13_108706_370831
  · exact context_13_108707_370838

theorem selected_cut_14319 : selected 8 ⟨370852, by decide⟩
    (prefixPartial 13 108708) = some ⟨13, 2, 0, 370852, 108708, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_108708_370852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108708 ⟨370852, by decide⟩ :=
  accepted_of_selected 13 108708 ⟨370852, by decide⟩ ⟨13, 2, 0, 370852, 108708, 1169, 16384⟩
    (by decide) selected_cut_14319

theorem selected_cut_14320 : selected 8 ⟨370887, by decide⟩
    (prefixPartial 13 108709) = some ⟨13, 2, 0, 370887, 108709, 3009, 16384⟩ := by
  decide +kernel

theorem context_13_108709_370887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108709 ⟨370887, by decide⟩ :=
  accepted_of_selected 13 108709 ⟨370887, by decide⟩ ⟨13, 2, 0, 370887, 108709, 3009, 16384⟩
    (by decide) selected_cut_14320

theorem selected_cut_14321 : selected 8 ⟨370907, by decide⟩
    (prefixPartial 13 108710) = some ⟨13, 2, 0, 370907, 108710, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_108710_370907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108710 ⟨370907, by decide⟩ :=
  accepted_of_selected 13 108710 ⟨370907, by decide⟩ ⟨13, 2, 0, 370907, 108710, 1637, 16384⟩
    (by decide) selected_cut_14321

theorem selected_cut_14322 : selected 8 ⟨370916, by decide⟩
    (prefixPartial 13 108711) = some ⟨13, 2, 0, 370916, 108711, 997, 16384⟩ := by
  decide +kernel

theorem context_13_108711_370916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108711 ⟨370916, by decide⟩ :=
  accepted_of_selected 13 108711 ⟨370916, by decide⟩ ⟨13, 2, 0, 370916, 108711, 997, 16384⟩
    (by decide) selected_cut_14322

theorem unmarked_context_12_27177_370917 : frontier 9 ⟨370917, by decide⟩
    (prefixCache 12 27177) (prefixPartial 12 27177) = false := by
  decide +kernel

theorem node_context_12_27177_370917 : EJMOriginalGlobalDAGData.nodes 9 ⟨370917, by decide⟩ =
    .split (coordinate 12) (![⟨370852, by decide⟩,⟨370887, by decide⟩,⟨370907, by decide⟩,⟨370916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27177_370917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27177 ⟨370917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27177
    ⟨370917, by decide⟩ (by decide) (![⟨370852, by decide⟩,⟨370887, by decide⟩,⟨370907, by decide⟩,⟨370916, by decide⟩]) unmarked_context_12_27177_370917 node_context_12_27177_370917
  intro a
  fin_cases a
  · exact context_13_108708_370852
  · exact context_13_108709_370887
  · exact context_13_108710_370907
  · exact context_13_108711_370916

theorem selected_cut_14323 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 27178) = some ⟨12, 1, 0, 242157, 27178, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27178_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27178 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 27178 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 27178, 1, 65536⟩
    (by decide) selected_cut_14323

theorem selected_cut_14324 : selected 8 ⟨370935, by decide⟩
    (prefixPartial 13 108716) = some ⟨13, 2, 0, 370935, 108716, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_108716_370935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108716 ⟨370935, by decide⟩ :=
  accepted_of_selected 13 108716 ⟨370935, by decide⟩ ⟨13, 2, 0, 370935, 108716, 1213, 16384⟩
    (by decide) selected_cut_14324

theorem selected_cut_14325 : selected 8 ⟨370984, by decide⟩
    (prefixPartial 13 108717) = some ⟨13, 2, 0, 370984, 108717, 3337, 16384⟩ := by
  decide +kernel

theorem context_13_108717_370984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108717 ⟨370984, by decide⟩ :=
  accepted_of_selected 13 108717 ⟨370984, by decide⟩ ⟨13, 2, 0, 370984, 108717, 3337, 16384⟩
    (by decide) selected_cut_14325

theorem selected_cut_14326 : selected 8 ⟨371005, by decide⟩
    (prefixPartial 13 108718) = some ⟨13, 2, 0, 371005, 108718, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_108718_371005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108718 ⟨371005, by decide⟩ :=
  accepted_of_selected 13 108718 ⟨371005, by decide⟩ ⟨13, 2, 0, 371005, 108718, 1585, 16384⟩
    (by decide) selected_cut_14326

theorem selected_cut_14327 : selected 8 ⟨371011, by decide⟩
    (prefixPartial 13 108719) = some ⟨13, 2, 0, 371011, 108719, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_108719_371011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108719 ⟨371011, by decide⟩ :=
  accepted_of_selected 13 108719 ⟨371011, by decide⟩ ⟨13, 2, 0, 371011, 108719, 1113, 16384⟩
    (by decide) selected_cut_14327

theorem unmarked_context_12_27179_371012 : frontier 9 ⟨371012, by decide⟩
    (prefixCache 12 27179) (prefixPartial 12 27179) = false := by
  decide +kernel

theorem node_context_12_27179_371012 : EJMOriginalGlobalDAGData.nodes 9 ⟨371012, by decide⟩ =
    .split (coordinate 12) (![⟨370935, by decide⟩,⟨370984, by decide⟩,⟨371005, by decide⟩,⟨371011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27179_371012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27179 ⟨371012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27179
    ⟨371012, by decide⟩ (by decide) (![⟨370935, by decide⟩,⟨370984, by decide⟩,⟨371005, by decide⟩,⟨371011, by decide⟩]) unmarked_context_12_27179_371012 node_context_12_27179_371012
  intro a
  fin_cases a
  · exact context_13_108716_370935
  · exact context_13_108717_370984
  · exact context_13_108718_371005
  · exact context_13_108719_371011

theorem unmarked_context_11_6794_371013 : frontier 10 ⟨371013, by decide⟩
    (prefixCache 11 6794) (prefixPartial 11 6794) = false := by
  decide +kernel

theorem node_context_11_6794_371013 : EJMOriginalGlobalDAGData.nodes 10 ⟨371013, by decide⟩ =
    .split (coordinate 11) (![⟨370839, by decide⟩,⟨370917, by decide⟩,⟨242157, by decide⟩,⟨371012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6794_371013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6794 ⟨371013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6794
    ⟨371013, by decide⟩ (by decide) (![⟨370839, by decide⟩,⟨370917, by decide⟩,⟨242157, by decide⟩,⟨371012, by decide⟩]) unmarked_context_11_6794_371013 node_context_11_6794_371013
  intro a
  fin_cases a
  · exact context_12_27176_370839
  · exact context_12_27177_370917
  · exact context_12_27178_242157
  · exact context_12_27179_371012

theorem selected_cut_14328 : selected 8 ⟨371018, by decide⟩
    (prefixPartial 13 108720) = some ⟨13, 2, 0, 371018, 108720, 629, 16384⟩ := by
  decide +kernel

theorem context_13_108720_371018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108720 ⟨371018, by decide⟩ :=
  accepted_of_selected 13 108720 ⟨371018, by decide⟩ ⟨13, 2, 0, 371018, 108720, 629, 16384⟩
    (by decide) selected_cut_14328

theorem selected_cut_14329 : selected 8 ⟨371047, by decide⟩
    (prefixPartial 13 108721) = some ⟨13, 2, 0, 371047, 108721, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_108721_371047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108721 ⟨371047, by decide⟩ :=
  accepted_of_selected 13 108721 ⟨371047, by decide⟩ ⟨13, 2, 0, 371047, 108721, 2357, 16384⟩
    (by decide) selected_cut_14329

theorem selected_cut_14330 : selected 8 ⟨371062, by decide⟩
    (prefixPartial 13 108722) = some ⟨13, 2, 0, 371062, 108722, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_108722_371062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108722 ⟨371062, by decide⟩ :=
  accepted_of_selected 13 108722 ⟨371062, by decide⟩ ⟨13, 2, 0, 371062, 108722, 1153, 16384⟩
    (by decide) selected_cut_14330

theorem selected_cut_14331 : selected 8 ⟨371068, by decide⟩
    (prefixPartial 13 108723) = some ⟨13, 2, 0, 371068, 108723, 809, 16384⟩ := by
  decide +kernel

theorem context_13_108723_371068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108723 ⟨371068, by decide⟩ :=
  accepted_of_selected 13 108723 ⟨371068, by decide⟩ ⟨13, 2, 0, 371068, 108723, 809, 16384⟩
    (by decide) selected_cut_14331

theorem unmarked_context_12_27180_371069 : frontier 9 ⟨371069, by decide⟩
    (prefixCache 12 27180) (prefixPartial 12 27180) = false := by
  decide +kernel

theorem node_context_12_27180_371069 : EJMOriginalGlobalDAGData.nodes 9 ⟨371069, by decide⟩ =
    .split (coordinate 12) (![⟨371018, by decide⟩,⟨371047, by decide⟩,⟨371062, by decide⟩,⟨371068, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27180_371069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27180 ⟨371069, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27180
    ⟨371069, by decide⟩ (by decide) (![⟨371018, by decide⟩,⟨371047, by decide⟩,⟨371062, by decide⟩,⟨371068, by decide⟩]) unmarked_context_12_27180_371069 node_context_12_27180_371069
  intro a
  fin_cases a
  · exact context_13_108720_371018
  · exact context_13_108721_371047
  · exact context_13_108722_371062
  · exact context_13_108723_371068

theorem selected_cut_14332 : selected 8 ⟨371079, by decide⟩
    (prefixPartial 13 108724) = some ⟨13, 2, 0, 371079, 108724, 837, 16384⟩ := by
  decide +kernel

theorem context_13_108724_371079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108724 ⟨371079, by decide⟩ :=
  accepted_of_selected 13 108724 ⟨371079, by decide⟩ ⟨13, 2, 0, 371079, 108724, 837, 16384⟩
    (by decide) selected_cut_14332

theorem selected_cut_14333 : selected 8 ⟨371111, by decide⟩
    (prefixPartial 13 108725) = some ⟨13, 2, 0, 371111, 108725, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_108725_371111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108725 ⟨371111, by decide⟩ :=
  accepted_of_selected 13 108725 ⟨371111, by decide⟩ ⟨13, 2, 0, 371111, 108725, 2433, 16384⟩
    (by decide) selected_cut_14333

theorem selected_cut_14334 : selected 8 ⟨371128, by decide⟩
    (prefixPartial 13 108726) = some ⟨13, 2, 0, 371128, 108726, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_108726_371128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108726 ⟨371128, by decide⟩ :=
  accepted_of_selected 13 108726 ⟨371128, by decide⟩ ⟨13, 2, 0, 371128, 108726, 1157, 16384⟩
    (by decide) selected_cut_14334

theorem selected_cut_14335 : selected 8 ⟨371132, by decide⟩
    (prefixPartial 13 108727) = some ⟨13, 2, 0, 371132, 108727, 737, 16384⟩ := by
  decide +kernel

theorem context_13_108727_371132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108727 ⟨371132, by decide⟩ :=
  accepted_of_selected 13 108727 ⟨371132, by decide⟩ ⟨13, 2, 0, 371132, 108727, 737, 16384⟩
    (by decide) selected_cut_14335

theorem unmarked_context_12_27181_371133 : frontier 9 ⟨371133, by decide⟩
    (prefixCache 12 27181) (prefixPartial 12 27181) = false := by
  decide +kernel

theorem node_context_12_27181_371133 : EJMOriginalGlobalDAGData.nodes 9 ⟨371133, by decide⟩ =
    .split (coordinate 12) (![⟨371079, by decide⟩,⟨371111, by decide⟩,⟨371128, by decide⟩,⟨371132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27181_371133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27181 ⟨371133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27181
    ⟨371133, by decide⟩ (by decide) (![⟨371079, by decide⟩,⟨371111, by decide⟩,⟨371128, by decide⟩,⟨371132, by decide⟩]) unmarked_context_12_27181_371133 node_context_12_27181_371133
  intro a
  fin_cases a
  · exact context_13_108724_371079
  · exact context_13_108725_371111
  · exact context_13_108726_371128
  · exact context_13_108727_371132

theorem selected_cut_14336 : selected 8 ⟨371142, by decide⟩
    (prefixPartial 13 108728) = some ⟨13, 2, 0, 371142, 108728, 621, 16384⟩ := by
  decide +kernel

theorem context_13_108728_371142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108728 ⟨371142, by decide⟩ :=
  accepted_of_selected 13 108728 ⟨371142, by decide⟩ ⟨13, 2, 0, 371142, 108728, 621, 16384⟩
    (by decide) selected_cut_14336

theorem selected_cut_14337 : selected 8 ⟨371166, by decide⟩
    (prefixPartial 13 108729) = some ⟨13, 2, 0, 371166, 108729, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_108729_371166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108729 ⟨371166, by decide⟩ :=
  accepted_of_selected 13 108729 ⟨371166, by decide⟩ ⟨13, 2, 0, 371166, 108729, 1969, 16384⟩
    (by decide) selected_cut_14337

theorem selected_cut_14338 : selected 8 ⟨371177, by decide⟩
    (prefixPartial 13 108730) = some ⟨13, 2, 0, 371177, 108730, 885, 16384⟩ := by
  decide +kernel

theorem context_13_108730_371177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108730 ⟨371177, by decide⟩ :=
  accepted_of_selected 13 108730 ⟨371177, by decide⟩ ⟨13, 2, 0, 371177, 108730, 885, 16384⟩
    (by decide) selected_cut_14338

theorem selected_cut_14339 : selected 8 ⟨371182, by decide⟩
    (prefixPartial 13 108731) = some ⟨13, 2, 0, 371182, 108731, 709, 16384⟩ := by
  decide +kernel

theorem context_13_108731_371182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108731 ⟨371182, by decide⟩ :=
  accepted_of_selected 13 108731 ⟨371182, by decide⟩ ⟨13, 2, 0, 371182, 108731, 709, 16384⟩
    (by decide) selected_cut_14339

theorem unmarked_context_12_27182_371183 : frontier 9 ⟨371183, by decide⟩
    (prefixCache 12 27182) (prefixPartial 12 27182) = false := by
  decide +kernel

theorem node_context_12_27182_371183 : EJMOriginalGlobalDAGData.nodes 9 ⟨371183, by decide⟩ =
    .split (coordinate 12) (![⟨371142, by decide⟩,⟨371166, by decide⟩,⟨371177, by decide⟩,⟨371182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27182_371183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27182 ⟨371183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27182
    ⟨371183, by decide⟩ (by decide) (![⟨371142, by decide⟩,⟨371166, by decide⟩,⟨371177, by decide⟩,⟨371182, by decide⟩]) unmarked_context_12_27182_371183 node_context_12_27182_371183
  intro a
  fin_cases a
  · exact context_13_108728_371142
  · exact context_13_108729_371166
  · exact context_13_108730_371177
  · exact context_13_108731_371182

theorem selected_cut_14340 : selected 8 ⟨371195, by decide⟩
    (prefixPartial 13 108732) = some ⟨13, 2, 0, 371195, 108732, 801, 16384⟩ := by
  decide +kernel

theorem context_13_108732_371195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108732 ⟨371195, by decide⟩ :=
  accepted_of_selected 13 108732 ⟨371195, by decide⟩ ⟨13, 2, 0, 371195, 108732, 801, 16384⟩
    (by decide) selected_cut_14340

theorem selected_cut_14341 : selected 8 ⟨371224, by decide⟩
    (prefixPartial 13 108733) = some ⟨13, 2, 0, 371224, 108733, 2401, 16384⟩ := by
  decide +kernel

theorem context_13_108733_371224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108733 ⟨371224, by decide⟩ :=
  accepted_of_selected 13 108733 ⟨371224, by decide⟩ ⟨13, 2, 0, 371224, 108733, 2401, 16384⟩
    (by decide) selected_cut_14341

theorem selected_cut_14342 : selected 8 ⟨371241, by decide⟩
    (prefixPartial 13 108734) = some ⟨13, 2, 0, 371241, 108734, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_108734_371241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108734 ⟨371241, by decide⟩ :=
  accepted_of_selected 13 108734 ⟨371241, by decide⟩ ⟨13, 2, 0, 371241, 108734, 1205, 16384⟩
    (by decide) selected_cut_14342

theorem selected_cut_14343 : selected 8 ⟨371247, by decide⟩
    (prefixPartial 13 108735) = some ⟨13, 2, 0, 371247, 108735, 789, 16384⟩ := by
  decide +kernel

theorem context_13_108735_371247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108735 ⟨371247, by decide⟩ :=
  accepted_of_selected 13 108735 ⟨371247, by decide⟩ ⟨13, 2, 0, 371247, 108735, 789, 16384⟩
    (by decide) selected_cut_14343

theorem unmarked_context_12_27183_371248 : frontier 9 ⟨371248, by decide⟩
    (prefixCache 12 27183) (prefixPartial 12 27183) = false := by
  decide +kernel

theorem node_context_12_27183_371248 : EJMOriginalGlobalDAGData.nodes 9 ⟨371248, by decide⟩ =
    .split (coordinate 12) (![⟨371195, by decide⟩,⟨371224, by decide⟩,⟨371241, by decide⟩,⟨371247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27183_371248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27183 ⟨371248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27183
    ⟨371248, by decide⟩ (by decide) (![⟨371195, by decide⟩,⟨371224, by decide⟩,⟨371241, by decide⟩,⟨371247, by decide⟩]) unmarked_context_12_27183_371248 node_context_12_27183_371248
  intro a
  fin_cases a
  · exact context_13_108732_371195
  · exact context_13_108733_371224
  · exact context_13_108734_371241
  · exact context_13_108735_371247

theorem unmarked_context_11_6795_371249 : frontier 10 ⟨371249, by decide⟩
    (prefixCache 11 6795) (prefixPartial 11 6795) = false := by
  decide +kernel

theorem node_context_11_6795_371249 : EJMOriginalGlobalDAGData.nodes 10 ⟨371249, by decide⟩ =
    .split (coordinate 11) (![⟨371069, by decide⟩,⟨371133, by decide⟩,⟨371183, by decide⟩,⟨371248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6795_371249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6795 ⟨371249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6795
    ⟨371249, by decide⟩ (by decide) (![⟨371069, by decide⟩,⟨371133, by decide⟩,⟨371183, by decide⟩,⟨371248, by decide⟩]) unmarked_context_11_6795_371249 node_context_11_6795_371249
  intro a
  fin_cases a
  · exact context_12_27180_371069
  · exact context_12_27181_371133
  · exact context_12_27182_371183
  · exact context_12_27183_371248

theorem unmarked_context_10_1698_371250 : frontier 11 ⟨371250, by decide⟩
    (prefixCache 10 1698) (prefixPartial 10 1698) = false := by
  decide +kernel

theorem node_context_10_1698_371250 : EJMOriginalGlobalDAGData.nodes 11 ⟨371250, by decide⟩ =
    .split (coordinate 10) (![⟨370508, by decide⟩,⟨370749, by decide⟩,⟨371013, by decide⟩,⟨371249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1698_371250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1698 ⟨371250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1698
    ⟨371250, by decide⟩ (by decide) (![⟨370508, by decide⟩,⟨370749, by decide⟩,⟨371013, by decide⟩,⟨371249, by decide⟩]) unmarked_context_10_1698_371250 node_context_10_1698_371250
  intro a
  fin_cases a
  · exact context_11_6792_370508
  · exact context_11_6793_370749
  · exact context_11_6794_371013
  · exact context_11_6795_371249

theorem selected_cut_14344 : selected 8 ⟨371257, by decide⟩
    (prefixPartial 13 108736) = some ⟨13, 2, 0, 371257, 108736, 845, 16384⟩ := by
  decide +kernel

theorem context_13_108736_371257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108736 ⟨371257, by decide⟩ :=
  accepted_of_selected 13 108736 ⟨371257, by decide⟩ ⟨13, 2, 0, 371257, 108736, 845, 16384⟩
    (by decide) selected_cut_14344

theorem selected_cut_14345 : selected 8 ⟨371282, by decide⟩
    (prefixPartial 13 108737) = some ⟨13, 2, 0, 371282, 108737, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_108737_371282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108737 ⟨371282, by decide⟩ :=
  accepted_of_selected 13 108737 ⟨371282, by decide⟩ ⟨13, 2, 0, 371282, 108737, 2409, 16384⟩
    (by decide) selected_cut_14345

theorem selected_cut_14346 : selected 8 ⟨371297, by decide⟩
    (prefixPartial 13 108738) = some ⟨13, 2, 0, 371297, 108738, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_108738_371297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108738 ⟨371297, by decide⟩ :=
  accepted_of_selected 13 108738 ⟨371297, by decide⟩ ⟨13, 2, 0, 371297, 108738, 1153, 16384⟩
    (by decide) selected_cut_14346

theorem selected_cut_14347 : selected 8 ⟨371304, by decide⟩
    (prefixPartial 13 108739) = some ⟨13, 2, 0, 371304, 108739, 873, 16384⟩ := by
  decide +kernel

theorem context_13_108739_371304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108739 ⟨371304, by decide⟩ :=
  accepted_of_selected 13 108739 ⟨371304, by decide⟩ ⟨13, 2, 0, 371304, 108739, 873, 16384⟩
    (by decide) selected_cut_14347

theorem unmarked_context_12_27184_371305 : frontier 9 ⟨371305, by decide⟩
    (prefixCache 12 27184) (prefixPartial 12 27184) = false := by
  decide +kernel

theorem node_context_12_27184_371305 : EJMOriginalGlobalDAGData.nodes 9 ⟨371305, by decide⟩ =
    .split (coordinate 12) (![⟨371257, by decide⟩,⟨371282, by decide⟩,⟨371297, by decide⟩,⟨371304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27184_371305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27184 ⟨371305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27184
    ⟨371305, by decide⟩ (by decide) (![⟨371257, by decide⟩,⟨371282, by decide⟩,⟨371297, by decide⟩,⟨371304, by decide⟩]) unmarked_context_12_27184_371305 node_context_12_27184_371305
  intro a
  fin_cases a
  · exact context_13_108736_371257
  · exact context_13_108737_371282
  · exact context_13_108738_371297
  · exact context_13_108739_371304

theorem selected_cut_14348 : selected 8 ⟨371316, by decide⟩
    (prefixPartial 13 108740) = some ⟨13, 2, 0, 371316, 108740, 925, 16384⟩ := by
  decide +kernel

theorem context_13_108740_371316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108740 ⟨371316, by decide⟩ :=
  accepted_of_selected 13 108740 ⟨371316, by decide⟩ ⟨13, 2, 0, 371316, 108740, 925, 16384⟩
    (by decide) selected_cut_14348

theorem selected_cut_14349 : selected 8 ⟨371345, by decide⟩
    (prefixPartial 13 108741) = some ⟨13, 2, 0, 371345, 108741, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_108741_371345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108741 ⟨371345, by decide⟩ :=
  accepted_of_selected 13 108741 ⟨371345, by decide⟩ ⟨13, 2, 0, 371345, 108741, 2361, 16384⟩
    (by decide) selected_cut_14349

theorem selected_cut_14350 : selected 8 ⟨371360, by decide⟩
    (prefixPartial 13 108742) = some ⟨13, 2, 0, 371360, 108742, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_108742_371360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108742 ⟨371360, by decide⟩ :=
  accepted_of_selected 13 108742 ⟨371360, by decide⟩ ⟨13, 2, 0, 371360, 108742, 1349, 16384⟩
    (by decide) selected_cut_14350

theorem selected_cut_14351 : selected 8 ⟨371365, by decide⟩
    (prefixPartial 13 108743) = some ⟨13, 2, 0, 371365, 108743, 921, 16384⟩ := by
  decide +kernel

theorem context_13_108743_371365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108743 ⟨371365, by decide⟩ :=
  accepted_of_selected 13 108743 ⟨371365, by decide⟩ ⟨13, 2, 0, 371365, 108743, 921, 16384⟩
    (by decide) selected_cut_14351

theorem unmarked_context_12_27185_371366 : frontier 9 ⟨371366, by decide⟩
    (prefixCache 12 27185) (prefixPartial 12 27185) = false := by
  decide +kernel

theorem node_context_12_27185_371366 : EJMOriginalGlobalDAGData.nodes 9 ⟨371366, by decide⟩ =
    .split (coordinate 12) (![⟨371316, by decide⟩,⟨371345, by decide⟩,⟨371360, by decide⟩,⟨371365, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27185_371366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27185 ⟨371366, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27185
    ⟨371366, by decide⟩ (by decide) (![⟨371316, by decide⟩,⟨371345, by decide⟩,⟨371360, by decide⟩,⟨371365, by decide⟩]) unmarked_context_12_27185_371366 node_context_12_27185_371366
  intro a
  fin_cases a
  · exact context_13_108740_371316
  · exact context_13_108741_371345
  · exact context_13_108742_371360
  · exact context_13_108743_371365

theorem selected_cut_14352 : selected 8 ⟨371376, by decide⟩
    (prefixPartial 13 108744) = some ⟨13, 2, 0, 371376, 108744, 741, 16384⟩ := by
  decide +kernel

theorem context_13_108744_371376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108744 ⟨371376, by decide⟩ :=
  accepted_of_selected 13 108744 ⟨371376, by decide⟩ ⟨13, 2, 0, 371376, 108744, 741, 16384⟩
    (by decide) selected_cut_14352

theorem selected_cut_14353 : selected 8 ⟨371398, by decide⟩
    (prefixPartial 13 108745) = some ⟨13, 2, 0, 371398, 108745, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_108745_371398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108745 ⟨371398, by decide⟩ :=
  accepted_of_selected 13 108745 ⟨371398, by decide⟩ ⟨13, 2, 0, 371398, 108745, 2205, 16384⟩
    (by decide) selected_cut_14353

theorem selected_cut_14354 : selected 8 ⟨371416, by decide⟩
    (prefixPartial 13 108746) = some ⟨13, 2, 0, 371416, 108746, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_108746_371416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108746 ⟨371416, by decide⟩ :=
  accepted_of_selected 13 108746 ⟨371416, by decide⟩ ⟨13, 2, 0, 371416, 108746, 1257, 16384⟩
    (by decide) selected_cut_14354

theorem selected_cut_14355 : selected 8 ⟨371421, by decide⟩
    (prefixPartial 13 108747) = some ⟨13, 2, 0, 371421, 108747, 877, 16384⟩ := by
  decide +kernel

theorem context_13_108747_371421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108747 ⟨371421, by decide⟩ :=
  accepted_of_selected 13 108747 ⟨371421, by decide⟩ ⟨13, 2, 0, 371421, 108747, 877, 16384⟩
    (by decide) selected_cut_14355

theorem unmarked_context_12_27186_371422 : frontier 9 ⟨371422, by decide⟩
    (prefixCache 12 27186) (prefixPartial 12 27186) = false := by
  decide +kernel

theorem node_context_12_27186_371422 : EJMOriginalGlobalDAGData.nodes 9 ⟨371422, by decide⟩ =
    .split (coordinate 12) (![⟨371376, by decide⟩,⟨371398, by decide⟩,⟨371416, by decide⟩,⟨371421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27186_371422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27186 ⟨371422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27186
    ⟨371422, by decide⟩ (by decide) (![⟨371376, by decide⟩,⟨371398, by decide⟩,⟨371416, by decide⟩,⟨371421, by decide⟩]) unmarked_context_12_27186_371422 node_context_12_27186_371422
  intro a
  fin_cases a
  · exact context_13_108744_371376
  · exact context_13_108745_371398
  · exact context_13_108746_371416
  · exact context_13_108747_371421

theorem selected_cut_14356 : selected 8 ⟨371437, by decide⟩
    (prefixPartial 13 108748) = some ⟨13, 2, 0, 371437, 108748, 953, 16384⟩ := by
  decide +kernel

theorem context_13_108748_371437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108748 ⟨371437, by decide⟩ :=
  accepted_of_selected 13 108748 ⟨371437, by decide⟩ ⟨13, 2, 0, 371437, 108748, 953, 16384⟩
    (by decide) selected_cut_14356

theorem selected_cut_14357 : selected 8 ⟨371474, by decide⟩
    (prefixPartial 13 108749) = some ⟨13, 2, 0, 371474, 108749, 2849, 16384⟩ := by
  decide +kernel

theorem context_13_108749_371474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108749 ⟨371474, by decide⟩ :=
  accepted_of_selected 13 108749 ⟨371474, by decide⟩ ⟨13, 2, 0, 371474, 108749, 2849, 16384⟩
    (by decide) selected_cut_14357

theorem selected_cut_14358 : selected 8 ⟨371496, by decide⟩
    (prefixPartial 13 108750) = some ⟨13, 2, 0, 371496, 108750, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_108750_371496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108750 ⟨371496, by decide⟩ :=
  accepted_of_selected 13 108750 ⟨371496, by decide⟩ ⟨13, 2, 0, 371496, 108750, 1493, 16384⟩
    (by decide) selected_cut_14358

theorem selected_cut_14359 : selected 8 ⟨371506, by decide⟩
    (prefixPartial 13 108751) = some ⟨13, 2, 0, 371506, 108751, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_108751_371506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108751 ⟨371506, by decide⟩ :=
  accepted_of_selected 13 108751 ⟨371506, by decide⟩ ⟨13, 2, 0, 371506, 108751, 1033, 16384⟩
    (by decide) selected_cut_14359

theorem unmarked_context_12_27187_371507 : frontier 9 ⟨371507, by decide⟩
    (prefixCache 12 27187) (prefixPartial 12 27187) = false := by
  decide +kernel

theorem node_context_12_27187_371507 : EJMOriginalGlobalDAGData.nodes 9 ⟨371507, by decide⟩ =
    .split (coordinate 12) (![⟨371437, by decide⟩,⟨371474, by decide⟩,⟨371496, by decide⟩,⟨371506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27187_371507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27187 ⟨371507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27187
    ⟨371507, by decide⟩ (by decide) (![⟨371437, by decide⟩,⟨371474, by decide⟩,⟨371496, by decide⟩,⟨371506, by decide⟩]) unmarked_context_12_27187_371507 node_context_12_27187_371507
  intro a
  fin_cases a
  · exact context_13_108748_371437
  · exact context_13_108749_371474
  · exact context_13_108750_371496
  · exact context_13_108751_371506

theorem unmarked_context_11_6796_371508 : frontier 10 ⟨371508, by decide⟩
    (prefixCache 11 6796) (prefixPartial 11 6796) = false := by
  decide +kernel

theorem node_context_11_6796_371508 : EJMOriginalGlobalDAGData.nodes 10 ⟨371508, by decide⟩ =
    .split (coordinate 11) (![⟨371305, by decide⟩,⟨371366, by decide⟩,⟨371422, by decide⟩,⟨371507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6796_371508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6796 ⟨371508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6796
    ⟨371508, by decide⟩ (by decide) (![⟨371305, by decide⟩,⟨371366, by decide⟩,⟨371422, by decide⟩,⟨371507, by decide⟩]) unmarked_context_11_6796_371508 node_context_11_6796_371508
  intro a
  fin_cases a
  · exact context_12_27184_371305
  · exact context_12_27185_371366
  · exact context_12_27186_371422
  · exact context_12_27187_371507

theorem selected_cut_14360 : selected 8 ⟨371514, by decide⟩
    (prefixPartial 13 108752) = some ⟨13, 2, 0, 371514, 108752, 625, 16384⟩ := by
  decide +kernel

theorem context_13_108752_371514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108752 ⟨371514, by decide⟩ :=
  accepted_of_selected 13 108752 ⟨371514, by decide⟩ ⟨13, 2, 0, 371514, 108752, 625, 16384⟩
    (by decide) selected_cut_14360

theorem selected_cut_14361 : selected 8 ⟨371542, by decide⟩
    (prefixPartial 13 108753) = some ⟨13, 2, 0, 371542, 108753, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_108753_371542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108753 ⟨371542, by decide⟩ :=
  accepted_of_selected 13 108753 ⟨371542, by decide⟩ ⟨13, 2, 0, 371542, 108753, 2497, 16384⟩
    (by decide) selected_cut_14361

theorem selected_cut_14362 : selected 8 ⟨371556, by decide⟩
    (prefixPartial 13 108754) = some ⟨13, 2, 0, 371556, 108754, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_108754_371556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108754 ⟨371556, by decide⟩ :=
  accepted_of_selected 13 108754 ⟨371556, by decide⟩ ⟨13, 2, 0, 371556, 108754, 1209, 16384⟩
    (by decide) selected_cut_14362

theorem selected_cut_14363 : selected 8 ⟨371560, by decide⟩
    (prefixPartial 13 108755) = some ⟨13, 2, 0, 371560, 108755, 945, 16384⟩ := by
  decide +kernel

theorem context_13_108755_371560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108755 ⟨371560, by decide⟩ :=
  accepted_of_selected 13 108755 ⟨371560, by decide⟩ ⟨13, 2, 0, 371560, 108755, 945, 16384⟩
    (by decide) selected_cut_14363

theorem unmarked_context_12_27188_371561 : frontier 9 ⟨371561, by decide⟩
    (prefixCache 12 27188) (prefixPartial 12 27188) = false := by
  decide +kernel

theorem node_context_12_27188_371561 : EJMOriginalGlobalDAGData.nodes 9 ⟨371561, by decide⟩ =
    .split (coordinate 12) (![⟨371514, by decide⟩,⟨371542, by decide⟩,⟨371556, by decide⟩,⟨371560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27188_371561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27188 ⟨371561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27188
    ⟨371561, by decide⟩ (by decide) (![⟨371514, by decide⟩,⟨371542, by decide⟩,⟨371556, by decide⟩,⟨371560, by decide⟩]) unmarked_context_12_27188_371561 node_context_12_27188_371561
  intro a
  fin_cases a
  · exact context_13_108752_371514
  · exact context_13_108753_371542
  · exact context_13_108754_371556
  · exact context_13_108755_371560

theorem selected_cut_14364 : selected 8 ⟨371570, by decide⟩
    (prefixPartial 13 108756) = some ⟨13, 2, 0, 371570, 108756, 705, 16384⟩ := by
  decide +kernel

theorem context_13_108756_371570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108756 ⟨371570, by decide⟩ :=
  accepted_of_selected 13 108756 ⟨371570, by decide⟩ ⟨13, 2, 0, 371570, 108756, 705, 16384⟩
    (by decide) selected_cut_14364

theorem selected_cut_14365 : selected 8 ⟨371592, by decide⟩
    (prefixPartial 13 108757) = some ⟨13, 2, 0, 371592, 108757, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_108757_371592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108757 ⟨371592, by decide⟩ :=
  accepted_of_selected 13 108757 ⟨371592, by decide⟩ ⟨13, 2, 0, 371592, 108757, 2073, 16384⟩
    (by decide) selected_cut_14365

theorem selected_cut_14366 : selected 8 ⟨371608, by decide⟩
    (prefixPartial 13 108758) = some ⟨13, 2, 0, 371608, 108758, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_108758_371608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108758 ⟨371608, by decide⟩ :=
  accepted_of_selected 13 108758 ⟨371608, by decide⟩ ⟨13, 2, 0, 371608, 108758, 1317, 16384⟩
    (by decide) selected_cut_14366

theorem selected_cut_14367 : selected 8 ⟨371613, by decide⟩
    (prefixPartial 13 108759) = some ⟨13, 2, 0, 371613, 108759, 905, 16384⟩ := by
  decide +kernel

theorem context_13_108759_371613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108759 ⟨371613, by decide⟩ :=
  accepted_of_selected 13 108759 ⟨371613, by decide⟩ ⟨13, 2, 0, 371613, 108759, 905, 16384⟩
    (by decide) selected_cut_14367

theorem unmarked_context_12_27189_371614 : frontier 9 ⟨371614, by decide⟩
    (prefixCache 12 27189) (prefixPartial 12 27189) = false := by
  decide +kernel

theorem node_context_12_27189_371614 : EJMOriginalGlobalDAGData.nodes 9 ⟨371614, by decide⟩ =
    .split (coordinate 12) (![⟨371570, by decide⟩,⟨371592, by decide⟩,⟨371608, by decide⟩,⟨371613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27189_371614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27189 ⟨371614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27189
    ⟨371614, by decide⟩ (by decide) (![⟨371570, by decide⟩,⟨371592, by decide⟩,⟨371608, by decide⟩,⟨371613, by decide⟩]) unmarked_context_12_27189_371614 node_context_12_27189_371614
  intro a
  fin_cases a
  · exact context_13_108756_371570
  · exact context_13_108757_371592
  · exact context_13_108758_371608
  · exact context_13_108759_371613

theorem selected_cut_14368 : selected 8 ⟨371620, by decide⟩
    (prefixPartial 13 108760) = some ⟨13, 2, 0, 371620, 108760, 533, 16384⟩ := by
  decide +kernel

theorem context_13_108760_371620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108760 ⟨371620, by decide⟩ :=
  accepted_of_selected 13 108760 ⟨371620, by decide⟩ ⟨13, 2, 0, 371620, 108760, 533, 16384⟩
    (by decide) selected_cut_14368

theorem selected_cut_14369 : selected 8 ⟨371642, by decide⟩
    (prefixPartial 13 108761) = some ⟨13, 2, 0, 371642, 108761, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_108761_371642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108761 ⟨371642, by decide⟩ :=
  accepted_of_selected 13 108761 ⟨371642, by decide⟩ ⟨13, 2, 0, 371642, 108761, 2069, 16384⟩
    (by decide) selected_cut_14369

theorem selected_cut_14370 : selected 8 ⟨371658, by decide⟩
    (prefixPartial 13 108762) = some ⟨13, 2, 0, 371658, 108762, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_108762_371658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108762 ⟨371658, by decide⟩ :=
  accepted_of_selected 13 108762 ⟨371658, by decide⟩ ⟨13, 2, 0, 371658, 108762, 1309, 16384⟩
    (by decide) selected_cut_14370

theorem selected_cut_14371 : selected 8 ⟨371663, by decide⟩
    (prefixPartial 13 108763) = some ⟨13, 2, 0, 371663, 108763, 913, 16384⟩ := by
  decide +kernel

theorem context_13_108763_371663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108763 ⟨371663, by decide⟩ :=
  accepted_of_selected 13 108763 ⟨371663, by decide⟩ ⟨13, 2, 0, 371663, 108763, 913, 16384⟩
    (by decide) selected_cut_14371

theorem unmarked_context_12_27190_371664 : frontier 9 ⟨371664, by decide⟩
    (prefixCache 12 27190) (prefixPartial 12 27190) = false := by
  decide +kernel

theorem node_context_12_27190_371664 : EJMOriginalGlobalDAGData.nodes 9 ⟨371664, by decide⟩ =
    .split (coordinate 12) (![⟨371620, by decide⟩,⟨371642, by decide⟩,⟨371658, by decide⟩,⟨371663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27190_371664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27190 ⟨371664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27190
    ⟨371664, by decide⟩ (by decide) (![⟨371620, by decide⟩,⟨371642, by decide⟩,⟨371658, by decide⟩,⟨371663, by decide⟩]) unmarked_context_12_27190_371664 node_context_12_27190_371664
  intro a
  fin_cases a
  · exact context_13_108760_371620
  · exact context_13_108761_371642
  · exact context_13_108762_371658
  · exact context_13_108763_371663

theorem selected_cut_14372 : selected 8 ⟨371672, by decide⟩
    (prefixPartial 13 108764) = some ⟨13, 2, 0, 371672, 108764, 629, 16384⟩ := by
  decide +kernel

theorem context_13_108764_371672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108764 ⟨371672, by decide⟩ :=
  accepted_of_selected 13 108764 ⟨371672, by decide⟩ ⟨13, 2, 0, 371672, 108764, 629, 16384⟩
    (by decide) selected_cut_14372

theorem selected_cut_14373 : selected 8 ⟨371698, by decide⟩
    (prefixPartial 13 108765) = some ⟨13, 2, 0, 371698, 108765, 2573, 16384⟩ := by
  decide +kernel

theorem context_13_108765_371698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108765 ⟨371698, by decide⟩ :=
  accepted_of_selected 13 108765 ⟨371698, by decide⟩ ⟨13, 2, 0, 371698, 108765, 2573, 16384⟩
    (by decide) selected_cut_14373

theorem selected_cut_14374 : selected 8 ⟨371720, by decide⟩
    (prefixPartial 13 108766) = some ⟨13, 2, 0, 371720, 108766, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_108766_371720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108766 ⟨371720, by decide⟩ :=
  accepted_of_selected 13 108766 ⟨371720, by decide⟩ ⟨13, 2, 0, 371720, 108766, 1489, 16384⟩
    (by decide) selected_cut_14374

theorem selected_cut_14375 : selected 8 ⟨371726, by decide⟩
    (prefixPartial 13 108767) = some ⟨13, 2, 0, 371726, 108767, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_108767_371726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108767 ⟨371726, by decide⟩ :=
  accepted_of_selected 13 108767 ⟨371726, by decide⟩ ⟨13, 2, 0, 371726, 108767, 1065, 16384⟩
    (by decide) selected_cut_14375

theorem unmarked_context_12_27191_371727 : frontier 9 ⟨371727, by decide⟩
    (prefixCache 12 27191) (prefixPartial 12 27191) = false := by
  decide +kernel

theorem node_context_12_27191_371727 : EJMOriginalGlobalDAGData.nodes 9 ⟨371727, by decide⟩ =
    .split (coordinate 12) (![⟨371672, by decide⟩,⟨371698, by decide⟩,⟨371720, by decide⟩,⟨371726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27191_371727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27191 ⟨371727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27191
    ⟨371727, by decide⟩ (by decide) (![⟨371672, by decide⟩,⟨371698, by decide⟩,⟨371720, by decide⟩,⟨371726, by decide⟩]) unmarked_context_12_27191_371727 node_context_12_27191_371727
  intro a
  fin_cases a
  · exact context_13_108764_371672
  · exact context_13_108765_371698
  · exact context_13_108766_371720
  · exact context_13_108767_371726

theorem unmarked_context_11_6797_371728 : frontier 10 ⟨371728, by decide⟩
    (prefixCache 11 6797) (prefixPartial 11 6797) = false := by
  decide +kernel

theorem node_context_11_6797_371728 : EJMOriginalGlobalDAGData.nodes 10 ⟨371728, by decide⟩ =
    .split (coordinate 11) (![⟨371561, by decide⟩,⟨371614, by decide⟩,⟨371664, by decide⟩,⟨371727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6797_371728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6797 ⟨371728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6797
    ⟨371728, by decide⟩ (by decide) (![⟨371561, by decide⟩,⟨371614, by decide⟩,⟨371664, by decide⟩,⟨371727, by decide⟩]) unmarked_context_11_6797_371728 node_context_11_6797_371728
  intro a
  fin_cases a
  · exact context_12_27188_371561
  · exact context_12_27189_371614
  · exact context_12_27190_371664
  · exact context_12_27191_371727

theorem selected_cut_14376 : selected 8 ⟨371734, by decide⟩
    (prefixPartial 13 108768) = some ⟨13, 2, 0, 371734, 108768, 353, 16384⟩ := by
  decide +kernel

theorem context_13_108768_371734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108768 ⟨371734, by decide⟩ :=
  accepted_of_selected 13 108768 ⟨371734, by decide⟩ ⟨13, 2, 0, 371734, 108768, 353, 16384⟩
    (by decide) selected_cut_14376

theorem selected_cut_14377 : selected 8 ⟨371764, by decide⟩
    (prefixPartial 13 108769) = some ⟨13, 2, 0, 371764, 108769, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_108769_371764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108769 ⟨371764, by decide⟩ :=
  accepted_of_selected 13 108769 ⟨371764, by decide⟩ ⟨13, 2, 0, 371764, 108769, 2249, 16384⟩
    (by decide) selected_cut_14377

theorem selected_cut_14378 : selected 8 ⟨371777, by decide⟩
    (prefixPartial 13 108770) = some ⟨13, 2, 0, 371777, 108770, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_108770_371777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108770 ⟨371777, by decide⟩ :=
  accepted_of_selected 13 108770 ⟨371777, by decide⟩ ⟨13, 2, 0, 371777, 108770, 1173, 16384⟩
    (by decide) selected_cut_14378

theorem selected_cut_14379 : selected 8 ⟨371783, by decide⟩
    (prefixPartial 13 108771) = some ⟨13, 2, 0, 371783, 108771, 905, 16384⟩ := by
  decide +kernel

theorem context_13_108771_371783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108771 ⟨371783, by decide⟩ :=
  accepted_of_selected 13 108771 ⟨371783, by decide⟩ ⟨13, 2, 0, 371783, 108771, 905, 16384⟩
    (by decide) selected_cut_14379

theorem unmarked_context_12_27192_371784 : frontier 9 ⟨371784, by decide⟩
    (prefixCache 12 27192) (prefixPartial 12 27192) = false := by
  decide +kernel

theorem node_context_12_27192_371784 : EJMOriginalGlobalDAGData.nodes 9 ⟨371784, by decide⟩ =
    .split (coordinate 12) (![⟨371734, by decide⟩,⟨371764, by decide⟩,⟨371777, by decide⟩,⟨371783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27192_371784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27192 ⟨371784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27192
    ⟨371784, by decide⟩ (by decide) (![⟨371734, by decide⟩,⟨371764, by decide⟩,⟨371777, by decide⟩,⟨371783, by decide⟩]) unmarked_context_12_27192_371784 node_context_12_27192_371784
  intro a
  fin_cases a
  · exact context_13_108768_371734
  · exact context_13_108769_371764
  · exact context_13_108770_371777
  · exact context_13_108771_371783

theorem selected_cut_14380 : selected 8 ⟨371790, by decide⟩
    (prefixPartial 13 108772) = some ⟨13, 2, 0, 371790, 108772, 373, 16384⟩ := by
  decide +kernel

theorem context_13_108772_371790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108772 ⟨371790, by decide⟩ :=
  accepted_of_selected 13 108772 ⟨371790, by decide⟩ ⟨13, 2, 0, 371790, 108772, 373, 16384⟩
    (by decide) selected_cut_14380

theorem selected_cut_14381 : selected 8 ⟨371815, by decide⟩
    (prefixPartial 13 108773) = some ⟨13, 2, 0, 371815, 108773, 2149, 16384⟩ := by
  decide +kernel

theorem context_13_108773_371815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108773 ⟨371815, by decide⟩ :=
  accepted_of_selected 13 108773 ⟨371815, by decide⟩ ⟨13, 2, 0, 371815, 108773, 2149, 16384⟩
    (by decide) selected_cut_14381

theorem selected_cut_14382 : selected 8 ⟨371831, by decide⟩
    (prefixPartial 13 108774) = some ⟨13, 2, 0, 371831, 108774, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_108774_371831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108774 ⟨371831, by decide⟩ :=
  accepted_of_selected 13 108774 ⟨371831, by decide⟩ ⟨13, 2, 0, 371831, 108774, 1293, 16384⟩
    (by decide) selected_cut_14382

theorem selected_cut_14383 : selected 8 ⟨371835, by decide⟩
    (prefixPartial 13 108775) = some ⟨13, 2, 0, 371835, 108775, 909, 16384⟩ := by
  decide +kernel

theorem context_13_108775_371835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108775 ⟨371835, by decide⟩ :=
  accepted_of_selected 13 108775 ⟨371835, by decide⟩ ⟨13, 2, 0, 371835, 108775, 909, 16384⟩
    (by decide) selected_cut_14383

theorem unmarked_context_12_27193_371836 : frontier 9 ⟨371836, by decide⟩
    (prefixCache 12 27193) (prefixPartial 12 27193) = false := by
  decide +kernel

theorem node_context_12_27193_371836 : EJMOriginalGlobalDAGData.nodes 9 ⟨371836, by decide⟩ =
    .split (coordinate 12) (![⟨371790, by decide⟩,⟨371815, by decide⟩,⟨371831, by decide⟩,⟨371835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27193_371836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27193 ⟨371836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27193
    ⟨371836, by decide⟩ (by decide) (![⟨371790, by decide⟩,⟨371815, by decide⟩,⟨371831, by decide⟩,⟨371835, by decide⟩]) unmarked_context_12_27193_371836 node_context_12_27193_371836
  intro a
  fin_cases a
  · exact context_13_108772_371790
  · exact context_13_108773_371815
  · exact context_13_108774_371831
  · exact context_13_108775_371835

theorem selected_cut_14384 : selected 8 ⟨371846, by decide⟩
    (prefixPartial 13 108776) = some ⟨13, 2, 0, 371846, 108776, 413, 16384⟩ := by
  decide +kernel

theorem context_13_108776_371846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108776 ⟨371846, by decide⟩ :=
  accepted_of_selected 13 108776 ⟨371846, by decide⟩ ⟨13, 2, 0, 371846, 108776, 413, 16384⟩
    (by decide) selected_cut_14384

theorem selected_cut_14385 : selected 8 ⟨371905, by decide⟩
    (prefixPartial 13 108777) = some ⟨13, 2, 0, 371905, 108777, 3693, 16384⟩ := by
  decide +kernel

theorem context_13_108777_371905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108777 ⟨371905, by decide⟩ :=
  accepted_of_selected 13 108777 ⟨371905, by decide⟩ ⟨13, 2, 0, 371905, 108777, 3693, 16384⟩
    (by decide) selected_cut_14385

theorem selected_cut_14386 : selected 8 ⟨371931, by decide⟩
    (prefixPartial 13 108778) = some ⟨13, 2, 0, 371931, 108778, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_108778_371931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108778 ⟨371931, by decide⟩ :=
  accepted_of_selected 13 108778 ⟨371931, by decide⟩ ⟨13, 2, 0, 371931, 108778, 2129, 16384⟩
    (by decide) selected_cut_14386

theorem selected_cut_14387 : selected 8 ⟨371943, by decide⟩
    (prefixPartial 13 108779) = some ⟨13, 2, 0, 371943, 108779, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_108779_371943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108779 ⟨371943, by decide⟩ :=
  accepted_of_selected 13 108779 ⟨371943, by decide⟩ ⟨13, 2, 0, 371943, 108779, 1225, 16384⟩
    (by decide) selected_cut_14387

theorem unmarked_context_12_27194_371944 : frontier 9 ⟨371944, by decide⟩
    (prefixCache 12 27194) (prefixPartial 12 27194) = false := by
  decide +kernel

theorem node_context_12_27194_371944 : EJMOriginalGlobalDAGData.nodes 9 ⟨371944, by decide⟩ =
    .split (coordinate 12) (![⟨371846, by decide⟩,⟨371905, by decide⟩,⟨371931, by decide⟩,⟨371943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27194_371944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27194 ⟨371944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27194
    ⟨371944, by decide⟩ (by decide) (![⟨371846, by decide⟩,⟨371905, by decide⟩,⟨371931, by decide⟩,⟨371943, by decide⟩]) unmarked_context_12_27194_371944 node_context_12_27194_371944
  intro a
  fin_cases a
  · exact context_13_108776_371846
  · exact context_13_108777_371905
  · exact context_13_108778_371931
  · exact context_13_108779_371943

theorem selected_cut_14388 : selected 8 ⟨371951, by decide⟩
    (prefixPartial 13 108780) = some ⟨13, 2, 0, 371951, 108780, 297, 16384⟩ := by
  decide +kernel

theorem context_13_108780_371951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108780 ⟨371951, by decide⟩ :=
  accepted_of_selected 13 108780 ⟨371951, by decide⟩ ⟨13, 2, 0, 371951, 108780, 297, 16384⟩
    (by decide) selected_cut_14388

theorem selected_cut_14389 : selected 8 ⟨371985, by decide⟩
    (prefixPartial 13 108781) = some ⟨13, 2, 0, 371985, 108781, 2713, 16384⟩ := by
  decide +kernel

theorem context_13_108781_371985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108781 ⟨371985, by decide⟩ :=
  accepted_of_selected 13 108781 ⟨371985, by decide⟩ ⟨13, 2, 0, 371985, 108781, 2713, 16384⟩
    (by decide) selected_cut_14389

theorem selected_cut_14390 : selected 8 ⟨372003, by decide⟩
    (prefixPartial 13 108782) = some ⟨13, 2, 0, 372003, 108782, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_108782_372003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108782 ⟨372003, by decide⟩ :=
  accepted_of_selected 13 108782 ⟨372003, by decide⟩ ⟨13, 2, 0, 372003, 108782, 1365, 16384⟩
    (by decide) selected_cut_14390

theorem selected_cut_14391 : selected 8 ⟨372014, by decide⟩
    (prefixPartial 13 108783) = some ⟨13, 2, 0, 372014, 108783, 993, 16384⟩ := by
  decide +kernel

theorem context_13_108783_372014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108783 ⟨372014, by decide⟩ :=
  accepted_of_selected 13 108783 ⟨372014, by decide⟩ ⟨13, 2, 0, 372014, 108783, 993, 16384⟩
    (by decide) selected_cut_14391

theorem unmarked_context_12_27195_372015 : frontier 9 ⟨372015, by decide⟩
    (prefixCache 12 27195) (prefixPartial 12 27195) = false := by
  decide +kernel

theorem node_context_12_27195_372015 : EJMOriginalGlobalDAGData.nodes 9 ⟨372015, by decide⟩ =
    .split (coordinate 12) (![⟨371951, by decide⟩,⟨371985, by decide⟩,⟨372003, by decide⟩,⟨372014, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27195_372015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27195 ⟨372015, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27195
    ⟨372015, by decide⟩ (by decide) (![⟨371951, by decide⟩,⟨371985, by decide⟩,⟨372003, by decide⟩,⟨372014, by decide⟩]) unmarked_context_12_27195_372015 node_context_12_27195_372015
  intro a
  fin_cases a
  · exact context_13_108780_371951
  · exact context_13_108781_371985
  · exact context_13_108782_372003
  · exact context_13_108783_372014

theorem unmarked_context_11_6798_372016 : frontier 10 ⟨372016, by decide⟩
    (prefixCache 11 6798) (prefixPartial 11 6798) = false := by
  decide +kernel

theorem node_context_11_6798_372016 : EJMOriginalGlobalDAGData.nodes 10 ⟨372016, by decide⟩ =
    .split (coordinate 11) (![⟨371784, by decide⟩,⟨371836, by decide⟩,⟨371944, by decide⟩,⟨372015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6798_372016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6798 ⟨372016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6798
    ⟨372016, by decide⟩ (by decide) (![⟨371784, by decide⟩,⟨371836, by decide⟩,⟨371944, by decide⟩,⟨372015, by decide⟩]) unmarked_context_11_6798_372016 node_context_11_6798_372016
  intro a
  fin_cases a
  · exact context_12_27192_371784
  · exact context_12_27193_371836
  · exact context_12_27194_371944
  · exact context_12_27195_372015

theorem selected_cut_14392 : selected 8 ⟨372019, by decide⟩
    (prefixPartial 13 108784) = some ⟨13, 2, 0, 372019, 108784, 153, 16384⟩ := by
  decide +kernel

theorem context_13_108784_372019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108784 ⟨372019, by decide⟩ :=
  accepted_of_selected 13 108784 ⟨372019, by decide⟩ ⟨13, 2, 0, 372019, 108784, 153, 16384⟩
    (by decide) selected_cut_14392

theorem selected_cut_14393 : selected 8 ⟨372042, by decide⟩
    (prefixPartial 13 108785) = some ⟨13, 2, 0, 372042, 108785, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_108785_372042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108785 ⟨372042, by decide⟩ :=
  accepted_of_selected 13 108785 ⟨372042, by decide⟩ ⟨13, 2, 0, 372042, 108785, 2373, 16384⟩
    (by decide) selected_cut_14393

theorem selected_cut_14394 : selected 8 ⟨372056, by decide⟩
    (prefixPartial 13 108786) = some ⟨13, 2, 0, 372056, 108786, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_108786_372056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108786 ⟨372056, by decide⟩ :=
  accepted_of_selected 13 108786 ⟨372056, by decide⟩ ⟨13, 2, 0, 372056, 108786, 1189, 16384⟩
    (by decide) selected_cut_14394

theorem selected_cut_14395 : selected 8 ⟨372063, by decide⟩
    (prefixPartial 13 108787) = some ⟨13, 2, 0, 372063, 108787, 909, 16384⟩ := by
  decide +kernel

theorem context_13_108787_372063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108787 ⟨372063, by decide⟩ :=
  accepted_of_selected 13 108787 ⟨372063, by decide⟩ ⟨13, 2, 0, 372063, 108787, 909, 16384⟩
    (by decide) selected_cut_14395

theorem unmarked_context_12_27196_372064 : frontier 9 ⟨372064, by decide⟩
    (prefixCache 12 27196) (prefixPartial 12 27196) = false := by
  decide +kernel

theorem node_context_12_27196_372064 : EJMOriginalGlobalDAGData.nodes 9 ⟨372064, by decide⟩ =
    .split (coordinate 12) (![⟨372019, by decide⟩,⟨372042, by decide⟩,⟨372056, by decide⟩,⟨372063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27196_372064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27196 ⟨372064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27196
    ⟨372064, by decide⟩ (by decide) (![⟨372019, by decide⟩,⟨372042, by decide⟩,⟨372056, by decide⟩,⟨372063, by decide⟩]) unmarked_context_12_27196_372064 node_context_12_27196_372064
  intro a
  fin_cases a
  · exact context_13_108784_372019
  · exact context_13_108785_372042
  · exact context_13_108786_372056
  · exact context_13_108787_372063

theorem selected_cut_14396 : selected 8 ⟨372068, by decide⟩
    (prefixPartial 13 108788) = some ⟨13, 2, 0, 372068, 108788, 177, 16384⟩ := by
  decide +kernel

theorem context_13_108788_372068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108788 ⟨372068, by decide⟩ :=
  accepted_of_selected 13 108788 ⟨372068, by decide⟩ ⟨13, 2, 0, 372068, 108788, 177, 16384⟩
    (by decide) selected_cut_14396

theorem selected_cut_14397 : selected 8 ⟨372095, by decide⟩
    (prefixPartial 13 108789) = some ⟨13, 2, 0, 372095, 108789, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_108789_372095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108789 ⟨372095, by decide⟩ :=
  accepted_of_selected 13 108789 ⟨372095, by decide⟩ ⟨13, 2, 0, 372095, 108789, 2301, 16384⟩
    (by decide) selected_cut_14397

theorem selected_cut_14398 : selected 8 ⟨372110, by decide⟩
    (prefixPartial 13 108790) = some ⟨13, 2, 0, 372110, 108790, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_108790_372110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108790 ⟨372110, by decide⟩ :=
  accepted_of_selected 13 108790 ⟨372110, by decide⟩ ⟨13, 2, 0, 372110, 108790, 1233, 16384⟩
    (by decide) selected_cut_14398

theorem selected_cut_14399 : selected 8 ⟨372116, by decide⟩
    (prefixPartial 13 108791) = some ⟨13, 2, 0, 372116, 108791, 837, 16384⟩ := by
  decide +kernel

theorem context_13_108791_372116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108791 ⟨372116, by decide⟩ :=
  accepted_of_selected 13 108791 ⟨372116, by decide⟩ ⟨13, 2, 0, 372116, 108791, 837, 16384⟩
    (by decide) selected_cut_14399

theorem unmarked_context_12_27197_372117 : frontier 9 ⟨372117, by decide⟩
    (prefixCache 12 27197) (prefixPartial 12 27197) = false := by
  decide +kernel

theorem node_context_12_27197_372117 : EJMOriginalGlobalDAGData.nodes 9 ⟨372117, by decide⟩ =
    .split (coordinate 12) (![⟨372068, by decide⟩,⟨372095, by decide⟩,⟨372110, by decide⟩,⟨372116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27197_372117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27197 ⟨372117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27197
    ⟨372117, by decide⟩ (by decide) (![⟨372068, by decide⟩,⟨372095, by decide⟩,⟨372110, by decide⟩,⟨372116, by decide⟩]) unmarked_context_12_27197_372117 node_context_12_27197_372117
  intro a
  fin_cases a
  · exact context_13_108788_372068
  · exact context_13_108789_372095
  · exact context_13_108790_372110
  · exact context_13_108791_372116

theorem selected_cut_14400 : selected 8 ⟨372120, by decide⟩
    (prefixPartial 13 108792) = some ⟨13, 2, 0, 372120, 108792, 85, 16384⟩ := by
  decide +kernel

theorem context_13_108792_372120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108792 ⟨372120, by decide⟩ :=
  accepted_of_selected 13 108792 ⟨372120, by decide⟩ ⟨13, 2, 0, 372120, 108792, 85, 16384⟩
    (by decide) selected_cut_14400

theorem selected_cut_14401 : selected 8 ⟨372144, by decide⟩
    (prefixPartial 13 108793) = some ⟨13, 2, 0, 372144, 108793, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_108793_372144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108793 ⟨372144, by decide⟩ :=
  accepted_of_selected 13 108793 ⟨372144, by decide⟩ ⟨13, 2, 0, 372144, 108793, 2117, 16384⟩
    (by decide) selected_cut_14401

theorem selected_cut_14402 : selected 8 ⟨372162, by decide⟩
    (prefixPartial 13 108794) = some ⟨13, 2, 0, 372162, 108794, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_108794_372162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108794 ⟨372162, by decide⟩ :=
  accepted_of_selected 13 108794 ⟨372162, by decide⟩ ⟨13, 2, 0, 372162, 108794, 1185, 16384⟩
    (by decide) selected_cut_14402

theorem selected_cut_14403 : selected 8 ⟨372170, by decide⟩
    (prefixPartial 13 108795) = some ⟨13, 2, 0, 372170, 108795, 793, 16384⟩ := by
  decide +kernel

theorem context_13_108795_372170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108795 ⟨372170, by decide⟩ :=
  accepted_of_selected 13 108795 ⟨372170, by decide⟩ ⟨13, 2, 0, 372170, 108795, 793, 16384⟩
    (by decide) selected_cut_14403

theorem unmarked_context_12_27198_372171 : frontier 9 ⟨372171, by decide⟩
    (prefixCache 12 27198) (prefixPartial 12 27198) = false := by
  decide +kernel

theorem node_context_12_27198_372171 : EJMOriginalGlobalDAGData.nodes 9 ⟨372171, by decide⟩ =
    .split (coordinate 12) (![⟨372120, by decide⟩,⟨372144, by decide⟩,⟨372162, by decide⟩,⟨372170, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27198_372171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27198 ⟨372171, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27198
    ⟨372171, by decide⟩ (by decide) (![⟨372120, by decide⟩,⟨372144, by decide⟩,⟨372162, by decide⟩,⟨372170, by decide⟩]) unmarked_context_12_27198_372171 node_context_12_27198_372171
  intro a
  fin_cases a
  · exact context_13_108792_372120
  · exact context_13_108793_372144
  · exact context_13_108794_372162
  · exact context_13_108795_372170

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
