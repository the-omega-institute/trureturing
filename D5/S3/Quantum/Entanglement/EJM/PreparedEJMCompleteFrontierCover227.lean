/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover226
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_75294_557403 : frontier 9 ⟨557403, by decide⟩
    (prefixCache 12 75294) (prefixPartial 12 75294) = false := by
  decide +kernel

theorem node_context_12_75294_557403 : EJMOriginalGlobalDAGData.nodes 9 ⟨557403, by decide⟩ =
    .split (coordinate 12) (![⟨557353, by decide⟩,⟨557381, by decide⟩,⟨557396, by decide⟩,⟨557402, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75294_557403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75294 ⟨557403, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75294
    ⟨557403, by decide⟩ (by decide) (![⟨557353, by decide⟩,⟨557381, by decide⟩,⟨557396, by decide⟩,⟨557402, by decide⟩]) unmarked_context_12_75294_557403 node_context_12_75294_557403
  intro a
  fin_cases a
  · exact context_13_301176_557353
  · exact context_13_301177_557381
  · exact context_13_301178_557396
  · exact context_13_301179_557402

theorem selected_cut_21796 : selected 8 ⟨557431, by decide⟩
    (prefixPartial 13 301180) = some ⟨13, 2, 0, 557431, 301180, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_301180_557431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301180 ⟨557431, by decide⟩ :=
  accepted_of_selected 13 301180 ⟨557431, by decide⟩ ⟨13, 2, 0, 557431, 301180, 1373, 16384⟩
    (by decide) selected_cut_21796

theorem selected_cut_21797 : selected 8 ⟨557464, by decide⟩
    (prefixPartial 13 301181) = some ⟨13, 2, 0, 557464, 301181, 2793, 16384⟩ := by
  decide +kernel

theorem context_13_301181_557464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301181 ⟨557464, by decide⟩ :=
  accepted_of_selected 13 301181 ⟨557464, by decide⟩ ⟨13, 2, 0, 557464, 301181, 2793, 16384⟩
    (by decide) selected_cut_21797

theorem selected_cut_21798 : selected 8 ⟨557483, by decide⟩
    (prefixPartial 13 301182) = some ⟨13, 2, 0, 557483, 301182, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_301182_557483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301182 ⟨557483, by decide⟩ :=
  accepted_of_selected 13 301182 ⟨557483, by decide⟩ ⟨13, 2, 0, 557483, 301182, 1701, 16384⟩
    (by decide) selected_cut_21798

theorem selected_cut_21799 : selected 8 ⟨557489, by decide⟩
    (prefixPartial 13 301183) = some ⟨13, 2, 0, 557489, 301183, 921, 16384⟩ := by
  decide +kernel

theorem context_13_301183_557489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301183 ⟨557489, by decide⟩ :=
  accepted_of_selected 13 301183 ⟨557489, by decide⟩ ⟨13, 2, 0, 557489, 301183, 921, 16384⟩
    (by decide) selected_cut_21799

theorem unmarked_context_12_75295_557490 : frontier 9 ⟨557490, by decide⟩
    (prefixCache 12 75295) (prefixPartial 12 75295) = false := by
  decide +kernel

theorem node_context_12_75295_557490 : EJMOriginalGlobalDAGData.nodes 9 ⟨557490, by decide⟩ =
    .split (coordinate 12) (![⟨557431, by decide⟩,⟨557464, by decide⟩,⟨557483, by decide⟩,⟨557489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75295_557490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75295 ⟨557490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75295
    ⟨557490, by decide⟩ (by decide) (![⟨557431, by decide⟩,⟨557464, by decide⟩,⟨557483, by decide⟩,⟨557489, by decide⟩]) unmarked_context_12_75295_557490 node_context_12_75295_557490
  intro a
  fin_cases a
  · exact context_13_301180_557431
  · exact context_13_301181_557464
  · exact context_13_301182_557483
  · exact context_13_301183_557489

theorem unmarked_context_11_18823_557491 : frontier 10 ⟨557491, by decide⟩
    (prefixCache 11 18823) (prefixPartial 11 18823) = false := by
  decide +kernel

theorem node_context_11_18823_557491 : EJMOriginalGlobalDAGData.nodes 10 ⟨557491, by decide⟩ =
    .split (coordinate 11) (![⟨557263, by decide⟩,⟨557331, by decide⟩,⟨557403, by decide⟩,⟨557490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18823_557491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18823 ⟨557491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18823
    ⟨557491, by decide⟩ (by decide) (![⟨557263, by decide⟩,⟨557331, by decide⟩,⟨557403, by decide⟩,⟨557490, by decide⟩]) unmarked_context_11_18823_557491 node_context_11_18823_557491
  intro a
  fin_cases a
  · exact context_12_75292_557263
  · exact context_12_75293_557331
  · exact context_12_75294_557403
  · exact context_12_75295_557490

theorem unmarked_context_10_4705_557492 : frontier 11 ⟨557492, by decide⟩
    (prefixCache 10 4705) (prefixPartial 10 4705) = false := by
  decide +kernel

theorem node_context_10_4705_557492 : EJMOriginalGlobalDAGData.nodes 11 ⟨557492, by decide⟩ =
    .split (coordinate 10) (![⟨556535, by decide⟩,⟨556771, by decide⟩,⟨557142, by decide⟩,⟨557491, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4705_557492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4705 ⟨557492, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4705
    ⟨557492, by decide⟩ (by decide) (![⟨556535, by decide⟩,⟨556771, by decide⟩,⟨557142, by decide⟩,⟨557491, by decide⟩]) unmarked_context_10_4705_557492 node_context_10_4705_557492
  intro a
  fin_cases a
  · exact context_11_18820_556535
  · exact context_11_18821_556771
  · exact context_11_18822_557142
  · exact context_11_18823_557491

theorem selected_cut_21800 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 75296) = some ⟨12, 1, 0, 435790, 75296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75296_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75296 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 75296 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 75296, 1, 65536⟩
    (by decide) selected_cut_21800

theorem selected_cut_21801 : selected 8 ⟨557506, by decide⟩
    (prefixPartial 13 301188) = some ⟨13, 2, 0, 557506, 301188, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_301188_557506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301188 ⟨557506, by decide⟩ :=
  accepted_of_selected 13 301188 ⟨557506, by decide⟩ ⟨13, 2, 0, 557506, 301188, 1045, 16384⟩
    (by decide) selected_cut_21801

theorem selected_cut_21802 : selected 8 ⟨557540, by decide⟩
    (prefixPartial 13 301189) = some ⟨13, 2, 0, 557540, 301189, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_301189_557540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301189 ⟨557540, by decide⟩ :=
  accepted_of_selected 13 301189 ⟨557540, by decide⟩ ⟨13, 2, 0, 557540, 301189, 2097, 16384⟩
    (by decide) selected_cut_21802

theorem selected_cut_21803 : selected 8 ⟨557557, by decide⟩
    (prefixPartial 13 301190) = some ⟨13, 2, 0, 557557, 301190, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_301190_557557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301190 ⟨557557, by decide⟩ :=
  accepted_of_selected 13 301190 ⟨557557, by decide⟩ ⟨13, 2, 0, 557557, 301190, 1305, 16384⟩
    (by decide) selected_cut_21803

theorem selected_cut_21804 : selected 8 ⟨557562, by decide⟩
    (prefixPartial 13 301191) = some ⟨13, 2, 0, 557562, 301191, 777, 16384⟩ := by
  decide +kernel

theorem context_13_301191_557562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301191 ⟨557562, by decide⟩ :=
  accepted_of_selected 13 301191 ⟨557562, by decide⟩ ⟨13, 2, 0, 557562, 301191, 777, 16384⟩
    (by decide) selected_cut_21804

theorem unmarked_context_12_75297_557563 : frontier 9 ⟨557563, by decide⟩
    (prefixCache 12 75297) (prefixPartial 12 75297) = false := by
  decide +kernel

theorem node_context_12_75297_557563 : EJMOriginalGlobalDAGData.nodes 9 ⟨557563, by decide⟩ =
    .split (coordinate 12) (![⟨557506, by decide⟩,⟨557540, by decide⟩,⟨557557, by decide⟩,⟨557562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75297_557563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75297 ⟨557563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75297
    ⟨557563, by decide⟩ (by decide) (![⟨557506, by decide⟩,⟨557540, by decide⟩,⟨557557, by decide⟩,⟨557562, by decide⟩]) unmarked_context_12_75297_557563 node_context_12_75297_557563
  intro a
  fin_cases a
  · exact context_13_301188_557506
  · exact context_13_301189_557540
  · exact context_13_301190_557557
  · exact context_13_301191_557562

theorem selected_cut_21805 : selected 8 ⟨557579, by decide⟩
    (prefixPartial 13 301192) = some ⟨13, 2, 0, 557579, 301192, 957, 16384⟩ := by
  decide +kernel

theorem context_13_301192_557579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301192 ⟨557579, by decide⟩ :=
  accepted_of_selected 13 301192 ⟨557579, by decide⟩ ⟨13, 2, 0, 557579, 301192, 957, 16384⟩
    (by decide) selected_cut_21805

theorem selected_cut_21806 : selected 8 ⟨557599, by decide⟩
    (prefixPartial 13 301193) = some ⟨13, 2, 0, 557599, 301193, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_301193_557599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301193 ⟨557599, by decide⟩ :=
  accepted_of_selected 13 301193 ⟨557599, by decide⟩ ⟨13, 2, 0, 557599, 301193, 1545, 16384⟩
    (by decide) selected_cut_21806

theorem selected_cut_21807 : selected 8 ⟨557613, by decide⟩
    (prefixPartial 13 301194) = some ⟨13, 2, 0, 557613, 301194, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_301194_557613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301194 ⟨557613, by decide⟩ :=
  accepted_of_selected 13 301194 ⟨557613, by decide⟩ ⟨13, 2, 0, 557613, 301194, 1125, 16384⟩
    (by decide) selected_cut_21807

theorem selected_cut_21808 : selected 8 ⟨557617, by decide⟩
    (prefixPartial 13 301195) = some ⟨13, 2, 0, 557617, 301195, 685, 16384⟩ := by
  decide +kernel

theorem context_13_301195_557617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301195 ⟨557617, by decide⟩ :=
  accepted_of_selected 13 301195 ⟨557617, by decide⟩ ⟨13, 2, 0, 557617, 301195, 685, 16384⟩
    (by decide) selected_cut_21808

theorem unmarked_context_12_75298_557618 : frontier 9 ⟨557618, by decide⟩
    (prefixCache 12 75298) (prefixPartial 12 75298) = false := by
  decide +kernel

theorem node_context_12_75298_557618 : EJMOriginalGlobalDAGData.nodes 9 ⟨557618, by decide⟩ =
    .split (coordinate 12) (![⟨557579, by decide⟩,⟨557599, by decide⟩,⟨557613, by decide⟩,⟨557617, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75298_557618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75298 ⟨557618, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75298
    ⟨557618, by decide⟩ (by decide) (![⟨557579, by decide⟩,⟨557599, by decide⟩,⟨557613, by decide⟩,⟨557617, by decide⟩]) unmarked_context_12_75298_557618 node_context_12_75298_557618
  intro a
  fin_cases a
  · exact context_13_301192_557579
  · exact context_13_301193_557599
  · exact context_13_301194_557613
  · exact context_13_301195_557617

theorem selected_cut_21809 : selected 8 ⟨557640, by decide⟩
    (prefixPartial 13 301196) = some ⟨13, 2, 0, 557640, 301196, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_301196_557640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301196 ⟨557640, by decide⟩ :=
  accepted_of_selected 13 301196 ⟨557640, by decide⟩ ⟨13, 2, 0, 557640, 301196, 1329, 16384⟩
    (by decide) selected_cut_21809

theorem selected_cut_21810 : selected 8 ⟨557665, by decide⟩
    (prefixPartial 13 301197) = some ⟨13, 2, 0, 557665, 301197, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_301197_557665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301197 ⟨557665, by decide⟩ :=
  accepted_of_selected 13 301197 ⟨557665, by decide⟩ ⟨13, 2, 0, 557665, 301197, 2289, 16384⟩
    (by decide) selected_cut_21810

theorem selected_cut_21811 : selected 8 ⟨557686, by decide⟩
    (prefixPartial 13 301198) = some ⟨13, 2, 0, 557686, 301198, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_301198_557686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301198 ⟨557686, by decide⟩ :=
  accepted_of_selected 13 301198 ⟨557686, by decide⟩ ⟨13, 2, 0, 557686, 301198, 1601, 16384⟩
    (by decide) selected_cut_21811

theorem selected_cut_21812 : selected 8 ⟨557691, by decide⟩
    (prefixPartial 13 301199) = some ⟨13, 2, 0, 557691, 301199, 761, 16384⟩ := by
  decide +kernel

theorem context_13_301199_557691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301199 ⟨557691, by decide⟩ :=
  accepted_of_selected 13 301199 ⟨557691, by decide⟩ ⟨13, 2, 0, 557691, 301199, 761, 16384⟩
    (by decide) selected_cut_21812

theorem unmarked_context_12_75299_557692 : frontier 9 ⟨557692, by decide⟩
    (prefixCache 12 75299) (prefixPartial 12 75299) = false := by
  decide +kernel

theorem node_context_12_75299_557692 : EJMOriginalGlobalDAGData.nodes 9 ⟨557692, by decide⟩ =
    .split (coordinate 12) (![⟨557640, by decide⟩,⟨557665, by decide⟩,⟨557686, by decide⟩,⟨557691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75299_557692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75299 ⟨557692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75299
    ⟨557692, by decide⟩ (by decide) (![⟨557640, by decide⟩,⟨557665, by decide⟩,⟨557686, by decide⟩,⟨557691, by decide⟩]) unmarked_context_12_75299_557692 node_context_12_75299_557692
  intro a
  fin_cases a
  · exact context_13_301196_557640
  · exact context_13_301197_557665
  · exact context_13_301198_557686
  · exact context_13_301199_557691

theorem unmarked_context_11_18824_557693 : frontier 10 ⟨557693, by decide⟩
    (prefixCache 11 18824) (prefixPartial 11 18824) = false := by
  decide +kernel

theorem node_context_11_18824_557693 : EJMOriginalGlobalDAGData.nodes 10 ⟨557693, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨557563, by decide⟩,⟨557618, by decide⟩,⟨557692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18824_557693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18824 ⟨557693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18824
    ⟨557693, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨557563, by decide⟩,⟨557618, by decide⟩,⟨557692, by decide⟩]) unmarked_context_11_18824_557693 node_context_11_18824_557693
  intro a
  fin_cases a
  · exact context_12_75296_435790
  · exact context_12_75297_557563
  · exact context_12_75298_557618
  · exact context_12_75299_557692

theorem selected_cut_21813 : selected 9 ⟨557793, by decide⟩
    (prefixPartial 12 75300) = some ⟨12, 2, 0, 557793, 75300, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_75300_557793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75300 ⟨557793, by decide⟩ :=
  accepted_of_selected 12 75300 ⟨557793, by decide⟩ ⟨12, 2, 0, 557793, 75300, 4073, 65536⟩
    (by decide) selected_cut_21813

theorem selected_cut_21814 : selected 8 ⟨557810, by decide⟩
    (prefixPartial 13 301204) = some ⟨13, 2, 0, 557810, 301204, 949, 16384⟩ := by
  decide +kernel

theorem context_13_301204_557810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301204 ⟨557810, by decide⟩ :=
  accepted_of_selected 13 301204 ⟨557810, by decide⟩ ⟨13, 2, 0, 557810, 301204, 949, 16384⟩
    (by decide) selected_cut_21814

theorem selected_cut_21815 : selected 8 ⟨557835, by decide⟩
    (prefixPartial 13 301205) = some ⟨13, 2, 0, 557835, 301205, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_301205_557835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301205 ⟨557835, by decide⟩ :=
  accepted_of_selected 13 301205 ⟨557835, by decide⟩ ⟨13, 2, 0, 557835, 301205, 1773, 16384⟩
    (by decide) selected_cut_21815

theorem selected_cut_21816 : selected 8 ⟨557851, by decide⟩
    (prefixPartial 13 301206) = some ⟨13, 2, 0, 557851, 301206, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_301206_557851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301206 ⟨557851, by decide⟩ :=
  accepted_of_selected 13 301206 ⟨557851, by decide⟩ ⟨13, 2, 0, 557851, 301206, 1237, 16384⟩
    (by decide) selected_cut_21816

theorem selected_cut_21817 : selected 8 ⟨557855, by decide⟩
    (prefixPartial 13 301207) = some ⟨13, 2, 0, 557855, 301207, 829, 16384⟩ := by
  decide +kernel

theorem context_13_301207_557855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301207 ⟨557855, by decide⟩ :=
  accepted_of_selected 13 301207 ⟨557855, by decide⟩ ⟨13, 2, 0, 557855, 301207, 829, 16384⟩
    (by decide) selected_cut_21817

theorem unmarked_context_12_75301_557856 : frontier 9 ⟨557856, by decide⟩
    (prefixCache 12 75301) (prefixPartial 12 75301) = false := by
  decide +kernel

theorem node_context_12_75301_557856 : EJMOriginalGlobalDAGData.nodes 9 ⟨557856, by decide⟩ =
    .split (coordinate 12) (![⟨557810, by decide⟩,⟨557835, by decide⟩,⟨557851, by decide⟩,⟨557855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75301_557856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75301 ⟨557856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75301
    ⟨557856, by decide⟩ (by decide) (![⟨557810, by decide⟩,⟨557835, by decide⟩,⟨557851, by decide⟩,⟨557855, by decide⟩]) unmarked_context_12_75301_557856 node_context_12_75301_557856
  intro a
  fin_cases a
  · exact context_13_301204_557810
  · exact context_13_301205_557835
  · exact context_13_301206_557851
  · exact context_13_301207_557855

theorem selected_cut_21818 : selected 8 ⟨557872, by decide⟩
    (prefixPartial 13 301208) = some ⟨13, 2, 0, 557872, 301208, 901, 16384⟩ := by
  decide +kernel

theorem context_13_301208_557872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301208 ⟨557872, by decide⟩ :=
  accepted_of_selected 13 301208 ⟨557872, by decide⟩ ⟨13, 2, 0, 557872, 301208, 901, 16384⟩
    (by decide) selected_cut_21818

theorem selected_cut_21819 : selected 8 ⟨557894, by decide⟩
    (prefixPartial 13 301209) = some ⟨13, 2, 0, 557894, 301209, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_301209_557894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301209 ⟨557894, by decide⟩ :=
  accepted_of_selected 13 301209 ⟨557894, by decide⟩ ⟨13, 2, 0, 557894, 301209, 1533, 16384⟩
    (by decide) selected_cut_21819

theorem selected_cut_21820 : selected 8 ⟨557910, by decide⟩
    (prefixPartial 13 301210) = some ⟨13, 2, 0, 557910, 301210, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_301210_557910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301210 ⟨557910, by decide⟩ :=
  accepted_of_selected 13 301210 ⟨557910, by decide⟩ ⟨13, 2, 0, 557910, 301210, 1165, 16384⟩
    (by decide) selected_cut_21820

theorem selected_cut_21821 : selected 8 ⟨557918, by decide⟩
    (prefixPartial 13 301211) = some ⟨13, 2, 0, 557918, 301211, 797, 16384⟩ := by
  decide +kernel

theorem context_13_301211_557918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301211 ⟨557918, by decide⟩ :=
  accepted_of_selected 13 301211 ⟨557918, by decide⟩ ⟨13, 2, 0, 557918, 301211, 797, 16384⟩
    (by decide) selected_cut_21821

theorem unmarked_context_12_75302_557919 : frontier 9 ⟨557919, by decide⟩
    (prefixCache 12 75302) (prefixPartial 12 75302) = false := by
  decide +kernel

theorem node_context_12_75302_557919 : EJMOriginalGlobalDAGData.nodes 9 ⟨557919, by decide⟩ =
    .split (coordinate 12) (![⟨557872, by decide⟩,⟨557894, by decide⟩,⟨557910, by decide⟩,⟨557918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75302_557919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75302 ⟨557919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75302
    ⟨557919, by decide⟩ (by decide) (![⟨557872, by decide⟩,⟨557894, by decide⟩,⟨557910, by decide⟩,⟨557918, by decide⟩]) unmarked_context_12_75302_557919 node_context_12_75302_557919
  intro a
  fin_cases a
  · exact context_13_301208_557872
  · exact context_13_301209_557894
  · exact context_13_301210_557910
  · exact context_13_301211_557918

theorem selected_cut_21822 : selected 8 ⟨557942, by decide⟩
    (prefixPartial 13 301212) = some ⟨13, 2, 0, 557942, 301212, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_301212_557942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301212 ⟨557942, by decide⟩ :=
  accepted_of_selected 13 301212 ⟨557942, by decide⟩ ⟨13, 2, 0, 557942, 301212, 1313, 16384⟩
    (by decide) selected_cut_21822

theorem selected_cut_21823 : selected 8 ⟨557967, by decide⟩
    (prefixPartial 13 301213) = some ⟨13, 2, 0, 557967, 301213, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_301213_557967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301213 ⟨557967, by decide⟩ :=
  accepted_of_selected 13 301213 ⟨557967, by decide⟩ ⟨13, 2, 0, 557967, 301213, 2117, 16384⟩
    (by decide) selected_cut_21823

theorem selected_cut_21824 : selected 8 ⟨557988, by decide⟩
    (prefixPartial 13 301214) = some ⟨13, 2, 0, 557988, 301214, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_301214_557988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301214 ⟨557988, by decide⟩ :=
  accepted_of_selected 13 301214 ⟨557988, by decide⟩ ⟨13, 2, 0, 557988, 301214, 1745, 16384⟩
    (by decide) selected_cut_21824

theorem selected_cut_21825 : selected 8 ⟨557992, by decide⟩
    (prefixPartial 13 301215) = some ⟨13, 2, 0, 557992, 301215, 889, 16384⟩ := by
  decide +kernel

theorem context_13_301215_557992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301215 ⟨557992, by decide⟩ :=
  accepted_of_selected 13 301215 ⟨557992, by decide⟩ ⟨13, 2, 0, 557992, 301215, 889, 16384⟩
    (by decide) selected_cut_21825

theorem unmarked_context_12_75303_557993 : frontier 9 ⟨557993, by decide⟩
    (prefixCache 12 75303) (prefixPartial 12 75303) = false := by
  decide +kernel

theorem node_context_12_75303_557993 : EJMOriginalGlobalDAGData.nodes 9 ⟨557993, by decide⟩ =
    .split (coordinate 12) (![⟨557942, by decide⟩,⟨557967, by decide⟩,⟨557988, by decide⟩,⟨557992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75303_557993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75303 ⟨557993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75303
    ⟨557993, by decide⟩ (by decide) (![⟨557942, by decide⟩,⟨557967, by decide⟩,⟨557988, by decide⟩,⟨557992, by decide⟩]) unmarked_context_12_75303_557993 node_context_12_75303_557993
  intro a
  fin_cases a
  · exact context_13_301212_557942
  · exact context_13_301213_557967
  · exact context_13_301214_557988
  · exact context_13_301215_557992

theorem unmarked_context_11_18825_557994 : frontier 10 ⟨557994, by decide⟩
    (prefixCache 11 18825) (prefixPartial 11 18825) = false := by
  decide +kernel

theorem node_context_11_18825_557994 : EJMOriginalGlobalDAGData.nodes 10 ⟨557994, by decide⟩ =
    .split (coordinate 11) (![⟨557793, by decide⟩,⟨557856, by decide⟩,⟨557919, by decide⟩,⟨557993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18825_557994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18825 ⟨557994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18825
    ⟨557994, by decide⟩ (by decide) (![⟨557793, by decide⟩,⟨557856, by decide⟩,⟨557919, by decide⟩,⟨557993, by decide⟩]) unmarked_context_11_18825_557994 node_context_11_18825_557994
  intro a
  fin_cases a
  · exact context_12_75300_557793
  · exact context_12_75301_557856
  · exact context_12_75302_557919
  · exact context_12_75303_557993

theorem selected_cut_21826 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 75304) = some ⟨12, 1, 0, 435790, 75304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75304_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75304 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 75304 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 75304, 1, 65536⟩
    (by decide) selected_cut_21826

theorem selected_cut_21827 : selected 8 ⟨558009, by decide⟩
    (prefixPartial 13 301220) = some ⟨13, 2, 0, 558009, 301220, 837, 16384⟩ := by
  decide +kernel

theorem context_13_301220_558009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301220 ⟨558009, by decide⟩ :=
  accepted_of_selected 13 301220 ⟨558009, by decide⟩ ⟨13, 2, 0, 558009, 301220, 837, 16384⟩
    (by decide) selected_cut_21827

theorem selected_cut_21828 : selected 8 ⟨558032, by decide⟩
    (prefixPartial 13 301221) = some ⟨13, 2, 0, 558032, 301221, 2009, 16384⟩ := by
  decide +kernel

theorem context_13_301221_558032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301221 ⟨558032, by decide⟩ :=
  accepted_of_selected 13 301221 ⟨558032, by decide⟩ ⟨13, 2, 0, 558032, 301221, 2009, 16384⟩
    (by decide) selected_cut_21828

theorem selected_cut_21829 : selected 8 ⟨558048, by decide⟩
    (prefixPartial 13 301222) = some ⟨13, 2, 0, 558048, 301222, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_301222_558048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301222 ⟨558048, by decide⟩ :=
  accepted_of_selected 13 301222 ⟨558048, by decide⟩ ⟨13, 2, 0, 558048, 301222, 1401, 16384⟩
    (by decide) selected_cut_21829

theorem selected_cut_21830 : selected 8 ⟨558054, by decide⟩
    (prefixPartial 13 301223) = some ⟨13, 2, 0, 558054, 301223, 857, 16384⟩ := by
  decide +kernel

theorem context_13_301223_558054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301223 ⟨558054, by decide⟩ :=
  accepted_of_selected 13 301223 ⟨558054, by decide⟩ ⟨13, 2, 0, 558054, 301223, 857, 16384⟩
    (by decide) selected_cut_21830

theorem unmarked_context_12_75305_558055 : frontier 9 ⟨558055, by decide⟩
    (prefixCache 12 75305) (prefixPartial 12 75305) = false := by
  decide +kernel

theorem node_context_12_75305_558055 : EJMOriginalGlobalDAGData.nodes 9 ⟨558055, by decide⟩ =
    .split (coordinate 12) (![⟨558009, by decide⟩,⟨558032, by decide⟩,⟨558048, by decide⟩,⟨558054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75305_558055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75305 ⟨558055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75305
    ⟨558055, by decide⟩ (by decide) (![⟨558009, by decide⟩,⟨558032, by decide⟩,⟨558048, by decide⟩,⟨558054, by decide⟩]) unmarked_context_12_75305_558055 node_context_12_75305_558055
  intro a
  fin_cases a
  · exact context_13_301220_558009
  · exact context_13_301221_558032
  · exact context_13_301222_558048
  · exact context_13_301223_558054

theorem selected_cut_21831 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 75306) = some ⟨12, 1, 0, 445248, 75306, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75306_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75306 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 75306 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 75306, 1, 65536⟩
    (by decide) selected_cut_21831

theorem selected_cut_21832 : selected 8 ⟨558069, by decide⟩
    (prefixPartial 13 301228) = some ⟨13, 2, 0, 558069, 301228, 889, 16384⟩ := by
  decide +kernel

theorem context_13_301228_558069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301228 ⟨558069, by decide⟩ :=
  accepted_of_selected 13 301228 ⟨558069, by decide⟩ ⟨13, 2, 0, 558069, 301228, 889, 16384⟩
    (by decide) selected_cut_21832

theorem selected_cut_21833 : selected 8 ⟨558099, by decide⟩
    (prefixPartial 13 301229) = some ⟨13, 2, 0, 558099, 301229, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_301229_558099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301229 ⟨558099, by decide⟩ :=
  accepted_of_selected 13 301229 ⟨558099, by decide⟩ ⟨13, 2, 0, 558099, 301229, 2305, 16384⟩
    (by decide) selected_cut_21833

theorem selected_cut_21834 : selected 8 ⟨558115, by decide⟩
    (prefixPartial 13 301230) = some ⟨13, 2, 0, 558115, 301230, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_301230_558115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301230 ⟨558115, by decide⟩ :=
  accepted_of_selected 13 301230 ⟨558115, by decide⟩ ⟨13, 2, 0, 558115, 301230, 1581, 16384⟩
    (by decide) selected_cut_21834

theorem selected_cut_21835 : selected 8 ⟨558121, by decide⟩
    (prefixPartial 13 301231) = some ⟨13, 2, 0, 558121, 301231, 733, 16384⟩ := by
  decide +kernel

theorem context_13_301231_558121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301231 ⟨558121, by decide⟩ :=
  accepted_of_selected 13 301231 ⟨558121, by decide⟩ ⟨13, 2, 0, 558121, 301231, 733, 16384⟩
    (by decide) selected_cut_21835

theorem unmarked_context_12_75307_558122 : frontier 9 ⟨558122, by decide⟩
    (prefixCache 12 75307) (prefixPartial 12 75307) = false := by
  decide +kernel

theorem node_context_12_75307_558122 : EJMOriginalGlobalDAGData.nodes 9 ⟨558122, by decide⟩ =
    .split (coordinate 12) (![⟨558069, by decide⟩,⟨558099, by decide⟩,⟨558115, by decide⟩,⟨558121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75307_558122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75307 ⟨558122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75307
    ⟨558122, by decide⟩ (by decide) (![⟨558069, by decide⟩,⟨558099, by decide⟩,⟨558115, by decide⟩,⟨558121, by decide⟩]) unmarked_context_12_75307_558122 node_context_12_75307_558122
  intro a
  fin_cases a
  · exact context_13_301228_558069
  · exact context_13_301229_558099
  · exact context_13_301230_558115
  · exact context_13_301231_558121

theorem unmarked_context_11_18826_558123 : frontier 10 ⟨558123, by decide⟩
    (prefixCache 11 18826) (prefixPartial 11 18826) = false := by
  decide +kernel

theorem node_context_11_18826_558123 : EJMOriginalGlobalDAGData.nodes 10 ⟨558123, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨558055, by decide⟩,⟨445248, by decide⟩,⟨558122, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18826_558123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18826 ⟨558123, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18826
    ⟨558123, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨558055, by decide⟩,⟨445248, by decide⟩,⟨558122, by decide⟩]) unmarked_context_11_18826_558123 node_context_11_18826_558123
  intro a
  fin_cases a
  · exact context_12_75304_435790
  · exact context_12_75305_558055
  · exact context_12_75306_445248
  · exact context_12_75307_558122

theorem selected_cut_21836 : selected 8 ⟨558145, by decide⟩
    (prefixPartial 13 301232) = some ⟨13, 2, 0, 558145, 301232, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_301232_558145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301232 ⟨558145, by decide⟩ :=
  accepted_of_selected 13 301232 ⟨558145, by decide⟩ ⟨13, 2, 0, 558145, 301232, 1121, 16384⟩
    (by decide) selected_cut_21836

theorem selected_cut_21837 : selected 8 ⟨558201, by decide⟩
    (prefixPartial 13 301233) = some ⟨13, 2, 0, 558201, 301233, 3405, 16384⟩ := by
  decide +kernel

theorem context_13_301233_558201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301233 ⟨558201, by decide⟩ :=
  accepted_of_selected 13 301233 ⟨558201, by decide⟩ ⟨13, 2, 0, 558201, 301233, 3405, 16384⟩
    (by decide) selected_cut_21837

theorem selected_cut_21838 : selected 8 ⟨558242, by decide⟩
    (prefixPartial 13 301234) = some ⟨13, 2, 0, 558242, 301234, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_301234_558242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301234 ⟨558242, by decide⟩ :=
  accepted_of_selected 13 301234 ⟨558242, by decide⟩ ⟨13, 2, 0, 558242, 301234, 2141, 16384⟩
    (by decide) selected_cut_21838

theorem selected_cut_21839 : selected 8 ⟨558252, by decide⟩
    (prefixPartial 13 301235) = some ⟨13, 2, 0, 558252, 301235, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_301235_558252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301235 ⟨558252, by decide⟩ :=
  accepted_of_selected 13 301235 ⟨558252, by decide⟩ ⟨13, 2, 0, 558252, 301235, 1005, 16384⟩
    (by decide) selected_cut_21839

theorem unmarked_context_12_75308_558253 : frontier 9 ⟨558253, by decide⟩
    (prefixCache 12 75308) (prefixPartial 12 75308) = false := by
  decide +kernel

theorem node_context_12_75308_558253 : EJMOriginalGlobalDAGData.nodes 9 ⟨558253, by decide⟩ =
    .split (coordinate 12) (![⟨558145, by decide⟩,⟨558201, by decide⟩,⟨558242, by decide⟩,⟨558252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75308_558253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75308 ⟨558253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75308
    ⟨558253, by decide⟩ (by decide) (![⟨558145, by decide⟩,⟨558201, by decide⟩,⟨558242, by decide⟩,⟨558252, by decide⟩]) unmarked_context_12_75308_558253 node_context_12_75308_558253
  intro a
  fin_cases a
  · exact context_13_301232_558145
  · exact context_13_301233_558201
  · exact context_13_301234_558242
  · exact context_13_301235_558252

theorem selected_cut_21840 : selected 8 ⟨558264, by decide⟩
    (prefixPartial 13 301236) = some ⟨13, 2, 0, 558264, 301236, 725, 16384⟩ := by
  decide +kernel

theorem context_13_301236_558264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301236 ⟨558264, by decide⟩ :=
  accepted_of_selected 13 301236 ⟨558264, by decide⟩ ⟨13, 2, 0, 558264, 301236, 725, 16384⟩
    (by decide) selected_cut_21840

theorem selected_cut_21841 : selected 8 ⟨558296, by decide⟩
    (prefixPartial 13 301237) = some ⟨13, 2, 0, 558296, 301237, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_301237_558296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301237 ⟨558296, by decide⟩ :=
  accepted_of_selected 13 301237 ⟨558296, by decide⟩ ⟨13, 2, 0, 558296, 301237, 2501, 16384⟩
    (by decide) selected_cut_21841

theorem selected_cut_21842 : selected 8 ⟨558313, by decide⟩
    (prefixPartial 13 301238) = some ⟨13, 2, 0, 558313, 301238, 1397, 16384⟩ := by
  decide +kernel

theorem context_13_301238_558313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301238 ⟨558313, by decide⟩ :=
  accepted_of_selected 13 301238 ⟨558313, by decide⟩ ⟨13, 2, 0, 558313, 301238, 1397, 16384⟩
    (by decide) selected_cut_21842

theorem selected_cut_21843 : selected 8 ⟨558317, by decide⟩
    (prefixPartial 13 301239) = some ⟨13, 2, 0, 558317, 301239, 773, 16384⟩ := by
  decide +kernel

theorem context_13_301239_558317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301239 ⟨558317, by decide⟩ :=
  accepted_of_selected 13 301239 ⟨558317, by decide⟩ ⟨13, 2, 0, 558317, 301239, 773, 16384⟩
    (by decide) selected_cut_21843

theorem unmarked_context_12_75309_558318 : frontier 9 ⟨558318, by decide⟩
    (prefixCache 12 75309) (prefixPartial 12 75309) = false := by
  decide +kernel

theorem node_context_12_75309_558318 : EJMOriginalGlobalDAGData.nodes 9 ⟨558318, by decide⟩ =
    .split (coordinate 12) (![⟨558264, by decide⟩,⟨558296, by decide⟩,⟨558313, by decide⟩,⟨558317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75309_558318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75309 ⟨558318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75309
    ⟨558318, by decide⟩ (by decide) (![⟨558264, by decide⟩,⟨558296, by decide⟩,⟨558313, by decide⟩,⟨558317, by decide⟩]) unmarked_context_12_75309_558318 node_context_12_75309_558318
  intro a
  fin_cases a
  · exact context_13_301236_558264
  · exact context_13_301237_558296
  · exact context_13_301238_558313
  · exact context_13_301239_558317

theorem selected_cut_21844 : selected 8 ⟨558329, by decide⟩
    (prefixPartial 13 301240) = some ⟨13, 2, 0, 558329, 301240, 609, 16384⟩ := by
  decide +kernel

theorem context_13_301240_558329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301240 ⟨558329, by decide⟩ :=
  accepted_of_selected 13 301240 ⟨558329, by decide⟩ ⟨13, 2, 0, 558329, 301240, 609, 16384⟩
    (by decide) selected_cut_21844

theorem selected_cut_21845 : selected 8 ⟨558353, by decide⟩
    (prefixPartial 13 301241) = some ⟨13, 2, 0, 558353, 301241, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_301241_558353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301241 ⟨558353, by decide⟩ :=
  accepted_of_selected 13 301241 ⟨558353, by decide⟩ ⟨13, 2, 0, 558353, 301241, 2161, 16384⟩
    (by decide) selected_cut_21845

theorem selected_cut_21846 : selected 8 ⟨558366, by decide⟩
    (prefixPartial 13 301242) = some ⟨13, 2, 0, 558366, 301242, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_301242_558366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301242 ⟨558366, by decide⟩ :=
  accepted_of_selected 13 301242 ⟨558366, by decide⟩ ⟨13, 2, 0, 558366, 301242, 1213, 16384⟩
    (by decide) selected_cut_21846

theorem selected_cut_21847 : selected 8 ⟨558370, by decide⟩
    (prefixPartial 13 301243) = some ⟨13, 2, 0, 558370, 301243, 729, 16384⟩ := by
  decide +kernel

theorem context_13_301243_558370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301243 ⟨558370, by decide⟩ :=
  accepted_of_selected 13 301243 ⟨558370, by decide⟩ ⟨13, 2, 0, 558370, 301243, 729, 16384⟩
    (by decide) selected_cut_21847

theorem unmarked_context_12_75310_558371 : frontier 9 ⟨558371, by decide⟩
    (prefixCache 12 75310) (prefixPartial 12 75310) = false := by
  decide +kernel

theorem node_context_12_75310_558371 : EJMOriginalGlobalDAGData.nodes 9 ⟨558371, by decide⟩ =
    .split (coordinate 12) (![⟨558329, by decide⟩,⟨558353, by decide⟩,⟨558366, by decide⟩,⟨558370, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75310_558371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75310 ⟨558371, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75310
    ⟨558371, by decide⟩ (by decide) (![⟨558329, by decide⟩,⟨558353, by decide⟩,⟨558366, by decide⟩,⟨558370, by decide⟩]) unmarked_context_12_75310_558371 node_context_12_75310_558371
  intro a
  fin_cases a
  · exact context_13_301240_558329
  · exact context_13_301241_558353
  · exact context_13_301242_558366
  · exact context_13_301243_558370

theorem selected_cut_21848 : selected 8 ⟨558384, by decide⟩
    (prefixPartial 13 301244) = some ⟨13, 2, 0, 558384, 301244, 845, 16384⟩ := by
  decide +kernel

theorem context_13_301244_558384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301244 ⟨558384, by decide⟩ :=
  accepted_of_selected 13 301244 ⟨558384, by decide⟩ ⟨13, 2, 0, 558384, 301244, 845, 16384⟩
    (by decide) selected_cut_21848

theorem selected_cut_21849 : selected 8 ⟨558417, by decide⟩
    (prefixPartial 13 301245) = some ⟨13, 2, 0, 558417, 301245, 2757, 16384⟩ := by
  decide +kernel

theorem context_13_301245_558417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301245 ⟨558417, by decide⟩ :=
  accepted_of_selected 13 301245 ⟨558417, by decide⟩ ⟨13, 2, 0, 558417, 301245, 2757, 16384⟩
    (by decide) selected_cut_21849

theorem selected_cut_21850 : selected 8 ⟨558432, by decide⟩
    (prefixPartial 13 301246) = some ⟨13, 2, 0, 558432, 301246, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_301246_558432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301246 ⟨558432, by decide⟩ :=
  accepted_of_selected 13 301246 ⟨558432, by decide⟩ ⟨13, 2, 0, 558432, 301246, 1725, 16384⟩
    (by decide) selected_cut_21850

theorem selected_cut_21851 : selected 8 ⟨558438, by decide⟩
    (prefixPartial 13 301247) = some ⟨13, 2, 0, 558438, 301247, 789, 16384⟩ := by
  decide +kernel

theorem context_13_301247_558438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301247 ⟨558438, by decide⟩ :=
  accepted_of_selected 13 301247 ⟨558438, by decide⟩ ⟨13, 2, 0, 558438, 301247, 789, 16384⟩
    (by decide) selected_cut_21851

theorem unmarked_context_12_75311_558439 : frontier 9 ⟨558439, by decide⟩
    (prefixCache 12 75311) (prefixPartial 12 75311) = false := by
  decide +kernel

theorem node_context_12_75311_558439 : EJMOriginalGlobalDAGData.nodes 9 ⟨558439, by decide⟩ =
    .split (coordinate 12) (![⟨558384, by decide⟩,⟨558417, by decide⟩,⟨558432, by decide⟩,⟨558438, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75311_558439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75311 ⟨558439, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75311
    ⟨558439, by decide⟩ (by decide) (![⟨558384, by decide⟩,⟨558417, by decide⟩,⟨558432, by decide⟩,⟨558438, by decide⟩]) unmarked_context_12_75311_558439 node_context_12_75311_558439
  intro a
  fin_cases a
  · exact context_13_301244_558384
  · exact context_13_301245_558417
  · exact context_13_301246_558432
  · exact context_13_301247_558438

theorem unmarked_context_11_18827_558440 : frontier 10 ⟨558440, by decide⟩
    (prefixCache 11 18827) (prefixPartial 11 18827) = false := by
  decide +kernel

theorem node_context_11_18827_558440 : EJMOriginalGlobalDAGData.nodes 10 ⟨558440, by decide⟩ =
    .split (coordinate 11) (![⟨558253, by decide⟩,⟨558318, by decide⟩,⟨558371, by decide⟩,⟨558439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18827_558440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18827 ⟨558440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18827
    ⟨558440, by decide⟩ (by decide) (![⟨558253, by decide⟩,⟨558318, by decide⟩,⟨558371, by decide⟩,⟨558439, by decide⟩]) unmarked_context_11_18827_558440 node_context_11_18827_558440
  intro a
  fin_cases a
  · exact context_12_75308_558253
  · exact context_12_75309_558318
  · exact context_12_75310_558371
  · exact context_12_75311_558439

theorem unmarked_context_10_4706_558441 : frontier 11 ⟨558441, by decide⟩
    (prefixCache 10 4706) (prefixPartial 10 4706) = false := by
  decide +kernel

theorem node_context_10_4706_558441 : EJMOriginalGlobalDAGData.nodes 11 ⟨558441, by decide⟩ =
    .split (coordinate 10) (![⟨557693, by decide⟩,⟨557994, by decide⟩,⟨558123, by decide⟩,⟨558440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4706_558441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4706 ⟨558441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4706
    ⟨558441, by decide⟩ (by decide) (![⟨557693, by decide⟩,⟨557994, by decide⟩,⟨558123, by decide⟩,⟨558440, by decide⟩]) unmarked_context_10_4706_558441 node_context_10_4706_558441
  intro a
  fin_cases a
  · exact context_11_18824_557693
  · exact context_11_18825_557994
  · exact context_11_18826_558123
  · exact context_11_18827_558440

theorem selected_cut_21852 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 75312) = some ⟨12, 1, 0, 445562, 75312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75312_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75312 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 75312 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 75312, 1, 65536⟩
    (by decide) selected_cut_21852

theorem selected_cut_21853 : selected 8 ⟨558451, by decide⟩
    (prefixPartial 13 301252) = some ⟨13, 2, 0, 558451, 301252, 681, 16384⟩ := by
  decide +kernel

theorem context_13_301252_558451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301252 ⟨558451, by decide⟩ :=
  accepted_of_selected 13 301252 ⟨558451, by decide⟩ ⟨13, 2, 0, 558451, 301252, 681, 16384⟩
    (by decide) selected_cut_21853

theorem selected_cut_21854 : selected 8 ⟨558482, by decide⟩
    (prefixPartial 13 301253) = some ⟨13, 2, 0, 558482, 301253, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_301253_558482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301253 ⟨558482, by decide⟩ :=
  accepted_of_selected 13 301253 ⟨558482, by decide⟩ ⟨13, 2, 0, 558482, 301253, 2273, 16384⟩
    (by decide) selected_cut_21854

theorem selected_cut_21855 : selected 8 ⟨558497, by decide⟩
    (prefixPartial 13 301254) = some ⟨13, 2, 0, 558497, 301254, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_301254_558497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301254 ⟨558497, by decide⟩ :=
  accepted_of_selected 13 301254 ⟨558497, by decide⟩ ⟨13, 2, 0, 558497, 301254, 1225, 16384⟩
    (by decide) selected_cut_21855

theorem selected_cut_21856 : selected 8 ⟨558505, by decide⟩
    (prefixPartial 13 301255) = some ⟨13, 2, 0, 558505, 301255, 797, 16384⟩ := by
  decide +kernel

theorem context_13_301255_558505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301255 ⟨558505, by decide⟩ :=
  accepted_of_selected 13 301255 ⟨558505, by decide⟩ ⟨13, 2, 0, 558505, 301255, 797, 16384⟩
    (by decide) selected_cut_21856

theorem unmarked_context_12_75313_558506 : frontier 9 ⟨558506, by decide⟩
    (prefixCache 12 75313) (prefixPartial 12 75313) = false := by
  decide +kernel

theorem node_context_12_75313_558506 : EJMOriginalGlobalDAGData.nodes 9 ⟨558506, by decide⟩ =
    .split (coordinate 12) (![⟨558451, by decide⟩,⟨558482, by decide⟩,⟨558497, by decide⟩,⟨558505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75313_558506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75313 ⟨558506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75313
    ⟨558506, by decide⟩ (by decide) (![⟨558451, by decide⟩,⟨558482, by decide⟩,⟨558497, by decide⟩,⟨558505, by decide⟩]) unmarked_context_12_75313_558506 node_context_12_75313_558506
  intro a
  fin_cases a
  · exact context_13_301252_558451
  · exact context_13_301253_558482
  · exact context_13_301254_558497
  · exact context_13_301255_558505

theorem selected_cut_21857 : selected 8 ⟨558515, by decide⟩
    (prefixPartial 13 301256) = some ⟨13, 2, 0, 558515, 301256, 649, 16384⟩ := by
  decide +kernel

theorem context_13_301256_558515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301256 ⟨558515, by decide⟩ :=
  accepted_of_selected 13 301256 ⟨558515, by decide⟩ ⟨13, 2, 0, 558515, 301256, 649, 16384⟩
    (by decide) selected_cut_21857

theorem selected_cut_21858 : selected 8 ⟨558536, by decide⟩
    (prefixPartial 13 301257) = some ⟨13, 2, 0, 558536, 301257, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_301257_558536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301257 ⟨558536, by decide⟩ :=
  accepted_of_selected 13 301257 ⟨558536, by decide⟩ ⟨13, 2, 0, 558536, 301257, 1981, 16384⟩
    (by decide) selected_cut_21858

theorem selected_cut_21859 : selected 8 ⟨558550, by decide⟩
    (prefixPartial 13 301258) = some ⟨13, 2, 0, 558550, 301258, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_301258_558550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301258 ⟨558550, by decide⟩ :=
  accepted_of_selected 13 301258 ⟨558550, by decide⟩ ⟨13, 2, 0, 558550, 301258, 1029, 16384⟩
    (by decide) selected_cut_21859

theorem selected_cut_21860 : selected 8 ⟨558554, by decide⟩
    (prefixPartial 13 301259) = some ⟨13, 2, 0, 558554, 301259, 793, 16384⟩ := by
  decide +kernel

theorem context_13_301259_558554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301259 ⟨558554, by decide⟩ :=
  accepted_of_selected 13 301259 ⟨558554, by decide⟩ ⟨13, 2, 0, 558554, 301259, 793, 16384⟩
    (by decide) selected_cut_21860

theorem unmarked_context_12_75314_558555 : frontier 9 ⟨558555, by decide⟩
    (prefixCache 12 75314) (prefixPartial 12 75314) = false := by
  decide +kernel

theorem node_context_12_75314_558555 : EJMOriginalGlobalDAGData.nodes 9 ⟨558555, by decide⟩ =
    .split (coordinate 12) (![⟨558515, by decide⟩,⟨558536, by decide⟩,⟨558550, by decide⟩,⟨558554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75314_558555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75314 ⟨558555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75314
    ⟨558555, by decide⟩ (by decide) (![⟨558515, by decide⟩,⟨558536, by decide⟩,⟨558550, by decide⟩,⟨558554, by decide⟩]) unmarked_context_12_75314_558555 node_context_12_75314_558555
  intro a
  fin_cases a
  · exact context_13_301256_558515
  · exact context_13_301257_558536
  · exact context_13_301258_558550
  · exact context_13_301259_558554

theorem selected_cut_21861 : selected 8 ⟨558567, by decide⟩
    (prefixPartial 13 301260) = some ⟨13, 2, 0, 558567, 301260, 769, 16384⟩ := by
  decide +kernel

theorem context_13_301260_558567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301260 ⟨558567, by decide⟩ :=
  accepted_of_selected 13 301260 ⟨558567, by decide⟩ ⟨13, 2, 0, 558567, 301260, 769, 16384⟩
    (by decide) selected_cut_21861

theorem selected_cut_21862 : selected 8 ⟨558600, by decide⟩
    (prefixPartial 13 301261) = some ⟨13, 2, 0, 558600, 301261, 2709, 16384⟩ := by
  decide +kernel

theorem context_13_301261_558600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301261 ⟨558600, by decide⟩ :=
  accepted_of_selected 13 301261 ⟨558600, by decide⟩ ⟨13, 2, 0, 558600, 301261, 2709, 16384⟩
    (by decide) selected_cut_21862

theorem selected_cut_21863 : selected 8 ⟨558616, by decide⟩
    (prefixPartial 13 301262) = some ⟨13, 2, 0, 558616, 301262, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_301262_558616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301262 ⟨558616, by decide⟩ :=
  accepted_of_selected 13 301262 ⟨558616, by decide⟩ ⟨13, 2, 0, 558616, 301262, 1429, 16384⟩
    (by decide) selected_cut_21863

theorem selected_cut_21864 : selected 8 ⟨558625, by decide⟩
    (prefixPartial 13 301263) = some ⟨13, 2, 0, 558625, 301263, 821, 16384⟩ := by
  decide +kernel

theorem context_13_301263_558625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301263 ⟨558625, by decide⟩ :=
  accepted_of_selected 13 301263 ⟨558625, by decide⟩ ⟨13, 2, 0, 558625, 301263, 821, 16384⟩
    (by decide) selected_cut_21864

theorem unmarked_context_12_75315_558626 : frontier 9 ⟨558626, by decide⟩
    (prefixCache 12 75315) (prefixPartial 12 75315) = false := by
  decide +kernel

theorem node_context_12_75315_558626 : EJMOriginalGlobalDAGData.nodes 9 ⟨558626, by decide⟩ =
    .split (coordinate 12) (![⟨558567, by decide⟩,⟨558600, by decide⟩,⟨558616, by decide⟩,⟨558625, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75315_558626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75315 ⟨558626, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75315
    ⟨558626, by decide⟩ (by decide) (![⟨558567, by decide⟩,⟨558600, by decide⟩,⟨558616, by decide⟩,⟨558625, by decide⟩]) unmarked_context_12_75315_558626 node_context_12_75315_558626
  intro a
  fin_cases a
  · exact context_13_301260_558567
  · exact context_13_301261_558600
  · exact context_13_301262_558616
  · exact context_13_301263_558625

theorem unmarked_context_11_18828_558627 : frontier 10 ⟨558627, by decide⟩
    (prefixCache 11 18828) (prefixPartial 11 18828) = false := by
  decide +kernel

theorem node_context_11_18828_558627 : EJMOriginalGlobalDAGData.nodes 10 ⟨558627, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨558506, by decide⟩,⟨558555, by decide⟩,⟨558626, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18828_558627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18828 ⟨558627, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18828
    ⟨558627, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨558506, by decide⟩,⟨558555, by decide⟩,⟨558626, by decide⟩]) unmarked_context_11_18828_558627 node_context_11_18828_558627
  intro a
  fin_cases a
  · exact context_12_75312_445562
  · exact context_12_75313_558506
  · exact context_12_75314_558555
  · exact context_12_75315_558626

theorem selected_cut_21865 : selected 8 ⟨558641, by decide⟩
    (prefixPartial 13 301264) = some ⟨13, 2, 0, 558641, 301264, 801, 16384⟩ := by
  decide +kernel

theorem context_13_301264_558641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301264 ⟨558641, by decide⟩ :=
  accepted_of_selected 13 301264 ⟨558641, by decide⟩ ⟨13, 2, 0, 558641, 301264, 801, 16384⟩
    (by decide) selected_cut_21865

theorem selected_cut_21866 : selected 8 ⟨558688, by decide⟩
    (prefixPartial 13 301265) = some ⟨13, 2, 0, 558688, 301265, 3209, 16384⟩ := by
  decide +kernel

theorem context_13_301265_558688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301265 ⟨558688, by decide⟩ :=
  accepted_of_selected 13 301265 ⟨558688, by decide⟩ ⟨13, 2, 0, 558688, 301265, 3209, 16384⟩
    (by decide) selected_cut_21866

theorem selected_cut_21867 : selected 8 ⟨558714, by decide⟩
    (prefixPartial 13 301266) = some ⟨13, 2, 0, 558714, 301266, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_301266_558714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301266 ⟨558714, by decide⟩ :=
  accepted_of_selected 13 301266 ⟨558714, by decide⟩ ⟨13, 2, 0, 558714, 301266, 1833, 16384⟩
    (by decide) selected_cut_21867

theorem selected_cut_21868 : selected 8 ⟨558725, by decide⟩
    (prefixPartial 13 301267) = some ⟨13, 2, 0, 558725, 301267, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_301267_558725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301267 ⟨558725, by decide⟩ :=
  accepted_of_selected 13 301267 ⟨558725, by decide⟩ ⟨13, 2, 0, 558725, 301267, 1077, 16384⟩
    (by decide) selected_cut_21868

theorem unmarked_context_12_75316_558726 : frontier 9 ⟨558726, by decide⟩
    (prefixCache 12 75316) (prefixPartial 12 75316) = false := by
  decide +kernel

theorem node_context_12_75316_558726 : EJMOriginalGlobalDAGData.nodes 9 ⟨558726, by decide⟩ =
    .split (coordinate 12) (![⟨558641, by decide⟩,⟨558688, by decide⟩,⟨558714, by decide⟩,⟨558725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75316_558726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75316 ⟨558726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75316
    ⟨558726, by decide⟩ (by decide) (![⟨558641, by decide⟩,⟨558688, by decide⟩,⟨558714, by decide⟩,⟨558725, by decide⟩]) unmarked_context_12_75316_558726 node_context_12_75316_558726
  intro a
  fin_cases a
  · exact context_13_301264_558641
  · exact context_13_301265_558688
  · exact context_13_301266_558714
  · exact context_13_301267_558725

theorem selected_cut_21869 : selected 8 ⟨558735, by decide⟩
    (prefixPartial 13 301268) = some ⟨13, 2, 0, 558735, 301268, 485, 16384⟩ := by
  decide +kernel

theorem context_13_301268_558735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301268 ⟨558735, by decide⟩ :=
  accepted_of_selected 13 301268 ⟨558735, by decide⟩ ⟨13, 2, 0, 558735, 301268, 485, 16384⟩
    (by decide) selected_cut_21869

theorem selected_cut_21870 : selected 8 ⟨558758, by decide⟩
    (prefixPartial 13 301269) = some ⟨13, 2, 0, 558758, 301269, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_301269_558758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301269 ⟨558758, by decide⟩ :=
  accepted_of_selected 13 301269 ⟨558758, by decide⟩ ⟨13, 2, 0, 558758, 301269, 1977, 16384⟩
    (by decide) selected_cut_21870

theorem selected_cut_21871 : selected 8 ⟨558773, by decide⟩
    (prefixPartial 13 301270) = some ⟨13, 2, 0, 558773, 301270, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_301270_558773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301270 ⟨558773, by decide⟩ :=
  accepted_of_selected 13 301270 ⟨558773, by decide⟩ ⟨13, 2, 0, 558773, 301270, 1173, 16384⟩
    (by decide) selected_cut_21871

theorem selected_cut_21872 : selected 8 ⟨558781, by decide⟩
    (prefixPartial 13 301271) = some ⟨13, 2, 0, 558781, 301271, 881, 16384⟩ := by
  decide +kernel

theorem context_13_301271_558781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301271 ⟨558781, by decide⟩ :=
  accepted_of_selected 13 301271 ⟨558781, by decide⟩ ⟨13, 2, 0, 558781, 301271, 881, 16384⟩
    (by decide) selected_cut_21872

theorem unmarked_context_12_75317_558782 : frontier 9 ⟨558782, by decide⟩
    (prefixCache 12 75317) (prefixPartial 12 75317) = false := by
  decide +kernel

theorem node_context_12_75317_558782 : EJMOriginalGlobalDAGData.nodes 9 ⟨558782, by decide⟩ =
    .split (coordinate 12) (![⟨558735, by decide⟩,⟨558758, by decide⟩,⟨558773, by decide⟩,⟨558781, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75317_558782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75317 ⟨558782, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75317
    ⟨558782, by decide⟩ (by decide) (![⟨558735, by decide⟩,⟨558758, by decide⟩,⟨558773, by decide⟩,⟨558781, by decide⟩]) unmarked_context_12_75317_558782 node_context_12_75317_558782
  intro a
  fin_cases a
  · exact context_13_301268_558735
  · exact context_13_301269_558758
  · exact context_13_301270_558773
  · exact context_13_301271_558781

theorem selected_cut_21873 : selected 8 ⟨558791, by decide⟩
    (prefixPartial 13 301272) = some ⟨13, 2, 0, 558791, 301272, 465, 16384⟩ := by
  decide +kernel

theorem context_13_301272_558791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301272 ⟨558791, by decide⟩ :=
  accepted_of_selected 13 301272 ⟨558791, by decide⟩ ⟨13, 2, 0, 558791, 301272, 465, 16384⟩
    (by decide) selected_cut_21873

theorem selected_cut_21874 : selected 8 ⟨558814, by decide⟩
    (prefixPartial 13 301273) = some ⟨13, 2, 0, 558814, 301273, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_301273_558814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301273 ⟨558814, by decide⟩ :=
  accepted_of_selected 13 301273 ⟨558814, by decide⟩ ⟨13, 2, 0, 558814, 301273, 1941, 16384⟩
    (by decide) selected_cut_21874

theorem selected_cut_21875 : selected 8 ⟨558828, by decide⟩
    (prefixPartial 13 301274) = some ⟨13, 2, 0, 558828, 301274, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_301274_558828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301274 ⟨558828, by decide⟩ :=
  accepted_of_selected 13 301274 ⟨558828, by decide⟩ ⟨13, 2, 0, 558828, 301274, 1137, 16384⟩
    (by decide) selected_cut_21875

theorem selected_cut_21876 : selected 8 ⟨558834, by decide⟩
    (prefixPartial 13 301275) = some ⟨13, 2, 0, 558834, 301275, 881, 16384⟩ := by
  decide +kernel

theorem context_13_301275_558834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301275 ⟨558834, by decide⟩ :=
  accepted_of_selected 13 301275 ⟨558834, by decide⟩ ⟨13, 2, 0, 558834, 301275, 881, 16384⟩
    (by decide) selected_cut_21876

theorem unmarked_context_12_75318_558835 : frontier 9 ⟨558835, by decide⟩
    (prefixCache 12 75318) (prefixPartial 12 75318) = false := by
  decide +kernel

theorem node_context_12_75318_558835 : EJMOriginalGlobalDAGData.nodes 9 ⟨558835, by decide⟩ =
    .split (coordinate 12) (![⟨558791, by decide⟩,⟨558814, by decide⟩,⟨558828, by decide⟩,⟨558834, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75318_558835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75318 ⟨558835, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75318
    ⟨558835, by decide⟩ (by decide) (![⟨558791, by decide⟩,⟨558814, by decide⟩,⟨558828, by decide⟩,⟨558834, by decide⟩]) unmarked_context_12_75318_558835 node_context_12_75318_558835
  intro a
  fin_cases a
  · exact context_13_301272_558791
  · exact context_13_301273_558814
  · exact context_13_301274_558828
  · exact context_13_301275_558834

theorem selected_cut_21877 : selected 8 ⟨558847, by decide⟩
    (prefixPartial 13 301276) = some ⟨13, 2, 0, 558847, 301276, 589, 16384⟩ := by
  decide +kernel

theorem context_13_301276_558847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301276 ⟨558847, by decide⟩ :=
  accepted_of_selected 13 301276 ⟨558847, by decide⟩ ⟨13, 2, 0, 558847, 301276, 589, 16384⟩
    (by decide) selected_cut_21877

theorem selected_cut_21878 : selected 8 ⟨558875, by decide⟩
    (prefixPartial 13 301277) = some ⟨13, 2, 0, 558875, 301277, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_301277_558875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301277 ⟨558875, by decide⟩ :=
  accepted_of_selected 13 301277 ⟨558875, by decide⟩ ⟨13, 2, 0, 558875, 301277, 2413, 16384⟩
    (by decide) selected_cut_21878

theorem selected_cut_21879 : selected 8 ⟨558896, by decide⟩
    (prefixPartial 13 301278) = some ⟨13, 2, 0, 558896, 301278, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_301278_558896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301278 ⟨558896, by decide⟩ :=
  accepted_of_selected 13 301278 ⟨558896, by decide⟩ ⟨13, 2, 0, 558896, 301278, 1633, 16384⟩
    (by decide) selected_cut_21879

theorem selected_cut_21880 : selected 8 ⟨558907, by decide⟩
    (prefixPartial 13 301279) = some ⟨13, 2, 0, 558907, 301279, 921, 16384⟩ := by
  decide +kernel

theorem context_13_301279_558907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301279 ⟨558907, by decide⟩ :=
  accepted_of_selected 13 301279 ⟨558907, by decide⟩ ⟨13, 2, 0, 558907, 301279, 921, 16384⟩
    (by decide) selected_cut_21880

theorem unmarked_context_12_75319_558908 : frontier 9 ⟨558908, by decide⟩
    (prefixCache 12 75319) (prefixPartial 12 75319) = false := by
  decide +kernel

theorem node_context_12_75319_558908 : EJMOriginalGlobalDAGData.nodes 9 ⟨558908, by decide⟩ =
    .split (coordinate 12) (![⟨558847, by decide⟩,⟨558875, by decide⟩,⟨558896, by decide⟩,⟨558907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75319_558908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75319 ⟨558908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75319
    ⟨558908, by decide⟩ (by decide) (![⟨558847, by decide⟩,⟨558875, by decide⟩,⟨558896, by decide⟩,⟨558907, by decide⟩]) unmarked_context_12_75319_558908 node_context_12_75319_558908
  intro a
  fin_cases a
  · exact context_13_301276_558847
  · exact context_13_301277_558875
  · exact context_13_301278_558896
  · exact context_13_301279_558907

theorem unmarked_context_11_18829_558909 : frontier 10 ⟨558909, by decide⟩
    (prefixCache 11 18829) (prefixPartial 11 18829) = false := by
  decide +kernel

theorem node_context_11_18829_558909 : EJMOriginalGlobalDAGData.nodes 10 ⟨558909, by decide⟩ =
    .split (coordinate 11) (![⟨558726, by decide⟩,⟨558782, by decide⟩,⟨558835, by decide⟩,⟨558908, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18829_558909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18829 ⟨558909, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18829
    ⟨558909, by decide⟩ (by decide) (![⟨558726, by decide⟩,⟨558782, by decide⟩,⟨558835, by decide⟩,⟨558908, by decide⟩]) unmarked_context_11_18829_558909 node_context_11_18829_558909
  intro a
  fin_cases a
  · exact context_12_75316_558726
  · exact context_12_75317_558782
  · exact context_12_75318_558835
  · exact context_12_75319_558908

theorem selected_cut_21881 : selected 8 ⟨558916, by decide⟩
    (prefixPartial 13 301280) = some ⟨13, 2, 0, 558916, 301280, 413, 16384⟩ := by
  decide +kernel

theorem context_13_301280_558916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301280 ⟨558916, by decide⟩ :=
  accepted_of_selected 13 301280 ⟨558916, by decide⟩ ⟨13, 2, 0, 558916, 301280, 413, 16384⟩
    (by decide) selected_cut_21881

theorem selected_cut_21882 : selected 8 ⟨558959, by decide⟩
    (prefixPartial 13 301281) = some ⟨13, 2, 0, 558959, 301281, 3329, 16384⟩ := by
  decide +kernel

theorem context_13_301281_558959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301281 ⟨558959, by decide⟩ :=
  accepted_of_selected 13 301281 ⟨558959, by decide⟩ ⟨13, 2, 0, 558959, 301281, 3329, 16384⟩
    (by decide) selected_cut_21882

theorem selected_cut_21883 : selected 8 ⟨558978, by decide⟩
    (prefixPartial 13 301282) = some ⟨13, 2, 0, 558978, 301282, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_301282_558978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301282 ⟨558978, by decide⟩ :=
  accepted_of_selected 13 301282 ⟨558978, by decide⟩ ⟨13, 2, 0, 558978, 301282, 1897, 16384⟩
    (by decide) selected_cut_21883

theorem selected_cut_21884 : selected 8 ⟨558988, by decide⟩
    (prefixPartial 13 301283) = some ⟨13, 2, 0, 558988, 301283, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_301283_558988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301283 ⟨558988, by decide⟩ :=
  accepted_of_selected 13 301283 ⟨558988, by decide⟩ ⟨13, 2, 0, 558988, 301283, 1041, 16384⟩
    (by decide) selected_cut_21884

theorem unmarked_context_12_75320_558989 : frontier 9 ⟨558989, by decide⟩
    (prefixCache 12 75320) (prefixPartial 12 75320) = false := by
  decide +kernel

theorem node_context_12_75320_558989 : EJMOriginalGlobalDAGData.nodes 9 ⟨558989, by decide⟩ =
    .split (coordinate 12) (![⟨558916, by decide⟩,⟨558959, by decide⟩,⟨558978, by decide⟩,⟨558988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75320_558989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75320 ⟨558989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75320
    ⟨558989, by decide⟩ (by decide) (![⟨558916, by decide⟩,⟨558959, by decide⟩,⟨558978, by decide⟩,⟨558988, by decide⟩]) unmarked_context_12_75320_558989 node_context_12_75320_558989
  intro a
  fin_cases a
  · exact context_13_301280_558916
  · exact context_13_301281_558959
  · exact context_13_301282_558978
  · exact context_13_301283_558988

theorem selected_cut_21885 : selected 8 ⟨558995, by decide⟩
    (prefixPartial 13 301284) = some ⟨13, 2, 0, 558995, 301284, 289, 16384⟩ := by
  decide +kernel

theorem context_13_301284_558995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301284 ⟨558995, by decide⟩ :=
  accepted_of_selected 13 301284 ⟨558995, by decide⟩ ⟨13, 2, 0, 558995, 301284, 289, 16384⟩
    (by decide) selected_cut_21885

theorem selected_cut_21886 : selected 8 ⟨559020, by decide⟩
    (prefixPartial 13 301285) = some ⟨13, 2, 0, 559020, 301285, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_301285_559020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301285 ⟨559020, by decide⟩ :=
  accepted_of_selected 13 301285 ⟨559020, by decide⟩ ⟨13, 2, 0, 559020, 301285, 2201, 16384⟩
    (by decide) selected_cut_21886

theorem selected_cut_21887 : selected 8 ⟨559035, by decide⟩
    (prefixPartial 13 301286) = some ⟨13, 2, 0, 559035, 301286, 1353, 16384⟩ := by
  decide +kernel

theorem context_13_301286_559035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301286 ⟨559035, by decide⟩ :=
  accepted_of_selected 13 301286 ⟨559035, by decide⟩ ⟨13, 2, 0, 559035, 301286, 1353, 16384⟩
    (by decide) selected_cut_21887

theorem selected_cut_21888 : selected 8 ⟨559043, by decide⟩
    (prefixPartial 13 301287) = some ⟨13, 2, 0, 559043, 301287, 933, 16384⟩ := by
  decide +kernel

theorem context_13_301287_559043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301287 ⟨559043, by decide⟩ :=
  accepted_of_selected 13 301287 ⟨559043, by decide⟩ ⟨13, 2, 0, 559043, 301287, 933, 16384⟩
    (by decide) selected_cut_21888

theorem unmarked_context_12_75321_559044 : frontier 9 ⟨559044, by decide⟩
    (prefixCache 12 75321) (prefixPartial 12 75321) = false := by
  decide +kernel

theorem node_context_12_75321_559044 : EJMOriginalGlobalDAGData.nodes 9 ⟨559044, by decide⟩ =
    .split (coordinate 12) (![⟨558995, by decide⟩,⟨559020, by decide⟩,⟨559035, by decide⟩,⟨559043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75321_559044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75321 ⟨559044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75321
    ⟨559044, by decide⟩ (by decide) (![⟨558995, by decide⟩,⟨559020, by decide⟩,⟨559035, by decide⟩,⟨559043, by decide⟩]) unmarked_context_12_75321_559044 node_context_12_75321_559044
  intro a
  fin_cases a
  · exact context_13_301284_558995
  · exact context_13_301285_559020
  · exact context_13_301286_559035
  · exact context_13_301287_559043

theorem selected_cut_21889 : selected 8 ⟨559051, by decide⟩
    (prefixPartial 13 301288) = some ⟨13, 2, 0, 559051, 301288, 369, 16384⟩ := by
  decide +kernel

theorem context_13_301288_559051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301288 ⟨559051, by decide⟩ :=
  accepted_of_selected 13 301288 ⟨559051, by decide⟩ ⟨13, 2, 0, 559051, 301288, 369, 16384⟩
    (by decide) selected_cut_21889

theorem selected_cut_21890 : selected 8 ⟨559099, by decide⟩
    (prefixPartial 13 301289) = some ⟨13, 2, 0, 559099, 301289, 3601, 16384⟩ := by
  decide +kernel

theorem context_13_301289_559099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301289 ⟨559099, by decide⟩ :=
  accepted_of_selected 13 301289 ⟨559099, by decide⟩ ⟨13, 2, 0, 559099, 301289, 3601, 16384⟩
    (by decide) selected_cut_21890

theorem selected_cut_21891 : selected 8 ⟨559117, by decide⟩
    (prefixPartial 13 301290) = some ⟨13, 2, 0, 559117, 301290, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_301290_559117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 301290 ⟨559117, by decide⟩ :=
  accepted_of_selected 13 301290 ⟨559117, by decide⟩ ⟨13, 2, 0, 559117, 301290, 2037, 16384⟩
    (by decide) selected_cut_21891

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
