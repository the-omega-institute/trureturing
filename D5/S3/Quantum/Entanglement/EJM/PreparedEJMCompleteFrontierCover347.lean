/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover346
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33315 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440580) = some ⟨13, 1, 0, 3444, 440580, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440580_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440580 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440580 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440580, 1, 16384⟩
    (by decide) selected_cut_33315

theorem selected_cut_33316 : selected 8 ⟨857613, by decide⟩
    (prefixPartial 13 440581) = some ⟨13, 2, 0, 857613, 440581, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_440581_857613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440581 ⟨857613, by decide⟩ :=
  accepted_of_selected 13 440581 ⟨857613, by decide⟩ ⟨13, 2, 0, 857613, 440581, 2577, 16384⟩
    (by decide) selected_cut_33316

theorem selected_cut_33317 : selected 8 ⟨857634, by decide⟩
    (prefixPartial 13 440582) = some ⟨13, 2, 0, 857634, 440582, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_440582_857634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440582 ⟨857634, by decide⟩ :=
  accepted_of_selected 13 440582 ⟨857634, by decide⟩ ⟨13, 2, 0, 857634, 440582, 1361, 16384⟩
    (by decide) selected_cut_33317

theorem selected_cut_33318 : selected 8 ⟨857639, by decide⟩
    (prefixPartial 13 440583) = some ⟨13, 2, 0, 857639, 440583, 721, 16384⟩ := by
  decide +kernel

theorem context_13_440583_857639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440583 ⟨857639, by decide⟩ :=
  accepted_of_selected 13 440583 ⟨857639, by decide⟩ ⟨13, 2, 0, 857639, 440583, 721, 16384⟩
    (by decide) selected_cut_33318

theorem unmarked_context_12_110145_857640 : frontier 9 ⟨857640, by decide⟩
    (prefixCache 12 110145) (prefixPartial 12 110145) = false := by
  decide +kernel

theorem node_context_12_110145_857640 : EJMOriginalGlobalDAGData.nodes 9 ⟨857640, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨857613, by decide⟩,⟨857634, by decide⟩,⟨857639, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110145_857640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110145 ⟨857640, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110145
    ⟨857640, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨857613, by decide⟩,⟨857634, by decide⟩,⟨857639, by decide⟩]) unmarked_context_12_110145_857640 node_context_12_110145_857640
  intro a
  fin_cases a
  · exact context_13_440580_3444
  · exact context_13_440581_857613
  · exact context_13_440582_857634
  · exact context_13_440583_857639

theorem selected_cut_33319 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440584) = some ⟨13, 1, 0, 3444, 440584, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440584_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440584 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440584 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440584, 1, 16384⟩
    (by decide) selected_cut_33319

theorem selected_cut_33320 : selected 8 ⟨857665, by decide⟩
    (prefixPartial 13 440585) = some ⟨13, 2, 0, 857665, 440585, 2317, 16384⟩ := by
  decide +kernel

theorem context_13_440585_857665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440585 ⟨857665, by decide⟩ :=
  accepted_of_selected 13 440585 ⟨857665, by decide⟩ ⟨13, 2, 0, 857665, 440585, 2317, 16384⟩
    (by decide) selected_cut_33320

theorem selected_cut_33321 : selected 8 ⟨857686, by decide⟩
    (prefixPartial 13 440586) = some ⟨13, 2, 0, 857686, 440586, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_440586_857686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440586 ⟨857686, by decide⟩ :=
  accepted_of_selected 13 440586 ⟨857686, by decide⟩ ⟨13, 2, 0, 857686, 440586, 1197, 16384⟩
    (by decide) selected_cut_33321

theorem selected_cut_33322 : selected 8 ⟨857691, by decide⟩
    (prefixPartial 13 440587) = some ⟨13, 2, 0, 857691, 440587, 721, 16384⟩ := by
  decide +kernel

theorem context_13_440587_857691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440587 ⟨857691, by decide⟩ :=
  accepted_of_selected 13 440587 ⟨857691, by decide⟩ ⟨13, 2, 0, 857691, 440587, 721, 16384⟩
    (by decide) selected_cut_33322

theorem unmarked_context_12_110146_857692 : frontier 9 ⟨857692, by decide⟩
    (prefixCache 12 110146) (prefixPartial 12 110146) = false := by
  decide +kernel

theorem node_context_12_110146_857692 : EJMOriginalGlobalDAGData.nodes 9 ⟨857692, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨857665, by decide⟩,⟨857686, by decide⟩,⟨857691, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110146_857692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110146 ⟨857692, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110146
    ⟨857692, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨857665, by decide⟩,⟨857686, by decide⟩,⟨857691, by decide⟩]) unmarked_context_12_110146_857692 node_context_12_110146_857692
  intro a
  fin_cases a
  · exact context_13_440584_3444
  · exact context_13_440585_857665
  · exact context_13_440586_857686
  · exact context_13_440587_857691

theorem selected_cut_33323 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440588) = some ⟨13, 1, 0, 3444, 440588, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440588_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440588 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440588 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440588, 1, 16384⟩
    (by decide) selected_cut_33323

theorem selected_cut_33324 : selected 8 ⟨857734, by decide⟩
    (prefixPartial 13 440589) = some ⟨13, 2, 0, 857734, 440589, 2805, 16384⟩ := by
  decide +kernel

theorem context_13_440589_857734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440589 ⟨857734, by decide⟩ :=
  accepted_of_selected 13 440589 ⟨857734, by decide⟩ ⟨13, 2, 0, 857734, 440589, 2805, 16384⟩
    (by decide) selected_cut_33324

theorem selected_cut_33325 : selected 8 ⟨857760, by decide⟩
    (prefixPartial 13 440590) = some ⟨13, 2, 0, 857760, 440590, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_440590_857760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440590 ⟨857760, by decide⟩ :=
  accepted_of_selected 13 440590 ⟨857760, by decide⟩ ⟨13, 2, 0, 857760, 440590, 1489, 16384⟩
    (by decide) selected_cut_33325

theorem selected_cut_33326 : selected 8 ⟨857769, by decide⟩
    (prefixPartial 13 440591) = some ⟨13, 2, 0, 857769, 440591, 825, 16384⟩ := by
  decide +kernel

theorem context_13_440591_857769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440591 ⟨857769, by decide⟩ :=
  accepted_of_selected 13 440591 ⟨857769, by decide⟩ ⟨13, 2, 0, 857769, 440591, 825, 16384⟩
    (by decide) selected_cut_33326

theorem unmarked_context_12_110147_857770 : frontier 9 ⟨857770, by decide⟩
    (prefixCache 12 110147) (prefixPartial 12 110147) = false := by
  decide +kernel

theorem node_context_12_110147_857770 : EJMOriginalGlobalDAGData.nodes 9 ⟨857770, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨857734, by decide⟩,⟨857760, by decide⟩,⟨857769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110147_857770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110147 ⟨857770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110147
    ⟨857770, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨857734, by decide⟩,⟨857760, by decide⟩,⟨857769, by decide⟩]) unmarked_context_12_110147_857770 node_context_12_110147_857770
  intro a
  fin_cases a
  · exact context_13_440588_3444
  · exact context_13_440589_857734
  · exact context_13_440590_857760
  · exact context_13_440591_857769

theorem unmarked_context_11_27536_857771 : frontier 10 ⟨857771, by decide⟩
    (prefixCache 11 27536) (prefixPartial 11 27536) = false := by
  decide +kernel

theorem node_context_11_27536_857771 : EJMOriginalGlobalDAGData.nodes 10 ⟨857771, by decide⟩ =
    .split (coordinate 11) (![⟨857577, by decide⟩,⟨857640, by decide⟩,⟨857692, by decide⟩,⟨857770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27536_857771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27536 ⟨857771, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27536
    ⟨857771, by decide⟩ (by decide) (![⟨857577, by decide⟩,⟨857640, by decide⟩,⟨857692, by decide⟩,⟨857770, by decide⟩]) unmarked_context_11_27536_857771 node_context_11_27536_857771
  intro a
  fin_cases a
  · exact context_12_110144_857577
  · exact context_12_110145_857640
  · exact context_12_110146_857692
  · exact context_12_110147_857770

theorem selected_cut_33327 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440592) = some ⟨13, 1, 0, 3444, 440592, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440592_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440592 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440592 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440592, 1, 16384⟩
    (by decide) selected_cut_33327

theorem selected_cut_33328 : selected 8 ⟨857819, by decide⟩
    (prefixPartial 13 440593) = some ⟨13, 2, 0, 857819, 440593, 2965, 16384⟩ := by
  decide +kernel

theorem context_13_440593_857819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440593 ⟨857819, by decide⟩ :=
  accepted_of_selected 13 440593 ⟨857819, by decide⟩ ⟨13, 2, 0, 857819, 440593, 2965, 16384⟩
    (by decide) selected_cut_33328

theorem selected_cut_33329 : selected 8 ⟨857842, by decide⟩
    (prefixPartial 13 440594) = some ⟨13, 2, 0, 857842, 440594, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_440594_857842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440594 ⟨857842, by decide⟩ :=
  accepted_of_selected 13 440594 ⟨857842, by decide⟩ ⟨13, 2, 0, 857842, 440594, 1501, 16384⟩
    (by decide) selected_cut_33329

theorem selected_cut_33330 : selected 8 ⟨857846, by decide⟩
    (prefixPartial 13 440595) = some ⟨13, 2, 0, 857846, 440595, 689, 16384⟩ := by
  decide +kernel

theorem context_13_440595_857846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440595 ⟨857846, by decide⟩ :=
  accepted_of_selected 13 440595 ⟨857846, by decide⟩ ⟨13, 2, 0, 857846, 440595, 689, 16384⟩
    (by decide) selected_cut_33330

theorem unmarked_context_12_110148_857847 : frontier 9 ⟨857847, by decide⟩
    (prefixCache 12 110148) (prefixPartial 12 110148) = false := by
  decide +kernel

theorem node_context_12_110148_857847 : EJMOriginalGlobalDAGData.nodes 9 ⟨857847, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨857819, by decide⟩,⟨857842, by decide⟩,⟨857846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110148_857847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110148 ⟨857847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110148
    ⟨857847, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨857819, by decide⟩,⟨857842, by decide⟩,⟨857846, by decide⟩]) unmarked_context_12_110148_857847 node_context_12_110148_857847
  intro a
  fin_cases a
  · exact context_13_440592_3444
  · exact context_13_440593_857819
  · exact context_13_440594_857842
  · exact context_13_440595_857846

theorem selected_cut_33331 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440596) = some ⟨13, 1, 0, 3444, 440596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440596, 1, 16384⟩
    (by decide) selected_cut_33331

theorem selected_cut_33332 : selected 8 ⟨857873, by decide⟩
    (prefixPartial 13 440597) = some ⟨13, 2, 0, 857873, 440597, 2281, 16384⟩ := by
  decide +kernel

theorem context_13_440597_857873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440597 ⟨857873, by decide⟩ :=
  accepted_of_selected 13 440597 ⟨857873, by decide⟩ ⟨13, 2, 0, 857873, 440597, 2281, 16384⟩
    (by decide) selected_cut_33332

theorem selected_cut_33333 : selected 8 ⟨857892, by decide⟩
    (prefixPartial 13 440598) = some ⟨13, 2, 0, 857892, 440598, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_440598_857892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440598 ⟨857892, by decide⟩ :=
  accepted_of_selected 13 440598 ⟨857892, by decide⟩ ⟨13, 2, 0, 857892, 440598, 1389, 16384⟩
    (by decide) selected_cut_33333

theorem selected_cut_33334 : selected 8 ⟨857897, by decide⟩
    (prefixPartial 13 440599) = some ⟨13, 2, 0, 857897, 440599, 737, 16384⟩ := by
  decide +kernel

theorem context_13_440599_857897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440599 ⟨857897, by decide⟩ :=
  accepted_of_selected 13 440599 ⟨857897, by decide⟩ ⟨13, 2, 0, 857897, 440599, 737, 16384⟩
    (by decide) selected_cut_33334

theorem unmarked_context_12_110149_857898 : frontier 9 ⟨857898, by decide⟩
    (prefixCache 12 110149) (prefixPartial 12 110149) = false := by
  decide +kernel

theorem node_context_12_110149_857898 : EJMOriginalGlobalDAGData.nodes 9 ⟨857898, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨857873, by decide⟩,⟨857892, by decide⟩,⟨857897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110149_857898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110149 ⟨857898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110149
    ⟨857898, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨857873, by decide⟩,⟨857892, by decide⟩,⟨857897, by decide⟩]) unmarked_context_12_110149_857898 node_context_12_110149_857898
  intro a
  fin_cases a
  · exact context_13_440596_3444
  · exact context_13_440597_857873
  · exact context_13_440598_857892
  · exact context_13_440599_857897

theorem selected_cut_33335 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440600) = some ⟨13, 1, 0, 3444, 440600, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440600_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440600 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440600 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440600, 1, 16384⟩
    (by decide) selected_cut_33335

theorem selected_cut_33336 : selected 8 ⟨857919, by decide⟩
    (prefixPartial 13 440601) = some ⟨13, 2, 0, 857919, 440601, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_440601_857919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440601 ⟨857919, by decide⟩ :=
  accepted_of_selected 13 440601 ⟨857919, by decide⟩ ⟨13, 2, 0, 857919, 440601, 2085, 16384⟩
    (by decide) selected_cut_33336

theorem selected_cut_33337 : selected 8 ⟨857944, by decide⟩
    (prefixPartial 13 440602) = some ⟨13, 2, 0, 857944, 440602, 1345, 16384⟩ := by
  decide +kernel

theorem context_13_440602_857944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440602 ⟨857944, by decide⟩ :=
  accepted_of_selected 13 440602 ⟨857944, by decide⟩ ⟨13, 2, 0, 857944, 440602, 1345, 16384⟩
    (by decide) selected_cut_33337

theorem selected_cut_33338 : selected 8 ⟨857949, by decide⟩
    (prefixPartial 13 440603) = some ⟨13, 2, 0, 857949, 440603, 705, 16384⟩ := by
  decide +kernel

theorem context_13_440603_857949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440603 ⟨857949, by decide⟩ :=
  accepted_of_selected 13 440603 ⟨857949, by decide⟩ ⟨13, 2, 0, 857949, 440603, 705, 16384⟩
    (by decide) selected_cut_33338

theorem unmarked_context_12_110150_857950 : frontier 9 ⟨857950, by decide⟩
    (prefixCache 12 110150) (prefixPartial 12 110150) = false := by
  decide +kernel

theorem node_context_12_110150_857950 : EJMOriginalGlobalDAGData.nodes 9 ⟨857950, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨857919, by decide⟩,⟨857944, by decide⟩,⟨857949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110150_857950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110150 ⟨857950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110150
    ⟨857950, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨857919, by decide⟩,⟨857944, by decide⟩,⟨857949, by decide⟩]) unmarked_context_12_110150_857950 node_context_12_110150_857950
  intro a
  fin_cases a
  · exact context_13_440600_3444
  · exact context_13_440601_857919
  · exact context_13_440602_857944
  · exact context_13_440603_857949

theorem selected_cut_33339 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440604) = some ⟨13, 1, 0, 3444, 440604, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440604_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440604 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440604 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440604, 1, 16384⟩
    (by decide) selected_cut_33339

theorem selected_cut_33340 : selected 8 ⟨857984, by decide⟩
    (prefixPartial 13 440605) = some ⟨13, 2, 0, 857984, 440605, 2537, 16384⟩ := by
  decide +kernel

theorem context_13_440605_857984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440605 ⟨857984, by decide⟩ :=
  accepted_of_selected 13 440605 ⟨857984, by decide⟩ ⟨13, 2, 0, 857984, 440605, 2537, 16384⟩
    (by decide) selected_cut_33340

theorem selected_cut_33341 : selected 8 ⟨858010, by decide⟩
    (prefixPartial 13 440606) = some ⟨13, 2, 0, 858010, 440606, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_440606_858010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440606 ⟨858010, by decide⟩ :=
  accepted_of_selected 13 440606 ⟨858010, by decide⟩ ⟨13, 2, 0, 858010, 440606, 1617, 16384⟩
    (by decide) selected_cut_33341

theorem selected_cut_33342 : selected 8 ⟨858018, by decide⟩
    (prefixPartial 13 440607) = some ⟨13, 2, 0, 858018, 440607, 849, 16384⟩ := by
  decide +kernel

theorem context_13_440607_858018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440607 ⟨858018, by decide⟩ :=
  accepted_of_selected 13 440607 ⟨858018, by decide⟩ ⟨13, 2, 0, 858018, 440607, 849, 16384⟩
    (by decide) selected_cut_33342

theorem unmarked_context_12_110151_858019 : frontier 9 ⟨858019, by decide⟩
    (prefixCache 12 110151) (prefixPartial 12 110151) = false := by
  decide +kernel

theorem node_context_12_110151_858019 : EJMOriginalGlobalDAGData.nodes 9 ⟨858019, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨857984, by decide⟩,⟨858010, by decide⟩,⟨858018, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110151_858019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110151 ⟨858019, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110151
    ⟨858019, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨857984, by decide⟩,⟨858010, by decide⟩,⟨858018, by decide⟩]) unmarked_context_12_110151_858019 node_context_12_110151_858019
  intro a
  fin_cases a
  · exact context_13_440604_3444
  · exact context_13_440605_857984
  · exact context_13_440606_858010
  · exact context_13_440607_858018

theorem unmarked_context_11_27537_858020 : frontier 10 ⟨858020, by decide⟩
    (prefixCache 11 27537) (prefixPartial 11 27537) = false := by
  decide +kernel

theorem node_context_11_27537_858020 : EJMOriginalGlobalDAGData.nodes 10 ⟨858020, by decide⟩ =
    .split (coordinate 11) (![⟨857847, by decide⟩,⟨857898, by decide⟩,⟨857950, by decide⟩,⟨858019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27537_858020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27537 ⟨858020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27537
    ⟨858020, by decide⟩ (by decide) (![⟨857847, by decide⟩,⟨857898, by decide⟩,⟨857950, by decide⟩,⟨858019, by decide⟩]) unmarked_context_11_27537_858020 node_context_11_27537_858020
  intro a
  fin_cases a
  · exact context_12_110148_857847
  · exact context_12_110149_857898
  · exact context_12_110150_857950
  · exact context_12_110151_858019

theorem selected_cut_33343 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440608) = some ⟨13, 1, 0, 3444, 440608, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440608_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440608 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440608 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440608, 1, 16384⟩
    (by decide) selected_cut_33343

theorem selected_cut_33344 : selected 8 ⟨858053, by decide⟩
    (prefixPartial 13 440609) = some ⟨13, 2, 0, 858053, 440609, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_440609_858053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440609 ⟨858053, by decide⟩ :=
  accepted_of_selected 13 440609 ⟨858053, by decide⟩ ⟨13, 2, 0, 858053, 440609, 2381, 16384⟩
    (by decide) selected_cut_33344

theorem selected_cut_33345 : selected 8 ⟨858072, by decide⟩
    (prefixPartial 13 440610) = some ⟨13, 2, 0, 858072, 440610, 1421, 16384⟩ := by
  decide +kernel

theorem context_13_440610_858072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440610 ⟨858072, by decide⟩ :=
  accepted_of_selected 13 440610 ⟨858072, by decide⟩ ⟨13, 2, 0, 858072, 440610, 1421, 16384⟩
    (by decide) selected_cut_33345

theorem selected_cut_33346 : selected 8 ⟨858075, by decide⟩
    (prefixPartial 13 440611) = some ⟨13, 2, 0, 858075, 440611, 513, 16384⟩ := by
  decide +kernel

theorem context_13_440611_858075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440611 ⟨858075, by decide⟩ :=
  accepted_of_selected 13 440611 ⟨858075, by decide⟩ ⟨13, 2, 0, 858075, 440611, 513, 16384⟩
    (by decide) selected_cut_33346

theorem unmarked_context_12_110152_858076 : frontier 9 ⟨858076, by decide⟩
    (prefixCache 12 110152) (prefixPartial 12 110152) = false := by
  decide +kernel

theorem node_context_12_110152_858076 : EJMOriginalGlobalDAGData.nodes 9 ⟨858076, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858053, by decide⟩,⟨858072, by decide⟩,⟨858075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110152_858076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110152 ⟨858076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110152
    ⟨858076, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858053, by decide⟩,⟨858072, by decide⟩,⟨858075, by decide⟩]) unmarked_context_12_110152_858076 node_context_12_110152_858076
  intro a
  fin_cases a
  · exact context_13_440608_3444
  · exact context_13_440609_858053
  · exact context_13_440610_858072
  · exact context_13_440611_858075

theorem selected_cut_33347 : selected 9 ⟨858125, by decide⟩
    (prefixPartial 12 110153) = some ⟨12, 2, 0, 858125, 110153, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_110153_858125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110153 ⟨858125, by decide⟩ :=
  accepted_of_selected 12 110153 ⟨858125, by decide⟩ ⟨12, 2, 0, 858125, 110153, 3677, 65536⟩
    (by decide) selected_cut_33347

theorem selected_cut_33348 : selected 9 ⟨810678, by decide⟩
    (prefixPartial 12 110154) = some ⟨12, 1, 0, 810678, 110154, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110154_810678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110154 ⟨810678, by decide⟩ :=
  accepted_of_selected 12 110154 ⟨810678, by decide⟩ ⟨12, 1, 0, 810678, 110154, 1, 65536⟩
    (by decide) selected_cut_33348

theorem selected_cut_33349 : selected 9 ⟨858184, by decide⟩
    (prefixPartial 12 110155) = some ⟨12, 2, 0, 858184, 110155, 3881, 65536⟩ := by
  decide +kernel

theorem context_12_110155_858184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110155 ⟨858184, by decide⟩ :=
  accepted_of_selected 12 110155 ⟨858184, by decide⟩ ⟨12, 2, 0, 858184, 110155, 3881, 65536⟩
    (by decide) selected_cut_33349

theorem unmarked_context_11_27538_858185 : frontier 10 ⟨858185, by decide⟩
    (prefixCache 11 27538) (prefixPartial 11 27538) = false := by
  decide +kernel

theorem node_context_11_27538_858185 : EJMOriginalGlobalDAGData.nodes 10 ⟨858185, by decide⟩ =
    .split (coordinate 11) (![⟨858076, by decide⟩,⟨858125, by decide⟩,⟨810678, by decide⟩,⟨858184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27538_858185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27538 ⟨858185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27538
    ⟨858185, by decide⟩ (by decide) (![⟨858076, by decide⟩,⟨858125, by decide⟩,⟨810678, by decide⟩,⟨858184, by decide⟩]) unmarked_context_11_27538_858185 node_context_11_27538_858185
  intro a
  fin_cases a
  · exact context_12_110152_858076
  · exact context_12_110153_858125
  · exact context_12_110154_810678
  · exact context_12_110155_858184

theorem selected_cut_33350 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440624) = some ⟨13, 1, 0, 3444, 440624, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440624_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440624 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440624 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440624, 1, 16384⟩
    (by decide) selected_cut_33350

theorem selected_cut_33351 : selected 8 ⟨858230, by decide⟩
    (prefixPartial 13 440625) = some ⟨13, 2, 0, 858230, 440625, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_440625_858230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440625 ⟨858230, by decide⟩ :=
  accepted_of_selected 13 440625 ⟨858230, by decide⟩ ⟨13, 2, 0, 858230, 440625, 2421, 16384⟩
    (by decide) selected_cut_33351

theorem selected_cut_33352 : selected 8 ⟨858258, by decide⟩
    (prefixPartial 13 440626) = some ⟨13, 2, 0, 858258, 440626, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_440626_858258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440626 ⟨858258, by decide⟩ :=
  accepted_of_selected 13 440626 ⟨858258, by decide⟩ ⟨13, 2, 0, 858258, 440626, 1493, 16384⟩
    (by decide) selected_cut_33352

theorem selected_cut_33353 : selected 8 ⟨858264, by decide⟩
    (prefixPartial 13 440627) = some ⟨13, 2, 0, 858264, 440627, 757, 16384⟩ := by
  decide +kernel

theorem context_13_440627_858264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440627 ⟨858264, by decide⟩ :=
  accepted_of_selected 13 440627 ⟨858264, by decide⟩ ⟨13, 2, 0, 858264, 440627, 757, 16384⟩
    (by decide) selected_cut_33353

theorem unmarked_context_12_110156_858265 : frontier 9 ⟨858265, by decide⟩
    (prefixCache 12 110156) (prefixPartial 12 110156) = false := by
  decide +kernel

theorem node_context_12_110156_858265 : EJMOriginalGlobalDAGData.nodes 9 ⟨858265, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858230, by decide⟩,⟨858258, by decide⟩,⟨858264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110156_858265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110156 ⟨858265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110156
    ⟨858265, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858230, by decide⟩,⟨858258, by decide⟩,⟨858264, by decide⟩]) unmarked_context_12_110156_858265 node_context_12_110156_858265
  intro a
  fin_cases a
  · exact context_13_440624_3444
  · exact context_13_440625_858230
  · exact context_13_440626_858258
  · exact context_13_440627_858264

theorem selected_cut_33354 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440628) = some ⟨13, 1, 0, 3444, 440628, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440628_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440628 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440628 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440628, 1, 16384⟩
    (by decide) selected_cut_33354

theorem selected_cut_33355 : selected 8 ⟨858289, by decide⟩
    (prefixPartial 13 440629) = some ⟨13, 2, 0, 858289, 440629, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_440629_858289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440629 ⟨858289, by decide⟩ :=
  accepted_of_selected 13 440629 ⟨858289, by decide⟩ ⟨13, 2, 0, 858289, 440629, 2029, 16384⟩
    (by decide) selected_cut_33355

theorem selected_cut_33356 : selected 8 ⟨858308, by decide⟩
    (prefixPartial 13 440630) = some ⟨13, 2, 0, 858308, 440630, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_440630_858308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440630 ⟨858308, by decide⟩ :=
  accepted_of_selected 13 440630 ⟨858308, by decide⟩ ⟨13, 2, 0, 858308, 440630, 1369, 16384⟩
    (by decide) selected_cut_33356

theorem selected_cut_33357 : selected 8 ⟨858314, by decide⟩
    (prefixPartial 13 440631) = some ⟨13, 2, 0, 858314, 440631, 781, 16384⟩ := by
  decide +kernel

theorem context_13_440631_858314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440631 ⟨858314, by decide⟩ :=
  accepted_of_selected 13 440631 ⟨858314, by decide⟩ ⟨13, 2, 0, 858314, 440631, 781, 16384⟩
    (by decide) selected_cut_33357

theorem unmarked_context_12_110157_858315 : frontier 9 ⟨858315, by decide⟩
    (prefixCache 12 110157) (prefixPartial 12 110157) = false := by
  decide +kernel

theorem node_context_12_110157_858315 : EJMOriginalGlobalDAGData.nodes 9 ⟨858315, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858289, by decide⟩,⟨858308, by decide⟩,⟨858314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110157_858315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110157 ⟨858315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110157
    ⟨858315, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858289, by decide⟩,⟨858308, by decide⟩,⟨858314, by decide⟩]) unmarked_context_12_110157_858315 node_context_12_110157_858315
  intro a
  fin_cases a
  · exact context_13_440628_3444
  · exact context_13_440629_858289
  · exact context_13_440630_858308
  · exact context_13_440631_858314

theorem selected_cut_33358 : selected 9 ⟨858363, by decide⟩
    (prefixPartial 12 110158) = some ⟨12, 2, 0, 858363, 110158, 3797, 65536⟩ := by
  decide +kernel

theorem context_12_110158_858363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110158 ⟨858363, by decide⟩ :=
  accepted_of_selected 12 110158 ⟨858363, by decide⟩ ⟨12, 2, 0, 858363, 110158, 3797, 65536⟩
    (by decide) selected_cut_33358

theorem selected_cut_33359 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440636) = some ⟨13, 1, 0, 3444, 440636, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440636_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440636 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440636 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440636, 1, 16384⟩
    (by decide) selected_cut_33359

theorem selected_cut_33360 : selected 8 ⟨858388, by decide⟩
    (prefixPartial 13 440637) = some ⟨13, 2, 0, 858388, 440637, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_440637_858388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440637 ⟨858388, by decide⟩ :=
  accepted_of_selected 13 440637 ⟨858388, by decide⟩ ⟨13, 2, 0, 858388, 440637, 1973, 16384⟩
    (by decide) selected_cut_33360

theorem selected_cut_33361 : selected 8 ⟨858405, by decide⟩
    (prefixPartial 13 440638) = some ⟨13, 2, 0, 858405, 440638, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_440638_858405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440638 ⟨858405, by decide⟩ :=
  accepted_of_selected 13 440638 ⟨858405, by decide⟩ ⟨13, 2, 0, 858405, 440638, 1513, 16384⟩
    (by decide) selected_cut_33361

theorem selected_cut_33362 : selected 8 ⟨858415, by decide⟩
    (prefixPartial 13 440639) = some ⟨13, 2, 0, 858415, 440639, 857, 16384⟩ := by
  decide +kernel

theorem context_13_440639_858415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440639 ⟨858415, by decide⟩ :=
  accepted_of_selected 13 440639 ⟨858415, by decide⟩ ⟨13, 2, 0, 858415, 440639, 857, 16384⟩
    (by decide) selected_cut_33362

theorem unmarked_context_12_110159_858416 : frontier 9 ⟨858416, by decide⟩
    (prefixCache 12 110159) (prefixPartial 12 110159) = false := by
  decide +kernel

theorem node_context_12_110159_858416 : EJMOriginalGlobalDAGData.nodes 9 ⟨858416, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858388, by decide⟩,⟨858405, by decide⟩,⟨858415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110159_858416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110159 ⟨858416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110159
    ⟨858416, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858388, by decide⟩,⟨858405, by decide⟩,⟨858415, by decide⟩]) unmarked_context_12_110159_858416 node_context_12_110159_858416
  intro a
  fin_cases a
  · exact context_13_440636_3444
  · exact context_13_440637_858388
  · exact context_13_440638_858405
  · exact context_13_440639_858415

theorem unmarked_context_11_27539_858417 : frontier 10 ⟨858417, by decide⟩
    (prefixCache 11 27539) (prefixPartial 11 27539) = false := by
  decide +kernel

theorem node_context_11_27539_858417 : EJMOriginalGlobalDAGData.nodes 10 ⟨858417, by decide⟩ =
    .split (coordinate 11) (![⟨858265, by decide⟩,⟨858315, by decide⟩,⟨858363, by decide⟩,⟨858416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27539_858417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27539 ⟨858417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27539
    ⟨858417, by decide⟩ (by decide) (![⟨858265, by decide⟩,⟨858315, by decide⟩,⟨858363, by decide⟩,⟨858416, by decide⟩]) unmarked_context_11_27539_858417 node_context_11_27539_858417
  intro a
  fin_cases a
  · exact context_12_110156_858265
  · exact context_12_110157_858315
  · exact context_12_110158_858363
  · exact context_12_110159_858416

theorem unmarked_context_10_6884_858418 : frontier 11 ⟨858418, by decide⟩
    (prefixCache 10 6884) (prefixPartial 10 6884) = false := by
  decide +kernel

theorem node_context_10_6884_858418 : EJMOriginalGlobalDAGData.nodes 11 ⟨858418, by decide⟩ =
    .split (coordinate 10) (![⟨857771, by decide⟩,⟨858020, by decide⟩,⟨858185, by decide⟩,⟨858417, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6884_858418 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6884 ⟨858418, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6884
    ⟨858418, by decide⟩ (by decide) (![⟨857771, by decide⟩,⟨858020, by decide⟩,⟨858185, by decide⟩,⟨858417, by decide⟩]) unmarked_context_10_6884_858418 node_context_10_6884_858418
  intro a
  fin_cases a
  · exact context_11_27536_857771
  · exact context_11_27537_858020
  · exact context_11_27538_858185
  · exact context_11_27539_858417

theorem selected_cut_33363 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440640) = some ⟨13, 1, 0, 3444, 440640, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440640_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440640 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440640 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440640, 1, 16384⟩
    (by decide) selected_cut_33363

theorem selected_cut_33364 : selected 8 ⟨858454, by decide⟩
    (prefixPartial 13 440641) = some ⟨13, 2, 0, 858454, 440641, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_440641_858454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440641 ⟨858454, by decide⟩ :=
  accepted_of_selected 13 440641 ⟨858454, by decide⟩ ⟨13, 2, 0, 858454, 440641, 2173, 16384⟩
    (by decide) selected_cut_33364

theorem selected_cut_33365 : selected 8 ⟨858489, by decide⟩
    (prefixPartial 13 440642) = some ⟨13, 2, 0, 858489, 440642, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_440642_858489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440642 ⟨858489, by decide⟩ :=
  accepted_of_selected 13 440642 ⟨858489, by decide⟩ ⟨13, 2, 0, 858489, 440642, 1621, 16384⟩
    (by decide) selected_cut_33365

theorem selected_cut_33366 : selected 8 ⟨858497, by decide⟩
    (prefixPartial 13 440643) = some ⟨13, 2, 0, 858497, 440643, 729, 16384⟩ := by
  decide +kernel

theorem context_13_440643_858497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440643 ⟨858497, by decide⟩ :=
  accepted_of_selected 13 440643 ⟨858497, by decide⟩ ⟨13, 2, 0, 858497, 440643, 729, 16384⟩
    (by decide) selected_cut_33366

theorem unmarked_context_12_110160_858498 : frontier 9 ⟨858498, by decide⟩
    (prefixCache 12 110160) (prefixPartial 12 110160) = false := by
  decide +kernel

theorem node_context_12_110160_858498 : EJMOriginalGlobalDAGData.nodes 9 ⟨858498, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858454, by decide⟩,⟨858489, by decide⟩,⟨858497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110160_858498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110160 ⟨858498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110160
    ⟨858498, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858454, by decide⟩,⟨858489, by decide⟩,⟨858497, by decide⟩]) unmarked_context_12_110160_858498 node_context_12_110160_858498
  intro a
  fin_cases a
  · exact context_13_440640_3444
  · exact context_13_440641_858454
  · exact context_13_440642_858489
  · exact context_13_440643_858497

theorem selected_cut_33367 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440644) = some ⟨13, 1, 0, 3444, 440644, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440644_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440644 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440644 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440644, 1, 16384⟩
    (by decide) selected_cut_33367

theorem selected_cut_33368 : selected 8 ⟨858531, by decide⟩
    (prefixPartial 13 440645) = some ⟨13, 2, 0, 858531, 440645, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_440645_858531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440645 ⟨858531, by decide⟩ :=
  accepted_of_selected 13 440645 ⟨858531, by decide⟩ ⟨13, 2, 0, 858531, 440645, 1977, 16384⟩
    (by decide) selected_cut_33368

theorem selected_cut_33369 : selected 8 ⟨858552, by decide⟩
    (prefixPartial 13 440646) = some ⟨13, 2, 0, 858552, 440646, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_440646_858552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440646 ⟨858552, by decide⟩ :=
  accepted_of_selected 13 440646 ⟨858552, by decide⟩ ⟨13, 2, 0, 858552, 440646, 1601, 16384⟩
    (by decide) selected_cut_33369

theorem selected_cut_33370 : selected 8 ⟨858561, by decide⟩
    (prefixPartial 13 440647) = some ⟨13, 2, 0, 858561, 440647, 901, 16384⟩ := by
  decide +kernel

theorem context_13_440647_858561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440647 ⟨858561, by decide⟩ :=
  accepted_of_selected 13 440647 ⟨858561, by decide⟩ ⟨13, 2, 0, 858561, 440647, 901, 16384⟩
    (by decide) selected_cut_33370

theorem unmarked_context_12_110161_858562 : frontier 9 ⟨858562, by decide⟩
    (prefixCache 12 110161) (prefixPartial 12 110161) = false := by
  decide +kernel

theorem node_context_12_110161_858562 : EJMOriginalGlobalDAGData.nodes 9 ⟨858562, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858531, by decide⟩,⟨858552, by decide⟩,⟨858561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110161_858562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110161 ⟨858562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110161
    ⟨858562, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858531, by decide⟩,⟨858552, by decide⟩,⟨858561, by decide⟩]) unmarked_context_12_110161_858562 node_context_12_110161_858562
  intro a
  fin_cases a
  · exact context_13_440644_3444
  · exact context_13_440645_858531
  · exact context_13_440646_858552
  · exact context_13_440647_858561

theorem selected_cut_33371 : selected 9 ⟨858598, by decide⟩
    (prefixPartial 12 110162) = some ⟨12, 2, 0, 858598, 110162, 3741, 65536⟩ := by
  decide +kernel

theorem context_12_110162_858598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110162 ⟨858598, by decide⟩ :=
  accepted_of_selected 12 110162 ⟨858598, by decide⟩ ⟨12, 2, 0, 858598, 110162, 3741, 65536⟩
    (by decide) selected_cut_33371

theorem selected_cut_33372 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440652) = some ⟨13, 1, 0, 3444, 440652, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440652_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440652 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440652 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440652, 1, 16384⟩
    (by decide) selected_cut_33372

theorem selected_cut_33373 : selected 8 ⟨858639, by decide⟩
    (prefixPartial 13 440653) = some ⟨13, 2, 0, 858639, 440653, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_440653_858639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440653 ⟨858639, by decide⟩ :=
  accepted_of_selected 13 440653 ⟨858639, by decide⟩ ⟨13, 2, 0, 858639, 440653, 2289, 16384⟩
    (by decide) selected_cut_33373

theorem selected_cut_33374 : selected 8 ⟨858673, by decide⟩
    (prefixPartial 13 440654) = some ⟨13, 2, 0, 858673, 440654, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_440654_858673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440654 ⟨858673, by decide⟩ :=
  accepted_of_selected 13 440654 ⟨858673, by decide⟩ ⟨13, 2, 0, 858673, 440654, 1745, 16384⟩
    (by decide) selected_cut_33374

theorem selected_cut_33375 : selected 8 ⟨858680, by decide⟩
    (prefixPartial 13 440655) = some ⟨13, 2, 0, 858680, 440655, 877, 16384⟩ := by
  decide +kernel

theorem context_13_440655_858680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440655 ⟨858680, by decide⟩ :=
  accepted_of_selected 13 440655 ⟨858680, by decide⟩ ⟨13, 2, 0, 858680, 440655, 877, 16384⟩
    (by decide) selected_cut_33375

theorem unmarked_context_12_110163_858681 : frontier 9 ⟨858681, by decide⟩
    (prefixCache 12 110163) (prefixPartial 12 110163) = false := by
  decide +kernel

theorem node_context_12_110163_858681 : EJMOriginalGlobalDAGData.nodes 9 ⟨858681, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858639, by decide⟩,⟨858673, by decide⟩,⟨858680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110163_858681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110163 ⟨858681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110163
    ⟨858681, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858639, by decide⟩,⟨858673, by decide⟩,⟨858680, by decide⟩]) unmarked_context_12_110163_858681 node_context_12_110163_858681
  intro a
  fin_cases a
  · exact context_13_440652_3444
  · exact context_13_440653_858639
  · exact context_13_440654_858673
  · exact context_13_440655_858680

theorem unmarked_context_11_27540_858682 : frontier 10 ⟨858682, by decide⟩
    (prefixCache 11 27540) (prefixPartial 11 27540) = false := by
  decide +kernel

theorem node_context_11_27540_858682 : EJMOriginalGlobalDAGData.nodes 10 ⟨858682, by decide⟩ =
    .split (coordinate 11) (![⟨858498, by decide⟩,⟨858562, by decide⟩,⟨858598, by decide⟩,⟨858681, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27540_858682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27540 ⟨858682, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27540
    ⟨858682, by decide⟩ (by decide) (![⟨858498, by decide⟩,⟨858562, by decide⟩,⟨858598, by decide⟩,⟨858681, by decide⟩]) unmarked_context_11_27540_858682 node_context_11_27540_858682
  intro a
  fin_cases a
  · exact context_12_110160_858498
  · exact context_12_110161_858562
  · exact context_12_110162_858598
  · exact context_12_110163_858681

theorem selected_cut_33376 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440656) = some ⟨13, 1, 0, 3444, 440656, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440656_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440656 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440656 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440656, 1, 16384⟩
    (by decide) selected_cut_33376

theorem selected_cut_33377 : selected 8 ⟨858708, by decide⟩
    (prefixPartial 13 440657) = some ⟨13, 2, 0, 858708, 440657, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_440657_858708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440657 ⟨858708, by decide⟩ :=
  accepted_of_selected 13 440657 ⟨858708, by decide⟩ ⟨13, 2, 0, 858708, 440657, 1837, 16384⟩
    (by decide) selected_cut_33377

theorem selected_cut_33378 : selected 8 ⟨858741, by decide⟩
    (prefixPartial 13 440658) = some ⟨13, 2, 0, 858741, 440658, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_440658_858741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440658 ⟨858741, by decide⟩ :=
  accepted_of_selected 13 440658 ⟨858741, by decide⟩ ⟨13, 2, 0, 858741, 440658, 1685, 16384⟩
    (by decide) selected_cut_33378

theorem selected_cut_33379 : selected 8 ⟨858749, by decide⟩
    (prefixPartial 13 440659) = some ⟨13, 2, 0, 858749, 440659, 665, 16384⟩ := by
  decide +kernel

theorem context_13_440659_858749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440659 ⟨858749, by decide⟩ :=
  accepted_of_selected 13 440659 ⟨858749, by decide⟩ ⟨13, 2, 0, 858749, 440659, 665, 16384⟩
    (by decide) selected_cut_33379

theorem unmarked_context_12_110164_858750 : frontier 9 ⟨858750, by decide⟩
    (prefixCache 12 110164) (prefixPartial 12 110164) = false := by
  decide +kernel

theorem node_context_12_110164_858750 : EJMOriginalGlobalDAGData.nodes 9 ⟨858750, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858708, by decide⟩,⟨858741, by decide⟩,⟨858749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110164_858750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110164 ⟨858750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110164
    ⟨858750, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858708, by decide⟩,⟨858741, by decide⟩,⟨858749, by decide⟩]) unmarked_context_12_110164_858750 node_context_12_110164_858750
  intro a
  fin_cases a
  · exact context_13_440656_3444
  · exact context_13_440657_858708
  · exact context_13_440658_858741
  · exact context_13_440659_858749

theorem selected_cut_33380 : selected 9 ⟨858802, by decide⟩
    (prefixPartial 12 110165) = some ⟨12, 2, 0, 858802, 110165, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_110165_858802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110165 ⟨858802, by decide⟩ :=
  accepted_of_selected 12 110165 ⟨858802, by decide⟩ ⟨12, 2, 0, 858802, 110165, 3933, 65536⟩
    (by decide) selected_cut_33380

theorem selected_cut_33381 : selected 9 ⟨858843, by decide⟩
    (prefixPartial 12 110166) = some ⟨12, 2, 0, 858843, 110166, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_110166_858843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110166 ⟨858843, by decide⟩ :=
  accepted_of_selected 12 110166 ⟨858843, by decide⟩ ⟨12, 2, 0, 858843, 110166, 3461, 65536⟩
    (by decide) selected_cut_33381

theorem selected_cut_33382 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440668) = some ⟨13, 1, 0, 3444, 440668, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440668_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440668 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440668 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440668, 1, 16384⟩
    (by decide) selected_cut_33382

theorem selected_cut_33383 : selected 8 ⟨858872, by decide⟩
    (prefixPartial 13 440669) = some ⟨13, 2, 0, 858872, 440669, 1777, 16384⟩ := by
  decide +kernel

theorem context_13_440669_858872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440669 ⟨858872, by decide⟩ :=
  accepted_of_selected 13 440669 ⟨858872, by decide⟩ ⟨13, 2, 0, 858872, 440669, 1777, 16384⟩
    (by decide) selected_cut_33383

theorem selected_cut_33384 : selected 8 ⟨858924, by decide⟩
    (prefixPartial 13 440670) = some ⟨13, 2, 0, 858924, 440670, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_440670_858924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440670 ⟨858924, by decide⟩ :=
  accepted_of_selected 13 440670 ⟨858924, by decide⟩ ⟨13, 2, 0, 858924, 440670, 1957, 16384⟩
    (by decide) selected_cut_33384

theorem selected_cut_33385 : selected 8 ⟨858933, by decide⟩
    (prefixPartial 13 440671) = some ⟨13, 2, 0, 858933, 440671, 797, 16384⟩ := by
  decide +kernel

theorem context_13_440671_858933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440671 ⟨858933, by decide⟩ :=
  accepted_of_selected 13 440671 ⟨858933, by decide⟩ ⟨13, 2, 0, 858933, 440671, 797, 16384⟩
    (by decide) selected_cut_33385

theorem unmarked_context_12_110167_858934 : frontier 9 ⟨858934, by decide⟩
    (prefixCache 12 110167) (prefixPartial 12 110167) = false := by
  decide +kernel

theorem node_context_12_110167_858934 : EJMOriginalGlobalDAGData.nodes 9 ⟨858934, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨858872, by decide⟩,⟨858924, by decide⟩,⟨858933, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110167_858934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110167 ⟨858934, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110167
    ⟨858934, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨858872, by decide⟩,⟨858924, by decide⟩,⟨858933, by decide⟩]) unmarked_context_12_110167_858934 node_context_12_110167_858934
  intro a
  fin_cases a
  · exact context_13_440668_3444
  · exact context_13_440669_858872
  · exact context_13_440670_858924
  · exact context_13_440671_858933

theorem unmarked_context_11_27541_858935 : frontier 10 ⟨858935, by decide⟩
    (prefixCache 11 27541) (prefixPartial 11 27541) = false := by
  decide +kernel

theorem node_context_11_27541_858935 : EJMOriginalGlobalDAGData.nodes 10 ⟨858935, by decide⟩ =
    .split (coordinate 11) (![⟨858750, by decide⟩,⟨858802, by decide⟩,⟨858843, by decide⟩,⟨858934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27541_858935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27541 ⟨858935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27541
    ⟨858935, by decide⟩ (by decide) (![⟨858750, by decide⟩,⟨858802, by decide⟩,⟨858843, by decide⟩,⟨858934, by decide⟩]) unmarked_context_11_27541_858935 node_context_11_27541_858935
  intro a
  fin_cases a
  · exact context_12_110164_858750
  · exact context_12_110165_858802
  · exact context_12_110166_858843
  · exact context_12_110167_858934

theorem selected_cut_33386 : selected 9 ⟨858986, by decide⟩
    (prefixPartial 12 110168) = some ⟨12, 2, 0, 858986, 110168, 3389, 65536⟩ := by
  decide +kernel

theorem context_12_110168_858986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110168 ⟨858986, by decide⟩ :=
  accepted_of_selected 12 110168 ⟨858986, by decide⟩ ⟨12, 2, 0, 858986, 110168, 3389, 65536⟩
    (by decide) selected_cut_33386

theorem selected_cut_33387 : selected 9 ⟨859028, by decide⟩
    (prefixPartial 12 110169) = some ⟨12, 2, 0, 859028, 110169, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_110169_859028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110169 ⟨859028, by decide⟩ :=
  accepted_of_selected 12 110169 ⟨859028, by decide⟩ ⟨12, 2, 0, 859028, 110169, 3137, 65536⟩
    (by decide) selected_cut_33387

theorem selected_cut_33388 : selected 9 ⟨859029, by decide⟩
    (prefixPartial 12 110170) = some ⟨12, 1, 0, 859029, 110170, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110170_859029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110170 ⟨859029, by decide⟩ :=
  accepted_of_selected 12 110170 ⟨859029, by decide⟩ ⟨12, 1, 0, 859029, 110170, 1, 65536⟩
    (by decide) selected_cut_33388

theorem selected_cut_33389 : selected 9 ⟨859077, by decide⟩
    (prefixPartial 12 110171) = some ⟨12, 2, 0, 859077, 110171, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_110171_859077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110171 ⟨859077, by decide⟩ :=
  accepted_of_selected 12 110171 ⟨859077, by decide⟩ ⟨12, 2, 0, 859077, 110171, 3429, 65536⟩
    (by decide) selected_cut_33389

theorem unmarked_context_11_27542_859078 : frontier 10 ⟨859078, by decide⟩
    (prefixCache 11 27542) (prefixPartial 11 27542) = false := by
  decide +kernel

theorem node_context_11_27542_859078 : EJMOriginalGlobalDAGData.nodes 10 ⟨859078, by decide⟩ =
    .split (coordinate 11) (![⟨858986, by decide⟩,⟨859028, by decide⟩,⟨859029, by decide⟩,⟨859077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27542_859078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27542 ⟨859078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27542
    ⟨859078, by decide⟩ (by decide) (![⟨858986, by decide⟩,⟨859028, by decide⟩,⟨859029, by decide⟩,⟨859077, by decide⟩]) unmarked_context_11_27542_859078 node_context_11_27542_859078
  intro a
  fin_cases a
  · exact context_12_110168_858986
  · exact context_12_110169_859028
  · exact context_12_110170_859029
  · exact context_12_110171_859077

theorem selected_cut_33390 : selected 9 ⟨859136, by decide⟩
    (prefixPartial 12 110172) = some ⟨12, 2, 0, 859136, 110172, 3817, 65536⟩ := by
  decide +kernel

theorem context_12_110172_859136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110172 ⟨859136, by decide⟩ :=
  accepted_of_selected 12 110172 ⟨859136, by decide⟩ ⟨12, 2, 0, 859136, 110172, 3817, 65536⟩
    (by decide) selected_cut_33390

theorem selected_cut_33391 : selected 9 ⟨859189, by decide⟩
    (prefixPartial 12 110173) = some ⟨12, 2, 0, 859189, 110173, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_110173_859189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110173 ⟨859189, by decide⟩ :=
  accepted_of_selected 12 110173 ⟨859189, by decide⟩ ⟨12, 2, 0, 859189, 110173, 3701, 65536⟩
    (by decide) selected_cut_33391

theorem selected_cut_33392 : selected 9 ⟨859227, by decide⟩
    (prefixPartial 12 110174) = some ⟨12, 2, 0, 859227, 110174, 3165, 65536⟩ := by
  decide +kernel

theorem context_12_110174_859227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110174 ⟨859227, by decide⟩ :=
  accepted_of_selected 12 110174 ⟨859227, by decide⟩ ⟨12, 2, 0, 859227, 110174, 3165, 65536⟩
    (by decide) selected_cut_33392

theorem selected_cut_33393 : selected 9 ⟨859286, by decide⟩
    (prefixPartial 12 110175) = some ⟨12, 2, 0, 859286, 110175, 3829, 65536⟩ := by
  decide +kernel

theorem context_12_110175_859286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110175 ⟨859286, by decide⟩ :=
  accepted_of_selected 12 110175 ⟨859286, by decide⟩ ⟨12, 2, 0, 859286, 110175, 3829, 65536⟩
    (by decide) selected_cut_33393

theorem unmarked_context_11_27543_859287 : frontier 10 ⟨859287, by decide⟩
    (prefixCache 11 27543) (prefixPartial 11 27543) = false := by
  decide +kernel

theorem node_context_11_27543_859287 : EJMOriginalGlobalDAGData.nodes 10 ⟨859287, by decide⟩ =
    .split (coordinate 11) (![⟨859136, by decide⟩,⟨859189, by decide⟩,⟨859227, by decide⟩,⟨859286, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27543_859287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27543 ⟨859287, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27543
    ⟨859287, by decide⟩ (by decide) (![⟨859136, by decide⟩,⟨859189, by decide⟩,⟨859227, by decide⟩,⟨859286, by decide⟩]) unmarked_context_11_27543_859287 node_context_11_27543_859287
  intro a
  fin_cases a
  · exact context_12_110172_859136
  · exact context_12_110173_859189
  · exact context_12_110174_859227
  · exact context_12_110175_859286

theorem unmarked_context_10_6885_859288 : frontier 11 ⟨859288, by decide⟩
    (prefixCache 10 6885) (prefixPartial 10 6885) = false := by
  decide +kernel

theorem node_context_10_6885_859288 : EJMOriginalGlobalDAGData.nodes 11 ⟨859288, by decide⟩ =
    .split (coordinate 10) (![⟨858682, by decide⟩,⟨858935, by decide⟩,⟨859078, by decide⟩,⟨859287, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6885_859288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6885 ⟨859288, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6885
    ⟨859288, by decide⟩ (by decide) (![⟨858682, by decide⟩,⟨858935, by decide⟩,⟨859078, by decide⟩,⟨859287, by decide⟩]) unmarked_context_10_6885_859288 node_context_10_6885_859288
  intro a
  fin_cases a
  · exact context_11_27540_858682
  · exact context_11_27541_858935
  · exact context_11_27542_859078
  · exact context_11_27543_859287

theorem selected_cut_33394 : selected 9 ⟨859357, by decide⟩
    (prefixPartial 12 110176) = some ⟨12, 2, 0, 859357, 110176, 3469, 65536⟩ := by
  decide +kernel

theorem context_12_110176_859357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110176 ⟨859357, by decide⟩ :=
  accepted_of_selected 12 110176 ⟨859357, by decide⟩ ⟨12, 2, 0, 859357, 110176, 3469, 65536⟩
    (by decide) selected_cut_33394

theorem selected_cut_33395 : selected 9 ⟨859412, by decide⟩
    (prefixPartial 12 110177) = some ⟨12, 2, 0, 859412, 110177, 3361, 65536⟩ := by
  decide +kernel

theorem context_12_110177_859412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110177 ⟨859412, by decide⟩ :=
  accepted_of_selected 12 110177 ⟨859412, by decide⟩ ⟨12, 2, 0, 859412, 110177, 3361, 65536⟩
    (by decide) selected_cut_33395

theorem selected_cut_33396 : selected 9 ⟨859447, by decide⟩
    (prefixPartial 12 110178) = some ⟨12, 2, 0, 859447, 110178, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_110178_859447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110178 ⟨859447, by decide⟩ :=
  accepted_of_selected 12 110178 ⟨859447, by decide⟩ ⟨12, 2, 0, 859447, 110178, 2741, 65536⟩
    (by decide) selected_cut_33396

theorem selected_cut_33397 : selected 9 ⟨859518, by decide⟩
    (prefixPartial 12 110179) = some ⟨12, 2, 0, 859518, 110179, 3685, 65536⟩ := by
  decide +kernel

theorem context_12_110179_859518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110179 ⟨859518, by decide⟩ :=
  accepted_of_selected 12 110179 ⟨859518, by decide⟩ ⟨12, 2, 0, 859518, 110179, 3685, 65536⟩
    (by decide) selected_cut_33397

theorem unmarked_context_11_27544_859519 : frontier 10 ⟨859519, by decide⟩
    (prefixCache 11 27544) (prefixPartial 11 27544) = false := by
  decide +kernel

theorem node_context_11_27544_859519 : EJMOriginalGlobalDAGData.nodes 10 ⟨859519, by decide⟩ =
    .split (coordinate 11) (![⟨859357, by decide⟩,⟨859412, by decide⟩,⟨859447, by decide⟩,⟨859518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27544_859519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27544 ⟨859519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27544
    ⟨859519, by decide⟩ (by decide) (![⟨859357, by decide⟩,⟨859412, by decide⟩,⟨859447, by decide⟩,⟨859518, by decide⟩]) unmarked_context_11_27544_859519 node_context_11_27544_859519
  intro a
  fin_cases a
  · exact context_12_110176_859357
  · exact context_12_110177_859412
  · exact context_12_110178_859447
  · exact context_12_110179_859518

theorem selected_cut_33398 : selected 9 ⟨859573, by decide⟩
    (prefixPartial 12 110180) = some ⟨12, 2, 0, 859573, 110180, 3273, 65536⟩ := by
  decide +kernel

theorem context_12_110180_859573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110180 ⟨859573, by decide⟩ :=
  accepted_of_selected 12 110180 ⟨859573, by decide⟩ ⟨12, 2, 0, 859573, 110180, 3273, 65536⟩
    (by decide) selected_cut_33398

theorem selected_cut_33399 : selected 9 ⟨859614, by decide⟩
    (prefixPartial 12 110181) = some ⟨12, 2, 0, 859614, 110181, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_110181_859614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110181 ⟨859614, by decide⟩ :=
  accepted_of_selected 12 110181 ⟨859614, by decide⟩ ⟨12, 2, 0, 859614, 110181, 3141, 65536⟩
    (by decide) selected_cut_33399

theorem selected_cut_33400 : selected 9 ⟨859653, by decide⟩
    (prefixPartial 12 110182) = some ⟨12, 2, 0, 859653, 110182, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_110182_859653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110182 ⟨859653, by decide⟩ :=
  accepted_of_selected 12 110182 ⟨859653, by decide⟩ ⟨12, 2, 0, 859653, 110182, 2729, 65536⟩
    (by decide) selected_cut_33400

theorem selected_cut_33401 : selected 9 ⟨859715, by decide⟩
    (prefixPartial 12 110183) = some ⟨12, 2, 0, 859715, 110183, 3457, 65536⟩ := by
  decide +kernel

theorem context_12_110183_859715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110183 ⟨859715, by decide⟩ :=
  accepted_of_selected 12 110183 ⟨859715, by decide⟩ ⟨12, 2, 0, 859715, 110183, 3457, 65536⟩
    (by decide) selected_cut_33401

theorem unmarked_context_11_27545_859716 : frontier 10 ⟨859716, by decide⟩
    (prefixCache 11 27545) (prefixPartial 11 27545) = false := by
  decide +kernel

theorem node_context_11_27545_859716 : EJMOriginalGlobalDAGData.nodes 10 ⟨859716, by decide⟩ =
    .split (coordinate 11) (![⟨859573, by decide⟩,⟨859614, by decide⟩,⟨859653, by decide⟩,⟨859715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27545_859716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27545 ⟨859716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27545
    ⟨859716, by decide⟩ (by decide) (![⟨859573, by decide⟩,⟨859614, by decide⟩,⟨859653, by decide⟩,⟨859715, by decide⟩]) unmarked_context_11_27545_859716 node_context_11_27545_859716
  intro a
  fin_cases a
  · exact context_12_110180_859573
  · exact context_12_110181_859614
  · exact context_12_110182_859653
  · exact context_12_110183_859715

theorem selected_cut_33402 : selected 9 ⟨859754, by decide⟩
    (prefixPartial 12 110184) = some ⟨12, 2, 0, 859754, 110184, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_110184_859754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110184 ⟨859754, by decide⟩ :=
  accepted_of_selected 12 110184 ⟨859754, by decide⟩ ⟨12, 2, 0, 859754, 110184, 2561, 65536⟩
    (by decide) selected_cut_33402

theorem selected_cut_33403 : selected 9 ⟨859788, by decide⟩
    (prefixPartial 12 110185) = some ⟨12, 2, 0, 859788, 110185, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_110185_859788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110185 ⟨859788, by decide⟩ :=
  accepted_of_selected 12 110185 ⟨859788, by decide⟩ ⟨12, 2, 0, 859788, 110185, 2417, 65536⟩
    (by decide) selected_cut_33403

theorem selected_cut_33404 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 110186) = some ⟨12, 1, 0, 445248, 110186, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110186_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110186 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 110186 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 110186, 1, 65536⟩
    (by decide) selected_cut_33404

theorem selected_cut_33405 : selected 9 ⟨859821, by decide⟩
    (prefixPartial 12 110187) = some ⟨12, 2, 0, 859821, 110187, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_110187_859821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110187 ⟨859821, by decide⟩ :=
  accepted_of_selected 12 110187 ⟨859821, by decide⟩ ⟨12, 2, 0, 859821, 110187, 2561, 65536⟩
    (by decide) selected_cut_33405

theorem unmarked_context_11_27546_859822 : frontier 10 ⟨859822, by decide⟩
    (prefixCache 11 27546) (prefixPartial 11 27546) = false := by
  decide +kernel

theorem node_context_11_27546_859822 : EJMOriginalGlobalDAGData.nodes 10 ⟨859822, by decide⟩ =
    .split (coordinate 11) (![⟨859754, by decide⟩,⟨859788, by decide⟩,⟨445248, by decide⟩,⟨859821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27546_859822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27546 ⟨859822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27546
    ⟨859822, by decide⟩ (by decide) (![⟨859754, by decide⟩,⟨859788, by decide⟩,⟨445248, by decide⟩,⟨859821, by decide⟩]) unmarked_context_11_27546_859822 node_context_11_27546_859822
  intro a
  fin_cases a
  · exact context_12_110184_859754
  · exact context_12_110185_859788
  · exact context_12_110186_445248
  · exact context_12_110187_859821

theorem selected_cut_33406 : selected 9 ⟨859862, by decide⟩
    (prefixPartial 12 110188) = some ⟨12, 2, 0, 859862, 110188, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_110188_859862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110188 ⟨859862, by decide⟩ :=
  accepted_of_selected 12 110188 ⟨859862, by decide⟩ ⟨12, 2, 0, 859862, 110188, 3017, 65536⟩
    (by decide) selected_cut_33406

theorem selected_cut_33407 : selected 9 ⟨859901, by decide⟩
    (prefixPartial 12 110189) = some ⟨12, 2, 0, 859901, 110189, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_110189_859901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110189 ⟨859901, by decide⟩ :=
  accepted_of_selected 12 110189 ⟨859901, by decide⟩ ⟨12, 2, 0, 859901, 110189, 2893, 65536⟩
    (by decide) selected_cut_33407

theorem selected_cut_33408 : selected 9 ⟨859928, by decide⟩
    (prefixPartial 12 110190) = some ⟨12, 2, 0, 859928, 110190, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_110190_859928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110190 ⟨859928, by decide⟩ :=
  accepted_of_selected 12 110190 ⟨859928, by decide⟩ ⟨12, 2, 0, 859928, 110190, 2393, 65536⟩
    (by decide) selected_cut_33408

theorem selected_cut_33409 : selected 9 ⟨859972, by decide⟩
    (prefixPartial 12 110191) = some ⟨12, 2, 0, 859972, 110191, 2957, 65536⟩ := by
  decide +kernel

theorem context_12_110191_859972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110191 ⟨859972, by decide⟩ :=
  accepted_of_selected 12 110191 ⟨859972, by decide⟩ ⟨12, 2, 0, 859972, 110191, 2957, 65536⟩
    (by decide) selected_cut_33409

theorem unmarked_context_11_27547_859973 : frontier 10 ⟨859973, by decide⟩
    (prefixCache 11 27547) (prefixPartial 11 27547) = false := by
  decide +kernel

theorem node_context_11_27547_859973 : EJMOriginalGlobalDAGData.nodes 10 ⟨859973, by decide⟩ =
    .split (coordinate 11) (![⟨859862, by decide⟩,⟨859901, by decide⟩,⟨859928, by decide⟩,⟨859972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27547_859973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27547 ⟨859973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27547
    ⟨859973, by decide⟩ (by decide) (![⟨859862, by decide⟩,⟨859901, by decide⟩,⟨859928, by decide⟩,⟨859972, by decide⟩]) unmarked_context_11_27547_859973 node_context_11_27547_859973
  intro a
  fin_cases a
  · exact context_12_110188_859862
  · exact context_12_110189_859901
  · exact context_12_110190_859928
  · exact context_12_110191_859972

theorem unmarked_context_10_6886_859974 : frontier 11 ⟨859974, by decide⟩
    (prefixCache 10 6886) (prefixPartial 10 6886) = false := by
  decide +kernel

theorem node_context_10_6886_859974 : EJMOriginalGlobalDAGData.nodes 11 ⟨859974, by decide⟩ =
    .split (coordinate 10) (![⟨859519, by decide⟩,⟨859716, by decide⟩,⟨859822, by decide⟩,⟨859973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6886_859974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6886 ⟨859974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6886
    ⟨859974, by decide⟩ (by decide) (![⟨859519, by decide⟩,⟨859716, by decide⟩,⟨859822, by decide⟩,⟨859973, by decide⟩]) unmarked_context_10_6886_859974 node_context_10_6886_859974
  intro a
  fin_cases a
  · exact context_11_27544_859519
  · exact context_11_27545_859716
  · exact context_11_27546_859822
  · exact context_11_27547_859973

theorem selected_cut_33410 : selected 9 ⟨860027, by decide⟩
    (prefixPartial 12 110192) = some ⟨12, 2, 0, 860027, 110192, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_110192_860027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110192 ⟨860027, by decide⟩ :=
  accepted_of_selected 12 110192 ⟨860027, by decide⟩ ⟨12, 2, 0, 860027, 110192, 2757, 65536⟩
    (by decide) selected_cut_33410

theorem selected_cut_33411 : selected 9 ⟨860061, by decide⟩
    (prefixPartial 12 110193) = some ⟨12, 2, 0, 860061, 110193, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_110193_860061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110193 ⟨860061, by decide⟩ :=
  accepted_of_selected 12 110193 ⟨860061, by decide⟩ ⟨12, 2, 0, 860061, 110193, 2553, 65536⟩
    (by decide) selected_cut_33411

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
