/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover105
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_10180 : selected 8 ⟨277899, by decide⟩
    (prefixPartial 13 99583) = some ⟨13, 2, 0, 277899, 99583, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_99583_277899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99583 ⟨277899, by decide⟩ :=
  accepted_of_selected 13 99583 ⟨277899, by decide⟩ ⟨13, 2, 0, 277899, 99583, 1041, 16384⟩
    (by decide) selected_cut_10180

theorem unmarked_context_12_24895_277900 : frontier 9 ⟨277900, by decide⟩
    (prefixCache 12 24895) (prefixPartial 12 24895) = false := by
  decide +kernel

theorem node_context_12_24895_277900 : EJMOriginalGlobalDAGData.nodes 9 ⟨277900, by decide⟩ =
    .split (coordinate 12) (![⟨277847, by decide⟩,⟨277871, by decide⟩,⟨277891, by decide⟩,⟨277899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24895_277900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24895 ⟨277900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24895
    ⟨277900, by decide⟩ (by decide) (![⟨277847, by decide⟩,⟨277871, by decide⟩,⟨277891, by decide⟩,⟨277899, by decide⟩]) unmarked_context_12_24895_277900 node_context_12_24895_277900
  intro a
  fin_cases a
  · exact context_13_99580_277847
  · exact context_13_99581_277871
  · exact context_13_99582_277891
  · exact context_13_99583_277899

theorem unmarked_context_11_6223_277901 : frontier 10 ⟨277901, by decide⟩
    (prefixCache 11 6223) (prefixPartial 11 6223) = false := by
  decide +kernel

theorem node_context_11_6223_277901 : EJMOriginalGlobalDAGData.nodes 10 ⟨277901, by decide⟩ =
    .split (coordinate 11) (![⟨277725, by decide⟩,⟨277784, by decide⟩,⟨277844, by decide⟩,⟨277900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6223_277901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6223 ⟨277901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6223
    ⟨277901, by decide⟩ (by decide) (![⟨277725, by decide⟩,⟨277784, by decide⟩,⟨277844, by decide⟩,⟨277900, by decide⟩]) unmarked_context_11_6223_277901 node_context_11_6223_277901
  intro a
  fin_cases a
  · exact context_12_24892_277725
  · exact context_12_24893_277784
  · exact context_12_24894_277844
  · exact context_12_24895_277900

theorem unmarked_context_10_1555_277902 : frontier 11 ⟨277902, by decide⟩
    (prefixCache 10 1555) (prefixPartial 10 1555) = false := by
  decide +kernel

theorem node_context_10_1555_277902 : EJMOriginalGlobalDAGData.nodes 11 ⟨277902, by decide⟩ =
    .split (coordinate 10) (![⟨277139, by decide⟩,⟨277424, by decide⟩,⟨277667, by decide⟩,⟨277901, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1555_277902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1555 ⟨277902, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1555
    ⟨277902, by decide⟩ (by decide) (![⟨277139, by decide⟩,⟨277424, by decide⟩,⟨277667, by decide⟩,⟨277901, by decide⟩]) unmarked_context_10_1555_277902 node_context_10_1555_277902
  intro a
  fin_cases a
  · exact context_11_6220_277139
  · exact context_11_6221_277424
  · exact context_11_6222_277667
  · exact context_11_6223_277901

theorem unmarked_context_9_388_277903 : frontier 12 ⟨277903, by decide⟩
    (prefixCache 9 388) (prefixPartial 9 388) = false := by
  decide +kernel

theorem node_context_9_388_277903 : EJMOriginalGlobalDAGData.nodes 12 ⟨277903, by decide⟩ =
    .split (coordinate 9) (![⟨274677, by decide⟩,⟨275774, by decide⟩,⟨276885, by decide⟩,⟨277902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_388_277903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 388 ⟨277903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 388
    ⟨277903, by decide⟩ (by decide) (![⟨274677, by decide⟩,⟨275774, by decide⟩,⟨276885, by decide⟩,⟨277902, by decide⟩]) unmarked_context_9_388_277903 node_context_9_388_277903
  intro a
  fin_cases a
  · exact context_10_1552_274677
  · exact context_10_1553_275774
  · exact context_10_1554_276885
  · exact context_10_1555_277902

theorem selected_cut_10181 : selected 9 ⟨277904, by decide⟩
    (prefixPartial 12 24896) = some ⟨12, 1, 0, 277904, 24896, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24896_277904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24896 ⟨277904, by decide⟩ :=
  accepted_of_selected 12 24896 ⟨277904, by decide⟩ ⟨12, 1, 0, 277904, 24896, 1, 65536⟩
    (by decide) selected_cut_10181

theorem selected_cut_10182 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99588) = some ⟨13, 1, 0, 3444, 99588, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99588_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99588 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99588 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99588, 1, 16384⟩
    (by decide) selected_cut_10182

theorem selected_cut_10183 : selected 8 ⟨277958, by decide⟩
    (prefixPartial 13 99589) = some ⟨13, 2, 0, 277958, 99589, 3497, 16384⟩ := by
  decide +kernel

theorem context_13_99589_277958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99589 ⟨277958, by decide⟩ :=
  accepted_of_selected 13 99589 ⟨277958, by decide⟩ ⟨13, 2, 0, 277958, 99589, 3497, 16384⟩
    (by decide) selected_cut_10183

theorem selected_cut_10184 : selected 8 ⟨278061, by decide⟩
    (prefixPartial 13 99590) = some ⟨13, 2, 0, 278061, 99590, 3661, 16384⟩ := by
  decide +kernel

theorem context_13_99590_278061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99590 ⟨278061, by decide⟩ :=
  accepted_of_selected 13 99590 ⟨278061, by decide⟩ ⟨13, 2, 0, 278061, 99590, 3661, 16384⟩
    (by decide) selected_cut_10184

theorem selected_cut_10185 : selected 8 ⟨278089, by decide⟩
    (prefixPartial 13 99591) = some ⟨13, 2, 0, 278089, 99591, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_99591_278089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99591 ⟨278089, by decide⟩ :=
  accepted_of_selected 13 99591 ⟨278089, by decide⟩ ⟨13, 2, 0, 278089, 99591, 1449, 16384⟩
    (by decide) selected_cut_10185

theorem unmarked_context_12_24897_278090 : frontier 9 ⟨278090, by decide⟩
    (prefixCache 12 24897) (prefixPartial 12 24897) = false := by
  decide +kernel

theorem node_context_12_24897_278090 : EJMOriginalGlobalDAGData.nodes 9 ⟨278090, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨277958, by decide⟩,⟨278061, by decide⟩,⟨278089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24897_278090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24897 ⟨278090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24897
    ⟨278090, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨277958, by decide⟩,⟨278061, by decide⟩,⟨278089, by decide⟩]) unmarked_context_12_24897_278090 node_context_12_24897_278090
  intro a
  fin_cases a
  · exact context_13_99588_3444
  · exact context_13_99589_277958
  · exact context_13_99590_278061
  · exact context_13_99591_278089

theorem selected_cut_10186 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99592) = some ⟨13, 1, 0, 3444, 99592, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99592_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99592 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99592 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99592, 1, 16384⟩
    (by decide) selected_cut_10186

theorem selected_cut_10187 : selected 8 ⟨278122, by decide⟩
    (prefixPartial 13 99593) = some ⟨13, 2, 0, 278122, 99593, 3037, 16384⟩ := by
  decide +kernel

theorem context_13_99593_278122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99593 ⟨278122, by decide⟩ :=
  accepted_of_selected 13 99593 ⟨278122, by decide⟩ ⟨13, 2, 0, 278122, 99593, 3037, 16384⟩
    (by decide) selected_cut_10187

theorem selected_cut_10188 : selected 8 ⟨278168, by decide⟩
    (prefixPartial 13 99594) = some ⟨13, 2, 0, 278168, 99594, 2661, 16384⟩ := by
  decide +kernel

theorem context_13_99594_278168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99594 ⟨278168, by decide⟩ :=
  accepted_of_selected 13 99594 ⟨278168, by decide⟩ ⟨13, 2, 0, 278168, 99594, 2661, 16384⟩
    (by decide) selected_cut_10188

theorem selected_cut_10189 : selected 8 ⟨278184, by decide⟩
    (prefixPartial 13 99595) = some ⟨13, 2, 0, 278184, 99595, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_99595_278184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99595 ⟨278184, by decide⟩ :=
  accepted_of_selected 13 99595 ⟨278184, by decide⟩ ⟨13, 2, 0, 278184, 99595, 1201, 16384⟩
    (by decide) selected_cut_10189

theorem unmarked_context_12_24898_278185 : frontier 9 ⟨278185, by decide⟩
    (prefixCache 12 24898) (prefixPartial 12 24898) = false := by
  decide +kernel

theorem node_context_12_24898_278185 : EJMOriginalGlobalDAGData.nodes 9 ⟨278185, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278122, by decide⟩,⟨278168, by decide⟩,⟨278184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24898_278185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24898 ⟨278185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24898
    ⟨278185, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278122, by decide⟩,⟨278168, by decide⟩,⟨278184, by decide⟩]) unmarked_context_12_24898_278185 node_context_12_24898_278185
  intro a
  fin_cases a
  · exact context_13_99592_3444
  · exact context_13_99593_278122
  · exact context_13_99594_278168
  · exact context_13_99595_278184

theorem selected_cut_10190 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99596) = some ⟨13, 1, 0, 3444, 99596, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99596_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99596 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99596 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99596, 1, 16384⟩
    (by decide) selected_cut_10190

theorem selected_cut_10191 : selected 8 ⟨278227, by decide⟩
    (prefixPartial 13 99597) = some ⟨13, 2, 0, 278227, 99597, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_99597_278227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99597 ⟨278227, by decide⟩ :=
  accepted_of_selected 13 99597 ⟨278227, by decide⟩ ⟨13, 2, 0, 278227, 99597, 3033, 16384⟩
    (by decide) selected_cut_10191

theorem selected_cut_10192 : selected 8 ⟨278273, by decide⟩
    (prefixPartial 13 99598) = some ⟨13, 2, 0, 278273, 99598, 2885, 16384⟩ := by
  decide +kernel

theorem context_13_99598_278273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99598 ⟨278273, by decide⟩ :=
  accepted_of_selected 13 99598 ⟨278273, by decide⟩ ⟨13, 2, 0, 278273, 99598, 2885, 16384⟩
    (by decide) selected_cut_10192

theorem selected_cut_10193 : selected 8 ⟨278289, by decide⟩
    (prefixPartial 13 99599) = some ⟨13, 2, 0, 278289, 99599, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_99599_278289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99599 ⟨278289, by decide⟩ :=
  accepted_of_selected 13 99599 ⟨278289, by decide⟩ ⟨13, 2, 0, 278289, 99599, 1265, 16384⟩
    (by decide) selected_cut_10193

theorem unmarked_context_12_24899_278290 : frontier 9 ⟨278290, by decide⟩
    (prefixCache 12 24899) (prefixPartial 12 24899) = false := by
  decide +kernel

theorem node_context_12_24899_278290 : EJMOriginalGlobalDAGData.nodes 9 ⟨278290, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278227, by decide⟩,⟨278273, by decide⟩,⟨278289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24899_278290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24899 ⟨278290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24899
    ⟨278290, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278227, by decide⟩,⟨278273, by decide⟩,⟨278289, by decide⟩]) unmarked_context_12_24899_278290 node_context_12_24899_278290
  intro a
  fin_cases a
  · exact context_13_99596_3444
  · exact context_13_99597_278227
  · exact context_13_99598_278273
  · exact context_13_99599_278289

theorem unmarked_context_11_6224_278291 : frontier 10 ⟨278291, by decide⟩
    (prefixCache 11 6224) (prefixPartial 11 6224) = false := by
  decide +kernel

theorem node_context_11_6224_278291 : EJMOriginalGlobalDAGData.nodes 10 ⟨278291, by decide⟩ =
    .split (coordinate 11) (![⟨277904, by decide⟩,⟨278090, by decide⟩,⟨278185, by decide⟩,⟨278290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6224_278291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6224 ⟨278291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6224
    ⟨278291, by decide⟩ (by decide) (![⟨277904, by decide⟩,⟨278090, by decide⟩,⟨278185, by decide⟩,⟨278290, by decide⟩]) unmarked_context_11_6224_278291 node_context_11_6224_278291
  intro a
  fin_cases a
  · exact context_12_24896_277904
  · exact context_12_24897_278090
  · exact context_12_24898_278185
  · exact context_12_24899_278290

theorem selected_cut_10194 : selected 9 ⟨278346, by decide⟩
    (prefixPartial 12 24900) = some ⟨12, 2, 0, 278346, 24900, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_24900_278346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24900 ⟨278346, by decide⟩ :=
  accepted_of_selected 12 24900 ⟨278346, by decide⟩ ⟨12, 2, 0, 278346, 24900, 3093, 65536⟩
    (by decide) selected_cut_10194

theorem selected_cut_10195 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 24901) = some ⟨12, 1, 0, 126884, 24901, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24901_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24901 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 24901 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 24901, 1, 65536⟩
    (by decide) selected_cut_10195

theorem selected_cut_10196 : selected 9 ⟨278406, by decide⟩
    (prefixPartial 12 24902) = some ⟨12, 2, 0, 278406, 24902, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_24902_278406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24902 ⟨278406, by decide⟩ :=
  accepted_of_selected 12 24902 ⟨278406, by decide⟩ ⟨12, 2, 0, 278406, 24902, 3917, 65536⟩
    (by decide) selected_cut_10196

theorem selected_cut_10197 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99612) = some ⟨13, 1, 0, 3444, 99612, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99612_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99612 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99612 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99612, 1, 16384⟩
    (by decide) selected_cut_10197

theorem selected_cut_10198 : selected 8 ⟨278428, by decide⟩
    (prefixPartial 13 99613) = some ⟨13, 2, 0, 278428, 99613, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_99613_278428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99613 ⟨278428, by decide⟩ :=
  accepted_of_selected 13 99613 ⟨278428, by decide⟩ ⟨13, 2, 0, 278428, 99613, 1809, 16384⟩
    (by decide) selected_cut_10198

theorem selected_cut_10199 : selected 8 ⟨278449, by decide⟩
    (prefixPartial 13 99614) = some ⟨13, 2, 0, 278449, 99614, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_99614_278449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99614 ⟨278449, by decide⟩ :=
  accepted_of_selected 13 99614 ⟨278449, by decide⟩ ⟨13, 2, 0, 278449, 99614, 1745, 16384⟩
    (by decide) selected_cut_10199

theorem selected_cut_10200 : selected 8 ⟨278459, by decide⟩
    (prefixPartial 13 99615) = some ⟨13, 2, 0, 278459, 99615, 857, 16384⟩ := by
  decide +kernel

theorem context_13_99615_278459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99615 ⟨278459, by decide⟩ :=
  accepted_of_selected 13 99615 ⟨278459, by decide⟩ ⟨13, 2, 0, 278459, 99615, 857, 16384⟩
    (by decide) selected_cut_10200

theorem unmarked_context_12_24903_278460 : frontier 9 ⟨278460, by decide⟩
    (prefixCache 12 24903) (prefixPartial 12 24903) = false := by
  decide +kernel

theorem node_context_12_24903_278460 : EJMOriginalGlobalDAGData.nodes 9 ⟨278460, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278428, by decide⟩,⟨278449, by decide⟩,⟨278459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24903_278460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24903 ⟨278460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24903
    ⟨278460, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278428, by decide⟩,⟨278449, by decide⟩,⟨278459, by decide⟩]) unmarked_context_12_24903_278460 node_context_12_24903_278460
  intro a
  fin_cases a
  · exact context_13_99612_3444
  · exact context_13_99613_278428
  · exact context_13_99614_278449
  · exact context_13_99615_278459

theorem unmarked_context_11_6225_278461 : frontier 10 ⟨278461, by decide⟩
    (prefixCache 11 6225) (prefixPartial 11 6225) = false := by
  decide +kernel

theorem node_context_11_6225_278461 : EJMOriginalGlobalDAGData.nodes 10 ⟨278461, by decide⟩ =
    .split (coordinate 11) (![⟨278346, by decide⟩,⟨126884, by decide⟩,⟨278406, by decide⟩,⟨278460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6225_278461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6225 ⟨278461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6225
    ⟨278461, by decide⟩ (by decide) (![⟨278346, by decide⟩,⟨126884, by decide⟩,⟨278406, by decide⟩,⟨278460, by decide⟩]) unmarked_context_11_6225_278461 node_context_11_6225_278461
  intro a
  fin_cases a
  · exact context_12_24900_278346
  · exact context_12_24901_126884
  · exact context_12_24902_278406
  · exact context_12_24903_278460

theorem selected_cut_10201 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99616) = some ⟨13, 1, 0, 3444, 99616, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99616_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99616 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99616 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99616, 1, 16384⟩
    (by decide) selected_cut_10201

theorem selected_cut_10202 : selected 8 ⟨278479, by decide⟩
    (prefixPartial 13 99617) = some ⟨13, 2, 0, 278479, 99617, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_99617_278479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99617 ⟨278479, by decide⟩ :=
  accepted_of_selected 13 99617 ⟨278479, by decide⟩ ⟨13, 2, 0, 278479, 99617, 1493, 16384⟩
    (by decide) selected_cut_10202

theorem selected_cut_10203 : selected 8 ⟨278508, by decide⟩
    (prefixPartial 13 99618) = some ⟨13, 2, 0, 278508, 99618, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_99618_278508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99618 ⟨278508, by decide⟩ :=
  accepted_of_selected 13 99618 ⟨278508, by decide⟩ ⟨13, 2, 0, 278508, 99618, 1945, 16384⟩
    (by decide) selected_cut_10203

theorem selected_cut_10204 : selected 8 ⟨278520, by decide⟩
    (prefixPartial 13 99619) = some ⟨13, 2, 0, 278520, 99619, 753, 16384⟩ := by
  decide +kernel

theorem context_13_99619_278520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99619 ⟨278520, by decide⟩ :=
  accepted_of_selected 13 99619 ⟨278520, by decide⟩ ⟨13, 2, 0, 278520, 99619, 753, 16384⟩
    (by decide) selected_cut_10204

theorem unmarked_context_12_24904_278521 : frontier 9 ⟨278521, by decide⟩
    (prefixCache 12 24904) (prefixPartial 12 24904) = false := by
  decide +kernel

theorem node_context_12_24904_278521 : EJMOriginalGlobalDAGData.nodes 9 ⟨278521, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278479, by decide⟩,⟨278508, by decide⟩,⟨278520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24904_278521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24904 ⟨278521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24904
    ⟨278521, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278479, by decide⟩,⟨278508, by decide⟩,⟨278520, by decide⟩]) unmarked_context_12_24904_278521 node_context_12_24904_278521
  intro a
  fin_cases a
  · exact context_13_99616_3444
  · exact context_13_99617_278479
  · exact context_13_99618_278508
  · exact context_13_99619_278520

theorem selected_cut_10205 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99620) = some ⟨13, 1, 0, 3444, 99620, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99620_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99620 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99620 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99620, 1, 16384⟩
    (by decide) selected_cut_10205

theorem selected_cut_10206 : selected 8 ⟨278540, by decide⟩
    (prefixPartial 13 99621) = some ⟨13, 2, 0, 278540, 99621, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_99621_278540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99621 ⟨278540, by decide⟩ :=
  accepted_of_selected 13 99621 ⟨278540, by decide⟩ ⟨13, 2, 0, 278540, 99621, 2109, 16384⟩
    (by decide) selected_cut_10206

theorem selected_cut_10207 : selected 8 ⟨278586, by decide⟩
    (prefixPartial 13 99622) = some ⟨13, 2, 0, 278586, 99622, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_99622_278586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99622 ⟨278586, by decide⟩ :=
  accepted_of_selected 13 99622 ⟨278586, by decide⟩ ⟨13, 2, 0, 278586, 99622, 2617, 16384⟩
    (by decide) selected_cut_10207

theorem selected_cut_10208 : selected 8 ⟨278601, by decide⟩
    (prefixPartial 13 99623) = some ⟨13, 2, 0, 278601, 99623, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_99623_278601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99623 ⟨278601, by decide⟩ :=
  accepted_of_selected 13 99623 ⟨278601, by decide⟩ ⟨13, 2, 0, 278601, 99623, 1137, 16384⟩
    (by decide) selected_cut_10208

theorem unmarked_context_12_24905_278602 : frontier 9 ⟨278602, by decide⟩
    (prefixCache 12 24905) (prefixPartial 12 24905) = false := by
  decide +kernel

theorem node_context_12_24905_278602 : EJMOriginalGlobalDAGData.nodes 9 ⟨278602, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278540, by decide⟩,⟨278586, by decide⟩,⟨278601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24905_278602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24905 ⟨278602, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24905
    ⟨278602, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278540, by decide⟩,⟨278586, by decide⟩,⟨278601, by decide⟩]) unmarked_context_12_24905_278602 node_context_12_24905_278602
  intro a
  fin_cases a
  · exact context_13_99620_3444
  · exact context_13_99621_278540
  · exact context_13_99622_278586
  · exact context_13_99623_278601

theorem selected_cut_10209 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99624) = some ⟨13, 1, 0, 3444, 99624, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99624_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99624 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99624 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99624, 1, 16384⟩
    (by decide) selected_cut_10209

theorem selected_cut_10210 : selected 8 ⟨278624, by decide⟩
    (prefixPartial 13 99625) = some ⟨13, 2, 0, 278624, 99625, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_99625_278624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99625 ⟨278624, by decide⟩ :=
  accepted_of_selected 13 99625 ⟨278624, by decide⟩ ⟨13, 2, 0, 278624, 99625, 1837, 16384⟩
    (by decide) selected_cut_10210

theorem selected_cut_10211 : selected 8 ⟨278652, by decide⟩
    (prefixPartial 13 99626) = some ⟨13, 2, 0, 278652, 99626, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_99626_278652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99626 ⟨278652, by decide⟩ :=
  accepted_of_selected 13 99626 ⟨278652, by decide⟩ ⟨13, 2, 0, 278652, 99626, 2109, 16384⟩
    (by decide) selected_cut_10211

theorem selected_cut_10212 : selected 8 ⟨278663, by decide⟩
    (prefixPartial 13 99627) = some ⟨13, 2, 0, 278663, 99627, 873, 16384⟩ := by
  decide +kernel

theorem context_13_99627_278663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99627 ⟨278663, by decide⟩ :=
  accepted_of_selected 13 99627 ⟨278663, by decide⟩ ⟨13, 2, 0, 278663, 99627, 873, 16384⟩
    (by decide) selected_cut_10212

theorem unmarked_context_12_24906_278664 : frontier 9 ⟨278664, by decide⟩
    (prefixCache 12 24906) (prefixPartial 12 24906) = false := by
  decide +kernel

theorem node_context_12_24906_278664 : EJMOriginalGlobalDAGData.nodes 9 ⟨278664, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278624, by decide⟩,⟨278652, by decide⟩,⟨278663, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24906_278664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24906 ⟨278664, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24906
    ⟨278664, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278624, by decide⟩,⟨278652, by decide⟩,⟨278663, by decide⟩]) unmarked_context_12_24906_278664 node_context_12_24906_278664
  intro a
  fin_cases a
  · exact context_13_99624_3444
  · exact context_13_99625_278624
  · exact context_13_99626_278652
  · exact context_13_99627_278663

theorem selected_cut_10213 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99628) = some ⟨13, 1, 0, 3444, 99628, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99628_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99628 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99628 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99628, 1, 16384⟩
    (by decide) selected_cut_10213

theorem selected_cut_10214 : selected 8 ⟨278685, by decide⟩
    (prefixPartial 13 99629) = some ⟨13, 2, 0, 278685, 99629, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_99629_278685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99629 ⟨278685, by decide⟩ :=
  accepted_of_selected 13 99629 ⟨278685, by decide⟩ ⟨13, 2, 0, 278685, 99629, 2013, 16384⟩
    (by decide) selected_cut_10214

theorem selected_cut_10215 : selected 8 ⟨278710, by decide⟩
    (prefixPartial 13 99630) = some ⟨13, 2, 0, 278710, 99630, 2265, 16384⟩ := by
  decide +kernel

theorem context_13_99630_278710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99630 ⟨278710, by decide⟩ :=
  accepted_of_selected 13 99630 ⟨278710, by decide⟩ ⟨13, 2, 0, 278710, 99630, 2265, 16384⟩
    (by decide) selected_cut_10215

theorem selected_cut_10216 : selected 8 ⟨278721, by decide⟩
    (prefixPartial 13 99631) = some ⟨13, 2, 0, 278721, 99631, 969, 16384⟩ := by
  decide +kernel

theorem context_13_99631_278721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99631 ⟨278721, by decide⟩ :=
  accepted_of_selected 13 99631 ⟨278721, by decide⟩ ⟨13, 2, 0, 278721, 99631, 969, 16384⟩
    (by decide) selected_cut_10216

theorem unmarked_context_12_24907_278722 : frontier 9 ⟨278722, by decide⟩
    (prefixCache 12 24907) (prefixPartial 12 24907) = false := by
  decide +kernel

theorem node_context_12_24907_278722 : EJMOriginalGlobalDAGData.nodes 9 ⟨278722, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278685, by decide⟩,⟨278710, by decide⟩,⟨278721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24907_278722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24907 ⟨278722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24907
    ⟨278722, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278685, by decide⟩,⟨278710, by decide⟩,⟨278721, by decide⟩]) unmarked_context_12_24907_278722 node_context_12_24907_278722
  intro a
  fin_cases a
  · exact context_13_99628_3444
  · exact context_13_99629_278685
  · exact context_13_99630_278710
  · exact context_13_99631_278721

theorem unmarked_context_11_6226_278723 : frontier 10 ⟨278723, by decide⟩
    (prefixCache 11 6226) (prefixPartial 11 6226) = false := by
  decide +kernel

theorem node_context_11_6226_278723 : EJMOriginalGlobalDAGData.nodes 10 ⟨278723, by decide⟩ =
    .split (coordinate 11) (![⟨278521, by decide⟩,⟨278602, by decide⟩,⟨278664, by decide⟩,⟨278722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6226_278723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6226 ⟨278723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6226
    ⟨278723, by decide⟩ (by decide) (![⟨278521, by decide⟩,⟨278602, by decide⟩,⟨278664, by decide⟩,⟨278722, by decide⟩]) unmarked_context_11_6226_278723 node_context_11_6226_278723
  intro a
  fin_cases a
  · exact context_12_24904_278521
  · exact context_12_24905_278602
  · exact context_12_24906_278664
  · exact context_12_24907_278722

theorem selected_cut_10217 : selected 9 ⟨278773, by decide⟩
    (prefixPartial 12 24908) = some ⟨12, 2, 0, 278773, 24908, 3961, 65536⟩ := by
  decide +kernel

theorem context_12_24908_278773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24908 ⟨278773, by decide⟩ :=
  accepted_of_selected 12 24908 ⟨278773, by decide⟩ ⟨12, 2, 0, 278773, 24908, 3961, 65536⟩
    (by decide) selected_cut_10217

theorem selected_cut_10218 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99636) = some ⟨13, 1, 0, 3444, 99636, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99636_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99636 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99636 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99636, 1, 16384⟩
    (by decide) selected_cut_10218

theorem selected_cut_10219 : selected 8 ⟨278797, by decide⟩
    (prefixPartial 13 99637) = some ⟨13, 2, 0, 278797, 99637, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_99637_278797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99637 ⟨278797, by decide⟩ :=
  accepted_of_selected 13 99637 ⟨278797, by decide⟩ ⟨13, 2, 0, 278797, 99637, 2129, 16384⟩
    (by decide) selected_cut_10219

theorem selected_cut_10220 : selected 8 ⟨278830, by decide⟩
    (prefixPartial 13 99638) = some ⟨13, 2, 0, 278830, 99638, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_99638_278830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99638 ⟨278830, by decide⟩ :=
  accepted_of_selected 13 99638 ⟨278830, by decide⟩ ⟨13, 2, 0, 278830, 99638, 2437, 16384⟩
    (by decide) selected_cut_10220

theorem selected_cut_10221 : selected 8 ⟨278845, by decide⟩
    (prefixPartial 13 99639) = some ⟨13, 2, 0, 278845, 99639, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_99639_278845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99639 ⟨278845, by decide⟩ :=
  accepted_of_selected 13 99639 ⟨278845, by decide⟩ ⟨13, 2, 0, 278845, 99639, 1169, 16384⟩
    (by decide) selected_cut_10221

theorem unmarked_context_12_24909_278846 : frontier 9 ⟨278846, by decide⟩
    (prefixCache 12 24909) (prefixPartial 12 24909) = false := by
  decide +kernel

theorem node_context_12_24909_278846 : EJMOriginalGlobalDAGData.nodes 9 ⟨278846, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278797, by decide⟩,⟨278830, by decide⟩,⟨278845, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24909_278846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24909 ⟨278846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24909
    ⟨278846, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278797, by decide⟩,⟨278830, by decide⟩,⟨278845, by decide⟩]) unmarked_context_12_24909_278846 node_context_12_24909_278846
  intro a
  fin_cases a
  · exact context_13_99636_3444
  · exact context_13_99637_278797
  · exact context_13_99638_278830
  · exact context_13_99639_278845

theorem selected_cut_10222 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99640) = some ⟨13, 1, 0, 3444, 99640, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99640_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99640 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99640 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99640, 1, 16384⟩
    (by decide) selected_cut_10222

theorem selected_cut_10223 : selected 8 ⟨278868, by decide⟩
    (prefixPartial 13 99641) = some ⟨13, 2, 0, 278868, 99641, 1773, 16384⟩ := by
  decide +kernel

theorem context_13_99641_278868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99641 ⟨278868, by decide⟩ :=
  accepted_of_selected 13 99641 ⟨278868, by decide⟩ ⟨13, 2, 0, 278868, 99641, 1773, 16384⟩
    (by decide) selected_cut_10223

theorem selected_cut_10224 : selected 8 ⟨278892, by decide⟩
    (prefixPartial 13 99642) = some ⟨13, 2, 0, 278892, 99642, 1829, 16384⟩ := by
  decide +kernel

theorem context_13_99642_278892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99642 ⟨278892, by decide⟩ :=
  accepted_of_selected 13 99642 ⟨278892, by decide⟩ ⟨13, 2, 0, 278892, 99642, 1829, 16384⟩
    (by decide) selected_cut_10224

theorem selected_cut_10225 : selected 8 ⟨278899, by decide⟩
    (prefixPartial 13 99643) = some ⟨13, 2, 0, 278899, 99643, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_99643_278899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99643 ⟨278899, by decide⟩ :=
  accepted_of_selected 13 99643 ⟨278899, by decide⟩ ⟨13, 2, 0, 278899, 99643, 1033, 16384⟩
    (by decide) selected_cut_10225

theorem unmarked_context_12_24910_278900 : frontier 9 ⟨278900, by decide⟩
    (prefixCache 12 24910) (prefixPartial 12 24910) = false := by
  decide +kernel

theorem node_context_12_24910_278900 : EJMOriginalGlobalDAGData.nodes 9 ⟨278900, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278868, by decide⟩,⟨278892, by decide⟩,⟨278899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24910_278900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24910 ⟨278900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24910
    ⟨278900, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278868, by decide⟩,⟨278892, by decide⟩,⟨278899, by decide⟩]) unmarked_context_12_24910_278900 node_context_12_24910_278900
  intro a
  fin_cases a
  · exact context_13_99640_3444
  · exact context_13_99641_278868
  · exact context_13_99642_278892
  · exact context_13_99643_278899

theorem selected_cut_10226 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99644) = some ⟨13, 1, 0, 3444, 99644, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99644_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99644 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99644 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99644, 1, 16384⟩
    (by decide) selected_cut_10226

theorem selected_cut_10227 : selected 8 ⟨278919, by decide⟩
    (prefixPartial 13 99645) = some ⟨13, 2, 0, 278919, 99645, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_99645_278919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99645 ⟨278919, by decide⟩ :=
  accepted_of_selected 13 99645 ⟨278919, by decide⟩ ⟨13, 2, 0, 278919, 99645, 1705, 16384⟩
    (by decide) selected_cut_10227

theorem selected_cut_10228 : selected 8 ⟨278942, by decide⟩
    (prefixPartial 13 99646) = some ⟨13, 2, 0, 278942, 99646, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_99646_278942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99646 ⟨278942, by decide⟩ :=
  accepted_of_selected 13 99646 ⟨278942, by decide⟩ ⟨13, 2, 0, 278942, 99646, 1997, 16384⟩
    (by decide) selected_cut_10228

theorem selected_cut_10229 : selected 8 ⟨278950, by decide⟩
    (prefixPartial 13 99647) = some ⟨13, 2, 0, 278950, 99647, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_99647_278950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99647 ⟨278950, by decide⟩ :=
  accepted_of_selected 13 99647 ⟨278950, by decide⟩ ⟨13, 2, 0, 278950, 99647, 1153, 16384⟩
    (by decide) selected_cut_10229

theorem unmarked_context_12_24911_278951 : frontier 9 ⟨278951, by decide⟩
    (prefixCache 12 24911) (prefixPartial 12 24911) = false := by
  decide +kernel

theorem node_context_12_24911_278951 : EJMOriginalGlobalDAGData.nodes 9 ⟨278951, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨278919, by decide⟩,⟨278942, by decide⟩,⟨278950, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24911_278951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24911 ⟨278951, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24911
    ⟨278951, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨278919, by decide⟩,⟨278942, by decide⟩,⟨278950, by decide⟩]) unmarked_context_12_24911_278951 node_context_12_24911_278951
  intro a
  fin_cases a
  · exact context_13_99644_3444
  · exact context_13_99645_278919
  · exact context_13_99646_278942
  · exact context_13_99647_278950

theorem unmarked_context_11_6227_278952 : frontier 10 ⟨278952, by decide⟩
    (prefixCache 11 6227) (prefixPartial 11 6227) = false := by
  decide +kernel

theorem node_context_11_6227_278952 : EJMOriginalGlobalDAGData.nodes 10 ⟨278952, by decide⟩ =
    .split (coordinate 11) (![⟨278773, by decide⟩,⟨278846, by decide⟩,⟨278900, by decide⟩,⟨278951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6227_278952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6227 ⟨278952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6227
    ⟨278952, by decide⟩ (by decide) (![⟨278773, by decide⟩,⟨278846, by decide⟩,⟨278900, by decide⟩,⟨278951, by decide⟩]) unmarked_context_11_6227_278952 node_context_11_6227_278952
  intro a
  fin_cases a
  · exact context_12_24908_278773
  · exact context_12_24909_278846
  · exact context_12_24910_278900
  · exact context_12_24911_278951

theorem unmarked_context_10_1556_278953 : frontier 11 ⟨278953, by decide⟩
    (prefixCache 10 1556) (prefixPartial 10 1556) = false := by
  decide +kernel

theorem node_context_10_1556_278953 : EJMOriginalGlobalDAGData.nodes 11 ⟨278953, by decide⟩ =
    .split (coordinate 10) (![⟨278291, by decide⟩,⟨278461, by decide⟩,⟨278723, by decide⟩,⟨278952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1556_278953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1556 ⟨278953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1556
    ⟨278953, by decide⟩ (by decide) (![⟨278291, by decide⟩,⟨278461, by decide⟩,⟨278723, by decide⟩,⟨278952, by decide⟩]) unmarked_context_10_1556_278953 node_context_10_1556_278953
  intro a
  fin_cases a
  · exact context_11_6224_278291
  · exact context_11_6225_278461
  · exact context_11_6226_278723
  · exact context_11_6227_278952

theorem selected_cut_10230 : selected 9 ⟨278994, by decide⟩
    (prefixPartial 12 24912) = some ⟨12, 2, 0, 278994, 24912, 3417, 65536⟩ := by
  decide +kernel

theorem context_12_24912_278994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24912 ⟨278994, by decide⟩ :=
  accepted_of_selected 12 24912 ⟨278994, by decide⟩ ⟨12, 2, 0, 278994, 24912, 3417, 65536⟩
    (by decide) selected_cut_10230

theorem selected_cut_10231 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 24913) = some ⟨12, 1, 0, 170504, 24913, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24913_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24913 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 24913 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 24913, 1, 65536⟩
    (by decide) selected_cut_10231

theorem selected_cut_10232 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99656) = some ⟨13, 1, 0, 3444, 99656, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99656_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99656 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99656 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99656, 1, 16384⟩
    (by decide) selected_cut_10232

theorem selected_cut_10233 : selected 8 ⟨279012, by decide⟩
    (prefixPartial 13 99657) = some ⟨13, 2, 0, 279012, 99657, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_99657_279012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99657 ⟨279012, by decide⟩ :=
  accepted_of_selected 13 99657 ⟨279012, by decide⟩ ⟨13, 2, 0, 279012, 99657, 1585, 16384⟩
    (by decide) selected_cut_10233

theorem selected_cut_10234 : selected 8 ⟨279034, by decide⟩
    (prefixPartial 13 99658) = some ⟨13, 2, 0, 279034, 99658, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_99658_279034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99658 ⟨279034, by decide⟩ :=
  accepted_of_selected 13 99658 ⟨279034, by decide⟩ ⟨13, 2, 0, 279034, 99658, 1761, 16384⟩
    (by decide) selected_cut_10234

theorem selected_cut_10235 : selected 8 ⟨279041, by decide⟩
    (prefixPartial 13 99659) = some ⟨13, 2, 0, 279041, 99659, 929, 16384⟩ := by
  decide +kernel

theorem context_13_99659_279041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99659 ⟨279041, by decide⟩ :=
  accepted_of_selected 13 99659 ⟨279041, by decide⟩ ⟨13, 2, 0, 279041, 99659, 929, 16384⟩
    (by decide) selected_cut_10235

theorem unmarked_context_12_24914_279042 : frontier 9 ⟨279042, by decide⟩
    (prefixCache 12 24914) (prefixPartial 12 24914) = false := by
  decide +kernel

theorem node_context_12_24914_279042 : EJMOriginalGlobalDAGData.nodes 9 ⟨279042, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨279012, by decide⟩,⟨279034, by decide⟩,⟨279041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24914_279042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24914 ⟨279042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24914
    ⟨279042, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨279012, by decide⟩,⟨279034, by decide⟩,⟨279041, by decide⟩]) unmarked_context_12_24914_279042 node_context_12_24914_279042
  intro a
  fin_cases a
  · exact context_13_99656_3444
  · exact context_13_99657_279012
  · exact context_13_99658_279034
  · exact context_13_99659_279041

theorem selected_cut_10236 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99660) = some ⟨13, 1, 0, 3444, 99660, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99660_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99660 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99660 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99660, 1, 16384⟩
    (by decide) selected_cut_10236

theorem selected_cut_10237 : selected 8 ⟨279057, by decide⟩
    (prefixPartial 13 99661) = some ⟨13, 2, 0, 279057, 99661, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_99661_279057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99661 ⟨279057, by decide⟩ :=
  accepted_of_selected 13 99661 ⟨279057, by decide⟩ ⟨13, 2, 0, 279057, 99661, 1577, 16384⟩
    (by decide) selected_cut_10237

theorem selected_cut_10238 : selected 8 ⟨279081, by decide⟩
    (prefixPartial 13 99662) = some ⟨13, 2, 0, 279081, 99662, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_99662_279081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99662 ⟨279081, by decide⟩ :=
  accepted_of_selected 13 99662 ⟨279081, by decide⟩ ⟨13, 2, 0, 279081, 99662, 2029, 16384⟩
    (by decide) selected_cut_10238

theorem selected_cut_10239 : selected 8 ⟨279088, by decide⟩
    (prefixPartial 13 99663) = some ⟨13, 2, 0, 279088, 99663, 853, 16384⟩ := by
  decide +kernel

theorem context_13_99663_279088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99663 ⟨279088, by decide⟩ :=
  accepted_of_selected 13 99663 ⟨279088, by decide⟩ ⟨13, 2, 0, 279088, 99663, 853, 16384⟩
    (by decide) selected_cut_10239

theorem unmarked_context_12_24915_279089 : frontier 9 ⟨279089, by decide⟩
    (prefixCache 12 24915) (prefixPartial 12 24915) = false := by
  decide +kernel

theorem node_context_12_24915_279089 : EJMOriginalGlobalDAGData.nodes 9 ⟨279089, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨279057, by decide⟩,⟨279081, by decide⟩,⟨279088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24915_279089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24915 ⟨279089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24915
    ⟨279089, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨279057, by decide⟩,⟨279081, by decide⟩,⟨279088, by decide⟩]) unmarked_context_12_24915_279089 node_context_12_24915_279089
  intro a
  fin_cases a
  · exact context_13_99660_3444
  · exact context_13_99661_279057
  · exact context_13_99662_279081
  · exact context_13_99663_279088

theorem unmarked_context_11_6228_279090 : frontier 10 ⟨279090, by decide⟩
    (prefixCache 11 6228) (prefixPartial 11 6228) = false := by
  decide +kernel

theorem node_context_11_6228_279090 : EJMOriginalGlobalDAGData.nodes 10 ⟨279090, by decide⟩ =
    .split (coordinate 11) (![⟨278994, by decide⟩,⟨170504, by decide⟩,⟨279042, by decide⟩,⟨279089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6228_279090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6228 ⟨279090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6228
    ⟨279090, by decide⟩ (by decide) (![⟨278994, by decide⟩,⟨170504, by decide⟩,⟨279042, by decide⟩,⟨279089, by decide⟩]) unmarked_context_11_6228_279090 node_context_11_6228_279090
  intro a
  fin_cases a
  · exact context_12_24912_278994
  · exact context_12_24913_170504
  · exact context_12_24914_279042
  · exact context_12_24915_279089

theorem selected_cut_10240 : selected 9 ⟨279133, by decide⟩
    (prefixPartial 12 24916) = some ⟨12, 2, 0, 279133, 24916, 2941, 65536⟩ := by
  decide +kernel

theorem context_12_24916_279133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24916 ⟨279133, by decide⟩ :=
  accepted_of_selected 12 24916 ⟨279133, by decide⟩ ⟨12, 2, 0, 279133, 24916, 2941, 65536⟩
    (by decide) selected_cut_10240

theorem selected_cut_10241 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 24917) = some ⟨12, 1, 0, 170504, 24917, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24917_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24917 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 24917 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 24917, 1, 65536⟩
    (by decide) selected_cut_10241

theorem selected_cut_10242 : selected 9 ⟨279181, by decide⟩
    (prefixPartial 12 24918) = some ⟨12, 2, 0, 279181, 24918, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_24918_279181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24918 ⟨279181, by decide⟩ :=
  accepted_of_selected 12 24918 ⟨279181, by decide⟩ ⟨12, 2, 0, 279181, 24918, 3633, 65536⟩
    (by decide) selected_cut_10242

theorem selected_cut_10243 : selected 9 ⟨279227, by decide⟩
    (prefixPartial 12 24919) = some ⟨12, 2, 0, 279227, 24919, 4029, 65536⟩ := by
  decide +kernel

theorem context_12_24919_279227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24919 ⟨279227, by decide⟩ :=
  accepted_of_selected 12 24919 ⟨279227, by decide⟩ ⟨12, 2, 0, 279227, 24919, 4029, 65536⟩
    (by decide) selected_cut_10243

theorem unmarked_context_11_6229_279228 : frontier 10 ⟨279228, by decide⟩
    (prefixCache 11 6229) (prefixPartial 11 6229) = false := by
  decide +kernel

theorem node_context_11_6229_279228 : EJMOriginalGlobalDAGData.nodes 10 ⟨279228, by decide⟩ =
    .split (coordinate 11) (![⟨279133, by decide⟩,⟨170504, by decide⟩,⟨279181, by decide⟩,⟨279227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6229_279228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6229 ⟨279228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6229
    ⟨279228, by decide⟩ (by decide) (![⟨279133, by decide⟩,⟨170504, by decide⟩,⟨279181, by decide⟩,⟨279227, by decide⟩]) unmarked_context_11_6229_279228 node_context_11_6229_279228
  intro a
  fin_cases a
  · exact context_12_24916_279133
  · exact context_12_24917_170504
  · exact context_12_24918_279181
  · exact context_12_24919_279227

theorem selected_cut_10244 : selected 9 ⟨279271, by decide⟩
    (prefixPartial 12 24920) = some ⟨12, 2, 0, 279271, 24920, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_24920_279271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24920 ⟨279271, by decide⟩ :=
  accepted_of_selected 12 24920 ⟨279271, by decide⟩ ⟨12, 2, 0, 279271, 24920, 3481, 65536⟩
    (by decide) selected_cut_10244

theorem selected_cut_10245 : selected 9 ⟨279341, by decide⟩
    (prefixPartial 12 24921) = some ⟨12, 2, 0, 279341, 24921, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_24921_279341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24921 ⟨279341, by decide⟩ :=
  accepted_of_selected 12 24921 ⟨279341, by decide⟩ ⟨12, 2, 0, 279341, 24921, 1997, 65536⟩
    (by decide) selected_cut_10245

theorem selected_cut_10246 : selected 9 ⟨279388, by decide⟩
    (prefixPartial 12 24922) = some ⟨12, 2, 0, 279388, 24922, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_24922_279388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24922 ⟨279388, by decide⟩ :=
  accepted_of_selected 12 24922 ⟨279388, by decide⟩ ⟨12, 2, 0, 279388, 24922, 3941, 65536⟩
    (by decide) selected_cut_10246

theorem selected_cut_10247 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99692) = some ⟨13, 1, 0, 3444, 99692, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99692_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99692 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99692 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99692, 1, 16384⟩
    (by decide) selected_cut_10247

theorem selected_cut_10248 : selected 8 ⟨279402, by decide⟩
    (prefixPartial 13 99693) = some ⟨13, 2, 0, 279402, 99693, 1357, 16384⟩ := by
  decide +kernel

theorem context_13_99693_279402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99693 ⟨279402, by decide⟩ :=
  accepted_of_selected 13 99693 ⟨279402, by decide⟩ ⟨13, 2, 0, 279402, 99693, 1357, 16384⟩
    (by decide) selected_cut_10248

theorem selected_cut_10249 : selected 8 ⟨279420, by decide⟩
    (prefixPartial 13 99694) = some ⟨13, 2, 0, 279420, 99694, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_99694_279420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99694 ⟨279420, by decide⟩ :=
  accepted_of_selected 13 99694 ⟨279420, by decide⟩ ⟨13, 2, 0, 279420, 99694, 1965, 16384⟩
    (by decide) selected_cut_10249

theorem selected_cut_10250 : selected 8 ⟨279430, by decide⟩
    (prefixPartial 13 99695) = some ⟨13, 2, 0, 279430, 99695, 845, 16384⟩ := by
  decide +kernel

theorem context_13_99695_279430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99695 ⟨279430, by decide⟩ :=
  accepted_of_selected 13 99695 ⟨279430, by decide⟩ ⟨13, 2, 0, 279430, 99695, 845, 16384⟩
    (by decide) selected_cut_10250

theorem unmarked_context_12_24923_279431 : frontier 9 ⟨279431, by decide⟩
    (prefixCache 12 24923) (prefixPartial 12 24923) = false := by
  decide +kernel

theorem node_context_12_24923_279431 : EJMOriginalGlobalDAGData.nodes 9 ⟨279431, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨279402, by decide⟩,⟨279420, by decide⟩,⟨279430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24923_279431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24923 ⟨279431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24923
    ⟨279431, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨279402, by decide⟩,⟨279420, by decide⟩,⟨279430, by decide⟩]) unmarked_context_12_24923_279431 node_context_12_24923_279431
  intro a
  fin_cases a
  · exact context_13_99692_3444
  · exact context_13_99693_279402
  · exact context_13_99694_279420
  · exact context_13_99695_279430

theorem unmarked_context_11_6230_279432 : frontier 10 ⟨279432, by decide⟩
    (prefixCache 11 6230) (prefixPartial 11 6230) = false := by
  decide +kernel

theorem node_context_11_6230_279432 : EJMOriginalGlobalDAGData.nodes 10 ⟨279432, by decide⟩ =
    .split (coordinate 11) (![⟨279271, by decide⟩,⟨279341, by decide⟩,⟨279388, by decide⟩,⟨279431, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6230_279432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6230 ⟨279432, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6230
    ⟨279432, by decide⟩ (by decide) (![⟨279271, by decide⟩,⟨279341, by decide⟩,⟨279388, by decide⟩,⟨279431, by decide⟩]) unmarked_context_11_6230_279432 node_context_11_6230_279432
  intro a
  fin_cases a
  · exact context_12_24920_279271
  · exact context_12_24921_279341
  · exact context_12_24922_279388
  · exact context_12_24923_279431

theorem selected_cut_10251 : selected 9 ⟨279472, by decide⟩
    (prefixPartial 12 24924) = some ⟨12, 2, 0, 279472, 24924, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_24924_279472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24924 ⟨279472, by decide⟩ :=
  accepted_of_selected 12 24924 ⟨279472, by decide⟩ ⟨12, 2, 0, 279472, 24924, 3445, 65536⟩
    (by decide) selected_cut_10251

theorem selected_cut_10252 : selected 9 ⟨279524, by decide⟩
    (prefixPartial 12 24925) = some ⟨12, 2, 0, 279524, 24925, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_24925_279524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24925 ⟨279524, by decide⟩ :=
  accepted_of_selected 12 24925 ⟨279524, by decide⟩ ⟨12, 2, 0, 279524, 24925, 2113, 65536⟩
    (by decide) selected_cut_10252

theorem selected_cut_10253 : selected 9 ⟨279567, by decide⟩
    (prefixPartial 12 24926) = some ⟨12, 2, 0, 279567, 24926, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_24926_279567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24926 ⟨279567, by decide⟩ :=
  accepted_of_selected 12 24926 ⟨279567, by decide⟩ ⟨12, 2, 0, 279567, 24926, 3893, 65536⟩
    (by decide) selected_cut_10253

theorem selected_cut_10254 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99708) = some ⟨13, 1, 0, 3444, 99708, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99708_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99708 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99708 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99708, 1, 16384⟩
    (by decide) selected_cut_10254

theorem selected_cut_10255 : selected 8 ⟨279581, by decide⟩
    (prefixPartial 13 99709) = some ⟨13, 2, 0, 279581, 99709, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_99709_279581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99709 ⟨279581, by decide⟩ :=
  accepted_of_selected 13 99709 ⟨279581, by decide⟩ ⟨13, 2, 0, 279581, 99709, 1285, 16384⟩
    (by decide) selected_cut_10255

theorem selected_cut_10256 : selected 8 ⟨279600, by decide⟩
    (prefixPartial 13 99710) = some ⟨13, 2, 0, 279600, 99710, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_99710_279600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99710 ⟨279600, by decide⟩ :=
  accepted_of_selected 13 99710 ⟨279600, by decide⟩ ⟨13, 2, 0, 279600, 99710, 1877, 16384⟩
    (by decide) selected_cut_10256

theorem selected_cut_10257 : selected 8 ⟨279607, by decide⟩
    (prefixPartial 13 99711) = some ⟨13, 2, 0, 279607, 99711, 941, 16384⟩ := by
  decide +kernel

theorem context_13_99711_279607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99711 ⟨279607, by decide⟩ :=
  accepted_of_selected 13 99711 ⟨279607, by decide⟩ ⟨13, 2, 0, 279607, 99711, 941, 16384⟩
    (by decide) selected_cut_10257

theorem unmarked_context_12_24927_279608 : frontier 9 ⟨279608, by decide⟩
    (prefixCache 12 24927) (prefixPartial 12 24927) = false := by
  decide +kernel

theorem node_context_12_24927_279608 : EJMOriginalGlobalDAGData.nodes 9 ⟨279608, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨279581, by decide⟩,⟨279600, by decide⟩,⟨279607, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24927_279608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24927 ⟨279608, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24927
    ⟨279608, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨279581, by decide⟩,⟨279600, by decide⟩,⟨279607, by decide⟩]) unmarked_context_12_24927_279608 node_context_12_24927_279608
  intro a
  fin_cases a
  · exact context_13_99708_3444
  · exact context_13_99709_279581
  · exact context_13_99710_279600
  · exact context_13_99711_279607

theorem unmarked_context_11_6231_279609 : frontier 10 ⟨279609, by decide⟩
    (prefixCache 11 6231) (prefixPartial 11 6231) = false := by
  decide +kernel

theorem node_context_11_6231_279609 : EJMOriginalGlobalDAGData.nodes 10 ⟨279609, by decide⟩ =
    .split (coordinate 11) (![⟨279472, by decide⟩,⟨279524, by decide⟩,⟨279567, by decide⟩,⟨279608, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6231_279609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6231 ⟨279609, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6231
    ⟨279609, by decide⟩ (by decide) (![⟨279472, by decide⟩,⟨279524, by decide⟩,⟨279567, by decide⟩,⟨279608, by decide⟩]) unmarked_context_11_6231_279609 node_context_11_6231_279609
  intro a
  fin_cases a
  · exact context_12_24924_279472
  · exact context_12_24925_279524
  · exact context_12_24926_279567
  · exact context_12_24927_279608

theorem unmarked_context_10_1557_279610 : frontier 11 ⟨279610, by decide⟩
    (prefixCache 10 1557) (prefixPartial 10 1557) = false := by
  decide +kernel

theorem node_context_10_1557_279610 : EJMOriginalGlobalDAGData.nodes 11 ⟨279610, by decide⟩ =
    .split (coordinate 10) (![⟨279090, by decide⟩,⟨279228, by decide⟩,⟨279432, by decide⟩,⟨279609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1557_279610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1557 ⟨279610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1557
    ⟨279610, by decide⟩ (by decide) (![⟨279090, by decide⟩,⟨279228, by decide⟩,⟨279432, by decide⟩,⟨279609, by decide⟩]) unmarked_context_10_1557_279610 node_context_10_1557_279610
  intro a
  fin_cases a
  · exact context_11_6228_279090
  · exact context_11_6229_279228
  · exact context_11_6230_279432
  · exact context_11_6231_279609

theorem selected_cut_10258 : selected 9 ⟨279648, by decide⟩
    (prefixPartial 12 24928) = some ⟨12, 2, 0, 279648, 24928, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_24928_279648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24928 ⟨279648, by decide⟩ :=
  accepted_of_selected 12 24928 ⟨279648, by decide⟩ ⟨12, 2, 0, 279648, 24928, 3529, 65536⟩
    (by decide) selected_cut_10258

theorem selected_cut_10259 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99716) = some ⟨13, 1, 0, 3444, 99716, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99716_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99716 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99716 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99716, 1, 16384⟩
    (by decide) selected_cut_10259

theorem selected_cut_10260 : selected 8 ⟨279662, by decide⟩
    (prefixPartial 13 99717) = some ⟨13, 2, 0, 279662, 99717, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_99717_279662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99717 ⟨279662, by decide⟩ :=
  accepted_of_selected 13 99717 ⟨279662, by decide⟩ ⟨13, 2, 0, 279662, 99717, 1553, 16384⟩
    (by decide) selected_cut_10260

theorem selected_cut_10261 : selected 8 ⟨279697, by decide⟩
    (prefixPartial 13 99718) = some ⟨13, 2, 0, 279697, 99718, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_99718_279697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99718 ⟨279697, by decide⟩ :=
  accepted_of_selected 13 99718 ⟨279697, by decide⟩ ⟨13, 2, 0, 279697, 99718, 2385, 16384⟩
    (by decide) selected_cut_10261

theorem selected_cut_10262 : selected 8 ⟨279709, by decide⟩
    (prefixPartial 13 99719) = some ⟨13, 2, 0, 279709, 99719, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_99719_279709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99719 ⟨279709, by decide⟩ :=
  accepted_of_selected 13 99719 ⟨279709, by decide⟩ ⟨13, 2, 0, 279709, 99719, 1225, 16384⟩
    (by decide) selected_cut_10262

theorem unmarked_context_12_24929_279710 : frontier 9 ⟨279710, by decide⟩
    (prefixCache 12 24929) (prefixPartial 12 24929) = false := by
  decide +kernel

theorem node_context_12_24929_279710 : EJMOriginalGlobalDAGData.nodes 9 ⟨279710, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨279662, by decide⟩,⟨279697, by decide⟩,⟨279709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24929_279710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24929 ⟨279710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24929
    ⟨279710, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨279662, by decide⟩,⟨279697, by decide⟩,⟨279709, by decide⟩]) unmarked_context_12_24929_279710 node_context_12_24929_279710
  intro a
  fin_cases a
  · exact context_13_99716_3444
  · exact context_13_99717_279662
  · exact context_13_99718_279697
  · exact context_13_99719_279709

theorem selected_cut_10263 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99720) = some ⟨13, 1, 0, 3444, 99720, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99720_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99720 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99720 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99720, 1, 16384⟩
    (by decide) selected_cut_10263

theorem selected_cut_10264 : selected 8 ⟨279731, by decide⟩
    (prefixPartial 13 99721) = some ⟨13, 2, 0, 279731, 99721, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_99721_279731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99721 ⟨279731, by decide⟩ :=
  accepted_of_selected 13 99721 ⟨279731, by decide⟩ ⟨13, 2, 0, 279731, 99721, 1457, 16384⟩
    (by decide) selected_cut_10264

theorem selected_cut_10265 : selected 8 ⟨279762, by decide⟩
    (prefixPartial 13 99722) = some ⟨13, 2, 0, 279762, 99722, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_99722_279762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99722 ⟨279762, by decide⟩ :=
  accepted_of_selected 13 99722 ⟨279762, by decide⟩ ⟨13, 2, 0, 279762, 99722, 1893, 16384⟩
    (by decide) selected_cut_10265

theorem selected_cut_10266 : selected 8 ⟨279774, by decide⟩
    (prefixPartial 13 99723) = some ⟨13, 2, 0, 279774, 99723, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_99723_279774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99723 ⟨279774, by decide⟩ :=
  accepted_of_selected 13 99723 ⟨279774, by decide⟩ ⟨13, 2, 0, 279774, 99723, 1077, 16384⟩
    (by decide) selected_cut_10266

theorem unmarked_context_12_24930_279775 : frontier 9 ⟨279775, by decide⟩
    (prefixCache 12 24930) (prefixPartial 12 24930) = false := by
  decide +kernel

theorem node_context_12_24930_279775 : EJMOriginalGlobalDAGData.nodes 9 ⟨279775, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨279731, by decide⟩,⟨279762, by decide⟩,⟨279774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24930_279775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24930 ⟨279775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24930
    ⟨279775, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨279731, by decide⟩,⟨279762, by decide⟩,⟨279774, by decide⟩]) unmarked_context_12_24930_279775 node_context_12_24930_279775
  intro a
  fin_cases a
  · exact context_13_99720_3444
  · exact context_13_99721_279731
  · exact context_13_99722_279762
  · exact context_13_99723_279774

theorem selected_cut_10267 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99724) = some ⟨13, 1, 0, 3444, 99724, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99724_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99724 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99724 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99724, 1, 16384⟩
    (by decide) selected_cut_10267

theorem selected_cut_10268 : selected 8 ⟨279789, by decide⟩
    (prefixPartial 13 99725) = some ⟨13, 2, 0, 279789, 99725, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_99725_279789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99725 ⟨279789, by decide⟩ :=
  accepted_of_selected 13 99725 ⟨279789, by decide⟩ ⟨13, 2, 0, 279789, 99725, 1477, 16384⟩
    (by decide) selected_cut_10268

theorem selected_cut_10269 : selected 8 ⟨279823, by decide⟩
    (prefixPartial 13 99726) = some ⟨13, 2, 0, 279823, 99726, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_99726_279823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99726 ⟨279823, by decide⟩ :=
  accepted_of_selected 13 99726 ⟨279823, by decide⟩ ⟨13, 2, 0, 279823, 99726, 2109, 16384⟩
    (by decide) selected_cut_10269

theorem selected_cut_10270 : selected 8 ⟨279835, by decide⟩
    (prefixPartial 13 99727) = some ⟨13, 2, 0, 279835, 99727, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_99727_279835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99727 ⟨279835, by decide⟩ :=
  accepted_of_selected 13 99727 ⟨279835, by decide⟩ ⟨13, 2, 0, 279835, 99727, 1073, 16384⟩
    (by decide) selected_cut_10270

theorem unmarked_context_12_24931_279836 : frontier 9 ⟨279836, by decide⟩
    (prefixCache 12 24931) (prefixPartial 12 24931) = false := by
  decide +kernel

theorem node_context_12_24931_279836 : EJMOriginalGlobalDAGData.nodes 9 ⟨279836, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨279789, by decide⟩,⟨279823, by decide⟩,⟨279835, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_24931_279836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24931 ⟨279836, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 24931
    ⟨279836, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨279789, by decide⟩,⟨279823, by decide⟩,⟨279835, by decide⟩]) unmarked_context_12_24931_279836 node_context_12_24931_279836
  intro a
  fin_cases a
  · exact context_13_99724_3444
  · exact context_13_99725_279789
  · exact context_13_99726_279823
  · exact context_13_99727_279835

theorem unmarked_context_11_6232_279837 : frontier 10 ⟨279837, by decide⟩
    (prefixCache 11 6232) (prefixPartial 11 6232) = false := by
  decide +kernel

theorem node_context_11_6232_279837 : EJMOriginalGlobalDAGData.nodes 10 ⟨279837, by decide⟩ =
    .split (coordinate 11) (![⟨279648, by decide⟩,⟨279710, by decide⟩,⟨279775, by decide⟩,⟨279836, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6232_279837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6232 ⟨279837, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6232
    ⟨279837, by decide⟩ (by decide) (![⟨279648, by decide⟩,⟨279710, by decide⟩,⟨279775, by decide⟩,⟨279836, by decide⟩]) unmarked_context_11_6232_279837 node_context_11_6232_279837
  intro a
  fin_cases a
  · exact context_12_24928_279648
  · exact context_12_24929_279710
  · exact context_12_24930_279775
  · exact context_12_24931_279836

theorem selected_cut_10271 : selected 9 ⟨279877, by decide⟩
    (prefixPartial 12 24932) = some ⟨12, 2, 0, 279877, 24932, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_24932_279877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24932 ⟨279877, by decide⟩ :=
  accepted_of_selected 12 24932 ⟨279877, by decide⟩ ⟨12, 2, 0, 279877, 24932, 2961, 65536⟩
    (by decide) selected_cut_10271

theorem selected_cut_10272 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 24933) = some ⟨12, 1, 0, 126884, 24933, 1, 65536⟩ := by
  decide +kernel

theorem context_12_24933_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24933 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 24933 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 24933, 1, 65536⟩
    (by decide) selected_cut_10272

theorem selected_cut_10273 : selected 9 ⟨279930, by decide⟩
    (prefixPartial 12 24934) = some ⟨12, 2, 0, 279930, 24934, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_24934_279930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 24934 ⟨279930, by decide⟩ :=
  accepted_of_selected 12 24934 ⟨279930, by decide⟩ ⟨12, 2, 0, 279930, 24934, 3777, 65536⟩
    (by decide) selected_cut_10273

theorem selected_cut_10274 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 99740) = some ⟨13, 1, 0, 3444, 99740, 1, 16384⟩ := by
  decide +kernel

theorem context_13_99740_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 99740 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 99740 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 99740, 1, 16384⟩
    (by decide) selected_cut_10274

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
