/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover277
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_26693 : selected 8 ⟨674796, by decide⟩
    (prefixPartial 13 355775) = some ⟨13, 2, 0, 674796, 355775, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_355775_674796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355775 ⟨674796, by decide⟩ :=
  accepted_of_selected 13 355775 ⟨674796, by decide⟩ ⟨13, 2, 0, 674796, 355775, 1173, 16384⟩
    (by decide) selected_cut_26693

theorem unmarked_context_12_88943_674797 : frontier 9 ⟨674797, by decide⟩
    (prefixCache 12 88943) (prefixPartial 12 88943) = false := by
  decide +kernel

theorem node_context_12_88943_674797 : EJMOriginalGlobalDAGData.nodes 9 ⟨674797, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨674763, by decide⟩,⟨674785, by decide⟩,⟨674796, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88943_674797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88943 ⟨674797, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88943
    ⟨674797, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨674763, by decide⟩,⟨674785, by decide⟩,⟨674796, by decide⟩]) unmarked_context_12_88943_674797 node_context_12_88943_674797
  intro a
  fin_cases a
  · exact context_13_355772_3444
  · exact context_13_355773_674763
  · exact context_13_355774_674785
  · exact context_13_355775_674796

theorem unmarked_context_11_22235_674798 : frontier 10 ⟨674798, by decide⟩
    (prefixCache 11 22235) (prefixPartial 11 22235) = false := by
  decide +kernel

theorem node_context_11_22235_674798 : EJMOriginalGlobalDAGData.nodes 10 ⟨674798, by decide⟩ =
    .split (coordinate 11) (![⟨674668, by decide⟩,⟨674713, by decide⟩,⟨674749, by decide⟩,⟨674797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22235_674798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22235 ⟨674798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22235
    ⟨674798, by decide⟩ (by decide) (![⟨674668, by decide⟩,⟨674713, by decide⟩,⟨674749, by decide⟩,⟨674797, by decide⟩]) unmarked_context_11_22235_674798 node_context_11_22235_674798
  intro a
  fin_cases a
  · exact context_12_88940_674668
  · exact context_12_88941_674713
  · exact context_12_88942_674749
  · exact context_12_88943_674797

theorem unmarked_context_10_5558_674799 : frontier 11 ⟨674799, by decide⟩
    (prefixCache 10 5558) (prefixPartial 10 5558) = false := by
  decide +kernel

theorem node_context_10_5558_674799 : EJMOriginalGlobalDAGData.nodes 11 ⟨674799, by decide⟩ =
    .split (coordinate 10) (![⟨674251, by decide⟩,⟨674362, by decide⟩,⟨674635, by decide⟩,⟨674798, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5558_674799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5558 ⟨674799, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5558
    ⟨674799, by decide⟩ (by decide) (![⟨674251, by decide⟩,⟨674362, by decide⟩,⟨674635, by decide⟩,⟨674798, by decide⟩]) unmarked_context_10_5558_674799 node_context_10_5558_674799
  intro a
  fin_cases a
  · exact context_11_22232_674251
  · exact context_11_22233_674362
  · exact context_11_22234_674635
  · exact context_11_22235_674798

theorem selected_cut_26694 : selected 9 ⟨674830, by decide⟩
    (prefixPartial 12 88944) = some ⟨12, 2, 0, 674830, 88944, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_88944_674830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88944 ⟨674830, by decide⟩ :=
  accepted_of_selected 12 88944 ⟨674830, by decide⟩ ⟨12, 2, 0, 674830, 88944, 2657, 65536⟩
    (by decide) selected_cut_26694

theorem selected_cut_26695 : selected 9 ⟨674906, by decide⟩
    (prefixPartial 12 88945) = some ⟨12, 2, 0, 674906, 88945, 3597, 65536⟩ := by
  decide +kernel

theorem context_12_88945_674906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88945 ⟨674906, by decide⟩ :=
  accepted_of_selected 12 88945 ⟨674906, by decide⟩ ⟨12, 2, 0, 674906, 88945, 3597, 65536⟩
    (by decide) selected_cut_26695

theorem selected_cut_26696 : selected 9 ⟨674941, by decide⟩
    (prefixPartial 12 88946) = some ⟨12, 2, 0, 674941, 88946, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_88946_674941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88946 ⟨674941, by decide⟩ :=
  accepted_of_selected 12 88946 ⟨674941, by decide⟩ ⟨12, 2, 0, 674941, 88946, 2909, 65536⟩
    (by decide) selected_cut_26696

theorem selected_cut_26697 : selected 9 ⟨674971, by decide⟩
    (prefixPartial 12 88947) = some ⟨12, 2, 0, 674971, 88947, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_88947_674971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88947 ⟨674971, by decide⟩ :=
  accepted_of_selected 12 88947 ⟨674971, by decide⟩ ⟨12, 2, 0, 674971, 88947, 2613, 65536⟩
    (by decide) selected_cut_26697

theorem unmarked_context_11_22236_674972 : frontier 10 ⟨674972, by decide⟩
    (prefixCache 11 22236) (prefixPartial 11 22236) = false := by
  decide +kernel

theorem node_context_11_22236_674972 : EJMOriginalGlobalDAGData.nodes 10 ⟨674972, by decide⟩ =
    .split (coordinate 11) (![⟨674830, by decide⟩,⟨674906, by decide⟩,⟨674941, by decide⟩,⟨674971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22236_674972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22236 ⟨674972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22236
    ⟨674972, by decide⟩ (by decide) (![⟨674830, by decide⟩,⟨674906, by decide⟩,⟨674941, by decide⟩,⟨674971, by decide⟩]) unmarked_context_11_22236_674972 node_context_11_22236_674972
  intro a
  fin_cases a
  · exact context_12_88944_674830
  · exact context_12_88945_674906
  · exact context_12_88946_674941
  · exact context_12_88947_674971

theorem selected_cut_26698 : selected 9 ⟨675003, by decide⟩
    (prefixPartial 12 88948) = some ⟨12, 2, 0, 675003, 88948, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_88948_675003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88948 ⟨675003, by decide⟩ :=
  accepted_of_selected 12 88948 ⟨675003, by decide⟩ ⟨12, 2, 0, 675003, 88948, 2633, 65536⟩
    (by decide) selected_cut_26698

theorem selected_cut_26699 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 88949) = some ⟨12, 1, 0, 642794, 88949, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88949_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88949 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 88949 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 88949, 1, 65536⟩
    (by decide) selected_cut_26699

theorem selected_cut_26700 : selected 9 ⟨675030, by decide⟩
    (prefixPartial 12 88950) = some ⟨12, 2, 0, 675030, 88950, 2749, 65536⟩ := by
  decide +kernel

theorem context_12_88950_675030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88950 ⟨675030, by decide⟩ :=
  accepted_of_selected 12 88950 ⟨675030, by decide⟩ ⟨12, 2, 0, 675030, 88950, 2749, 65536⟩
    (by decide) selected_cut_26700

theorem selected_cut_26701 : selected 9 ⟨675056, by decide⟩
    (prefixPartial 12 88951) = some ⟨12, 2, 0, 675056, 88951, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_88951_675056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88951 ⟨675056, by decide⟩ :=
  accepted_of_selected 12 88951 ⟨675056, by decide⟩ ⟨12, 2, 0, 675056, 88951, 2393, 65536⟩
    (by decide) selected_cut_26701

theorem unmarked_context_11_22237_675057 : frontier 10 ⟨675057, by decide⟩
    (prefixCache 11 22237) (prefixPartial 11 22237) = false := by
  decide +kernel

theorem node_context_11_22237_675057 : EJMOriginalGlobalDAGData.nodes 10 ⟨675057, by decide⟩ =
    .split (coordinate 11) (![⟨675003, by decide⟩,⟨642794, by decide⟩,⟨675030, by decide⟩,⟨675056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22237_675057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22237 ⟨675057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22237
    ⟨675057, by decide⟩ (by decide) (![⟨675003, by decide⟩,⟨642794, by decide⟩,⟨675030, by decide⟩,⟨675056, by decide⟩]) unmarked_context_11_22237_675057 node_context_11_22237_675057
  intro a
  fin_cases a
  · exact context_12_88948_675003
  · exact context_12_88949_642794
  · exact context_12_88950_675030
  · exact context_12_88951_675056

theorem selected_cut_26702 : selected 9 ⟨675097, by decide⟩
    (prefixPartial 12 88952) = some ⟨12, 2, 0, 675097, 88952, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_88952_675097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88952 ⟨675097, by decide⟩ :=
  accepted_of_selected 12 88952 ⟨675097, by decide⟩ ⟨12, 2, 0, 675097, 88952, 3029, 65536⟩
    (by decide) selected_cut_26702

theorem selected_cut_26703 : selected 9 ⟨675167, by decide⟩
    (prefixPartial 12 88953) = some ⟨12, 2, 0, 675167, 88953, 3737, 65536⟩ := by
  decide +kernel

theorem context_12_88953_675167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88953 ⟨675167, by decide⟩ :=
  accepted_of_selected 12 88953 ⟨675167, by decide⟩ ⟨12, 2, 0, 675167, 88953, 3737, 65536⟩
    (by decide) selected_cut_26703

theorem selected_cut_26704 : selected 9 ⟨675205, by decide⟩
    (prefixPartial 12 88954) = some ⟨12, 2, 0, 675205, 88954, 3173, 65536⟩ := by
  decide +kernel

theorem context_12_88954_675205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88954 ⟨675205, by decide⟩ :=
  accepted_of_selected 12 88954 ⟨675205, by decide⟩ ⟨12, 2, 0, 675205, 88954, 3173, 65536⟩
    (by decide) selected_cut_26704

theorem selected_cut_26705 : selected 9 ⟨675231, by decide⟩
    (prefixPartial 12 88955) = some ⟨12, 2, 0, 675231, 88955, 2865, 65536⟩ := by
  decide +kernel

theorem context_12_88955_675231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88955 ⟨675231, by decide⟩ :=
  accepted_of_selected 12 88955 ⟨675231, by decide⟩ ⟨12, 2, 0, 675231, 88955, 2865, 65536⟩
    (by decide) selected_cut_26705

theorem unmarked_context_11_22238_675232 : frontier 10 ⟨675232, by decide⟩
    (prefixCache 11 22238) (prefixPartial 11 22238) = false := by
  decide +kernel

theorem node_context_11_22238_675232 : EJMOriginalGlobalDAGData.nodes 10 ⟨675232, by decide⟩ =
    .split (coordinate 11) (![⟨675097, by decide⟩,⟨675167, by decide⟩,⟨675205, by decide⟩,⟨675231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22238_675232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22238 ⟨675232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22238
    ⟨675232, by decide⟩ (by decide) (![⟨675097, by decide⟩,⟨675167, by decide⟩,⟨675205, by decide⟩,⟨675231, by decide⟩]) unmarked_context_11_22238_675232 node_context_11_22238_675232
  intro a
  fin_cases a
  · exact context_12_88952_675097
  · exact context_12_88953_675167
  · exact context_12_88954_675205
  · exact context_12_88955_675231

theorem selected_cut_26706 : selected 9 ⟨675266, by decide⟩
    (prefixPartial 12 88956) = some ⟨12, 2, 0, 675266, 88956, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_88956_675266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88956 ⟨675266, by decide⟩ :=
  accepted_of_selected 12 88956 ⟨675266, by decide⟩ ⟨12, 2, 0, 675266, 88956, 2429, 65536⟩
    (by decide) selected_cut_26706

theorem selected_cut_26707 : selected 9 ⟨675267, by decide⟩
    (prefixPartial 12 88957) = some ⟨12, 1, 0, 675267, 88957, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88957_675267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88957 ⟨675267, by decide⟩ :=
  accepted_of_selected 12 88957 ⟨675267, by decide⟩ ⟨12, 1, 0, 675267, 88957, 1, 65536⟩
    (by decide) selected_cut_26707

theorem selected_cut_26708 : selected 9 ⟨675294, by decide⟩
    (prefixPartial 12 88958) = some ⟨12, 2, 0, 675294, 88958, 2429, 65536⟩ := by
  decide +kernel

theorem context_12_88958_675294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88958 ⟨675294, by decide⟩ :=
  accepted_of_selected 12 88958 ⟨675294, by decide⟩ ⟨12, 2, 0, 675294, 88958, 2429, 65536⟩
    (by decide) selected_cut_26708

theorem selected_cut_26709 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 88959) = some ⟨12, 1, 0, 512556, 88959, 1, 65536⟩ := by
  decide +kernel

theorem context_12_88959_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88959 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 88959 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 88959, 1, 65536⟩
    (by decide) selected_cut_26709

theorem unmarked_context_11_22239_675295 : frontier 10 ⟨675295, by decide⟩
    (prefixCache 11 22239) (prefixPartial 11 22239) = false := by
  decide +kernel

theorem node_context_11_22239_675295 : EJMOriginalGlobalDAGData.nodes 10 ⟨675295, by decide⟩ =
    .split (coordinate 11) (![⟨675266, by decide⟩,⟨675267, by decide⟩,⟨675294, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22239_675295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22239 ⟨675295, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22239
    ⟨675295, by decide⟩ (by decide) (![⟨675266, by decide⟩,⟨675267, by decide⟩,⟨675294, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_22239_675295 node_context_11_22239_675295
  intro a
  fin_cases a
  · exact context_12_88956_675266
  · exact context_12_88957_675267
  · exact context_12_88958_675294
  · exact context_12_88959_512556

theorem unmarked_context_10_5559_675296 : frontier 11 ⟨675296, by decide⟩
    (prefixCache 10 5559) (prefixPartial 10 5559) = false := by
  decide +kernel

theorem node_context_10_5559_675296 : EJMOriginalGlobalDAGData.nodes 11 ⟨675296, by decide⟩ =
    .split (coordinate 10) (![⟨674972, by decide⟩,⟨675057, by decide⟩,⟨675232, by decide⟩,⟨675295, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5559_675296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5559 ⟨675296, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5559
    ⟨675296, by decide⟩ (by decide) (![⟨674972, by decide⟩,⟨675057, by decide⟩,⟨675232, by decide⟩,⟨675295, by decide⟩]) unmarked_context_10_5559_675296 node_context_10_5559_675296
  intro a
  fin_cases a
  · exact context_11_22236_674972
  · exact context_11_22237_675057
  · exact context_11_22238_675232
  · exact context_11_22239_675295

theorem unmarked_context_9_1389_675297 : frontier 12 ⟨675297, by decide⟩
    (prefixCache 9 1389) (prefixPartial 9 1389) = false := by
  decide +kernel

theorem node_context_9_1389_675297 : EJMOriginalGlobalDAGData.nodes 12 ⟨675297, by decide⟩ =
    .split (coordinate 9) (![⟨673381, by decide⟩,⟨674072, by decide⟩,⟨674799, by decide⟩,⟨675296, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1389_675297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1389 ⟨675297, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1389
    ⟨675297, by decide⟩ (by decide) (![⟨673381, by decide⟩,⟨674072, by decide⟩,⟨674799, by decide⟩,⟨675296, by decide⟩]) unmarked_context_9_1389_675297 node_context_9_1389_675297
  intro a
  fin_cases a
  · exact context_10_5556_673381
  · exact context_10_5557_674072
  · exact context_10_5558_674799
  · exact context_10_5559_675296

theorem selected_cut_26710 : selected 9 ⟨675322, by decide⟩
    (prefixPartial 12 88960) = some ⟨12, 2, 0, 675322, 88960, 1981, 65536⟩ := by
  decide +kernel

theorem context_12_88960_675322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88960 ⟨675322, by decide⟩ :=
  accepted_of_selected 12 88960 ⟨675322, by decide⟩ ⟨12, 2, 0, 675322, 88960, 1981, 65536⟩
    (by decide) selected_cut_26710

theorem selected_cut_26711 : selected 9 ⟨675348, by decide⟩
    (prefixPartial 12 88961) = some ⟨12, 2, 0, 675348, 88961, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_88961_675348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88961 ⟨675348, by decide⟩ :=
  accepted_of_selected 12 88961 ⟨675348, by decide⟩ ⟨12, 2, 0, 675348, 88961, 1929, 65536⟩
    (by decide) selected_cut_26711

theorem selected_cut_26712 : selected 9 ⟨675392, by decide⟩
    (prefixPartial 12 88962) = some ⟨12, 2, 0, 675392, 88962, 2365, 65536⟩ := by
  decide +kernel

theorem context_12_88962_675392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88962 ⟨675392, by decide⟩ :=
  accepted_of_selected 12 88962 ⟨675392, by decide⟩ ⟨12, 2, 0, 675392, 88962, 2365, 65536⟩
    (by decide) selected_cut_26712

theorem selected_cut_26713 : selected 9 ⟨675420, by decide⟩
    (prefixPartial 12 88963) = some ⟨12, 2, 0, 675420, 88963, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_88963_675420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88963 ⟨675420, by decide⟩ :=
  accepted_of_selected 12 88963 ⟨675420, by decide⟩ ⟨12, 2, 0, 675420, 88963, 1997, 65536⟩
    (by decide) selected_cut_26713

theorem unmarked_context_11_22240_675421 : frontier 10 ⟨675421, by decide⟩
    (prefixCache 11 22240) (prefixPartial 11 22240) = false := by
  decide +kernel

theorem node_context_11_22240_675421 : EJMOriginalGlobalDAGData.nodes 10 ⟨675421, by decide⟩ =
    .split (coordinate 11) (![⟨675322, by decide⟩,⟨675348, by decide⟩,⟨675392, by decide⟩,⟨675420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22240_675421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22240 ⟨675421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22240
    ⟨675421, by decide⟩ (by decide) (![⟨675322, by decide⟩,⟨675348, by decide⟩,⟨675392, by decide⟩,⟨675420, by decide⟩]) unmarked_context_11_22240_675421 node_context_11_22240_675421
  intro a
  fin_cases a
  · exact context_12_88960_675322
  · exact context_12_88961_675348
  · exact context_12_88962_675392
  · exact context_12_88963_675420

theorem selected_cut_26714 : selected 9 ⟨675445, by decide⟩
    (prefixPartial 12 88964) = some ⟨12, 2, 0, 675445, 88964, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_88964_675445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88964 ⟨675445, by decide⟩ :=
  accepted_of_selected 12 88964 ⟨675445, by decide⟩ ⟨12, 2, 0, 675445, 88964, 2005, 65536⟩
    (by decide) selected_cut_26714

theorem selected_cut_26715 : selected 9 ⟨675470, by decide⟩
    (prefixPartial 12 88965) = some ⟨12, 2, 0, 675470, 88965, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_88965_675470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88965 ⟨675470, by decide⟩ :=
  accepted_of_selected 12 88965 ⟨675470, by decide⟩ ⟨12, 2, 0, 675470, 88965, 1625, 65536⟩
    (by decide) selected_cut_26715

theorem selected_cut_26716 : selected 9 ⟨675504, by decide⟩
    (prefixPartial 12 88966) = some ⟨12, 2, 0, 675504, 88966, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_88966_675504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88966 ⟨675504, by decide⟩ :=
  accepted_of_selected 12 88966 ⟨675504, by decide⟩ ⟨12, 2, 0, 675504, 88966, 2141, 65536⟩
    (by decide) selected_cut_26716

theorem selected_cut_26717 : selected 9 ⟨675527, by decide⟩
    (prefixPartial 12 88967) = some ⟨12, 2, 0, 675527, 88967, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_88967_675527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88967 ⟨675527, by decide⟩ :=
  accepted_of_selected 12 88967 ⟨675527, by decide⟩ ⟨12, 2, 0, 675527, 88967, 1801, 65536⟩
    (by decide) selected_cut_26717

theorem unmarked_context_11_22241_675528 : frontier 10 ⟨675528, by decide⟩
    (prefixCache 11 22241) (prefixPartial 11 22241) = false := by
  decide +kernel

theorem node_context_11_22241_675528 : EJMOriginalGlobalDAGData.nodes 10 ⟨675528, by decide⟩ =
    .split (coordinate 11) (![⟨675445, by decide⟩,⟨675470, by decide⟩,⟨675504, by decide⟩,⟨675527, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22241_675528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22241 ⟨675528, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22241
    ⟨675528, by decide⟩ (by decide) (![⟨675445, by decide⟩,⟨675470, by decide⟩,⟨675504, by decide⟩,⟨675527, by decide⟩]) unmarked_context_11_22241_675528 node_context_11_22241_675528
  intro a
  fin_cases a
  · exact context_12_88964_675445
  · exact context_12_88965_675470
  · exact context_12_88966_675504
  · exact context_12_88967_675527

theorem selected_cut_26718 : selected 9 ⟨675553, by decide⟩
    (prefixPartial 12 88968) = some ⟨12, 2, 0, 675553, 88968, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_88968_675553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88968 ⟨675553, by decide⟩ :=
  accepted_of_selected 12 88968 ⟨675553, by decide⟩ ⟨12, 2, 0, 675553, 88968, 2029, 65536⟩
    (by decide) selected_cut_26718

theorem selected_cut_26719 : selected 9 ⟨675577, by decide⟩
    (prefixPartial 12 88969) = some ⟨12, 2, 0, 675577, 88969, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_88969_675577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88969 ⟨675577, by decide⟩ :=
  accepted_of_selected 12 88969 ⟨675577, by decide⟩ ⟨12, 2, 0, 675577, 88969, 1829, 65536⟩
    (by decide) selected_cut_26719

theorem selected_cut_26720 : selected 9 ⟨675609, by decide⟩
    (prefixPartial 12 88970) = some ⟨12, 2, 0, 675609, 88970, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_88970_675609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88970 ⟨675609, by decide⟩ :=
  accepted_of_selected 12 88970 ⟨675609, by decide⟩ ⟨12, 2, 0, 675609, 88970, 2233, 65536⟩
    (by decide) selected_cut_26720

theorem selected_cut_26721 : selected 9 ⟨675636, by decide⟩
    (prefixPartial 12 88971) = some ⟨12, 2, 0, 675636, 88971, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_88971_675636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88971 ⟨675636, by decide⟩ :=
  accepted_of_selected 12 88971 ⟨675636, by decide⟩ ⟨12, 2, 0, 675636, 88971, 1925, 65536⟩
    (by decide) selected_cut_26721

theorem unmarked_context_11_22242_675637 : frontier 10 ⟨675637, by decide⟩
    (prefixCache 11 22242) (prefixPartial 11 22242) = false := by
  decide +kernel

theorem node_context_11_22242_675637 : EJMOriginalGlobalDAGData.nodes 10 ⟨675637, by decide⟩ =
    .split (coordinate 11) (![⟨675553, by decide⟩,⟨675577, by decide⟩,⟨675609, by decide⟩,⟨675636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22242_675637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22242 ⟨675637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22242
    ⟨675637, by decide⟩ (by decide) (![⟨675553, by decide⟩,⟨675577, by decide⟩,⟨675609, by decide⟩,⟨675636, by decide⟩]) unmarked_context_11_22242_675637 node_context_11_22242_675637
  intro a
  fin_cases a
  · exact context_12_88968_675553
  · exact context_12_88969_675577
  · exact context_12_88970_675609
  · exact context_12_88971_675636

theorem selected_cut_26722 : selected 9 ⟨675657, by decide⟩
    (prefixPartial 12 88972) = some ⟨12, 2, 0, 675657, 88972, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_88972_675657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88972 ⟨675657, by decide⟩ :=
  accepted_of_selected 12 88972 ⟨675657, by decide⟩ ⟨12, 2, 0, 675657, 88972, 1769, 65536⟩
    (by decide) selected_cut_26722

theorem selected_cut_26723 : selected 9 ⟨675678, by decide⟩
    (prefixPartial 12 88973) = some ⟨12, 2, 0, 675678, 88973, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_88973_675678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88973 ⟨675678, by decide⟩ :=
  accepted_of_selected 12 88973 ⟨675678, by decide⟩ ⟨12, 2, 0, 675678, 88973, 1569, 65536⟩
    (by decide) selected_cut_26723

theorem selected_cut_26724 : selected 9 ⟨675711, by decide⟩
    (prefixPartial 12 88974) = some ⟨12, 2, 0, 675711, 88974, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_88974_675711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88974 ⟨675711, by decide⟩ :=
  accepted_of_selected 12 88974 ⟨675711, by decide⟩ ⟨12, 2, 0, 675711, 88974, 1873, 65536⟩
    (by decide) selected_cut_26724

theorem selected_cut_26725 : selected 9 ⟨675745, by decide⟩
    (prefixPartial 12 88975) = some ⟨12, 2, 0, 675745, 88975, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_88975_675745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88975 ⟨675745, by decide⟩ :=
  accepted_of_selected 12 88975 ⟨675745, by decide⟩ ⟨12, 2, 0, 675745, 88975, 2793, 65536⟩
    (by decide) selected_cut_26725

theorem unmarked_context_11_22243_675746 : frontier 10 ⟨675746, by decide⟩
    (prefixCache 11 22243) (prefixPartial 11 22243) = false := by
  decide +kernel

theorem node_context_11_22243_675746 : EJMOriginalGlobalDAGData.nodes 10 ⟨675746, by decide⟩ =
    .split (coordinate 11) (![⟨675657, by decide⟩,⟨675678, by decide⟩,⟨675711, by decide⟩,⟨675745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22243_675746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22243 ⟨675746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22243
    ⟨675746, by decide⟩ (by decide) (![⟨675657, by decide⟩,⟨675678, by decide⟩,⟨675711, by decide⟩,⟨675745, by decide⟩]) unmarked_context_11_22243_675746 node_context_11_22243_675746
  intro a
  fin_cases a
  · exact context_12_88972_675657
  · exact context_12_88973_675678
  · exact context_12_88974_675711
  · exact context_12_88975_675745

theorem unmarked_context_10_5560_675747 : frontier 11 ⟨675747, by decide⟩
    (prefixCache 10 5560) (prefixPartial 10 5560) = false := by
  decide +kernel

theorem node_context_10_5560_675747 : EJMOriginalGlobalDAGData.nodes 11 ⟨675747, by decide⟩ =
    .split (coordinate 10) (![⟨675421, by decide⟩,⟨675528, by decide⟩,⟨675637, by decide⟩,⟨675746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5560_675747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5560 ⟨675747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5560
    ⟨675747, by decide⟩ (by decide) (![⟨675421, by decide⟩,⟨675528, by decide⟩,⟨675637, by decide⟩,⟨675746, by decide⟩]) unmarked_context_10_5560_675747 node_context_10_5560_675747
  intro a
  fin_cases a
  · exact context_11_22240_675421
  · exact context_11_22241_675528
  · exact context_11_22242_675637
  · exact context_11_22243_675746

theorem selected_cut_26726 : selected 9 ⟨675771, by decide⟩
    (prefixPartial 12 88976) = some ⟨12, 2, 0, 675771, 88976, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_88976_675771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88976 ⟨675771, by decide⟩ :=
  accepted_of_selected 12 88976 ⟨675771, by decide⟩ ⟨12, 2, 0, 675771, 88976, 1757, 65536⟩
    (by decide) selected_cut_26726

theorem selected_cut_26727 : selected 9 ⟨675793, by decide⟩
    (prefixPartial 12 88977) = some ⟨12, 2, 0, 675793, 88977, 1801, 65536⟩ := by
  decide +kernel

theorem context_12_88977_675793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88977 ⟨675793, by decide⟩ :=
  accepted_of_selected 12 88977 ⟨675793, by decide⟩ ⟨12, 2, 0, 675793, 88977, 1801, 65536⟩
    (by decide) selected_cut_26727

theorem selected_cut_26728 : selected 9 ⟨675821, by decide⟩
    (prefixPartial 12 88978) = some ⟨12, 2, 0, 675821, 88978, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_88978_675821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88978 ⟨675821, by decide⟩ :=
  accepted_of_selected 12 88978 ⟨675821, by decide⟩ ⟨12, 2, 0, 675821, 88978, 2053, 65536⟩
    (by decide) selected_cut_26728

theorem selected_cut_26729 : selected 9 ⟨675840, by decide⟩
    (prefixPartial 12 88979) = some ⟨12, 2, 0, 675840, 88979, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_88979_675840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88979 ⟨675840, by decide⟩ :=
  accepted_of_selected 12 88979 ⟨675840, by decide⟩ ⟨12, 2, 0, 675840, 88979, 1613, 65536⟩
    (by decide) selected_cut_26729

theorem unmarked_context_11_22244_675841 : frontier 10 ⟨675841, by decide⟩
    (prefixCache 11 22244) (prefixPartial 11 22244) = false := by
  decide +kernel

theorem node_context_11_22244_675841 : EJMOriginalGlobalDAGData.nodes 10 ⟨675841, by decide⟩ =
    .split (coordinate 11) (![⟨675771, by decide⟩,⟨675793, by decide⟩,⟨675821, by decide⟩,⟨675840, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22244_675841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22244 ⟨675841, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22244
    ⟨675841, by decide⟩ (by decide) (![⟨675771, by decide⟩,⟨675793, by decide⟩,⟨675821, by decide⟩,⟨675840, by decide⟩]) unmarked_context_11_22244_675841 node_context_11_22244_675841
  intro a
  fin_cases a
  · exact context_12_88976_675771
  · exact context_12_88977_675793
  · exact context_12_88978_675821
  · exact context_12_88979_675840

theorem selected_cut_26730 : selected 9 ⟨675860, by decide⟩
    (prefixPartial 12 88980) = some ⟨12, 2, 0, 675860, 88980, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_88980_675860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88980 ⟨675860, by decide⟩ :=
  accepted_of_selected 12 88980 ⟨675860, by decide⟩ ⟨12, 2, 0, 675860, 88980, 1733, 65536⟩
    (by decide) selected_cut_26730

theorem selected_cut_26731 : selected 9 ⟨675876, by decide⟩
    (prefixPartial 12 88981) = some ⟨12, 2, 0, 675876, 88981, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_88981_675876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88981 ⟨675876, by decide⟩ :=
  accepted_of_selected 12 88981 ⟨675876, by decide⟩ ⟨12, 2, 0, 675876, 88981, 1481, 65536⟩
    (by decide) selected_cut_26731

theorem selected_cut_26732 : selected 9 ⟨675897, by decide⟩
    (prefixPartial 12 88982) = some ⟨12, 2, 0, 675897, 88982, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_88982_675897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88982 ⟨675897, by decide⟩ :=
  accepted_of_selected 12 88982 ⟨675897, by decide⟩ ⟨12, 2, 0, 675897, 88982, 1781, 65536⟩
    (by decide) selected_cut_26732

theorem selected_cut_26733 : selected 9 ⟨675915, by decide⟩
    (prefixPartial 12 88983) = some ⟨12, 2, 0, 675915, 88983, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_88983_675915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88983 ⟨675915, by decide⟩ :=
  accepted_of_selected 12 88983 ⟨675915, by decide⟩ ⟨12, 2, 0, 675915, 88983, 1365, 65536⟩
    (by decide) selected_cut_26733

theorem unmarked_context_11_22245_675916 : frontier 10 ⟨675916, by decide⟩
    (prefixCache 11 22245) (prefixPartial 11 22245) = false := by
  decide +kernel

theorem node_context_11_22245_675916 : EJMOriginalGlobalDAGData.nodes 10 ⟨675916, by decide⟩ =
    .split (coordinate 11) (![⟨675860, by decide⟩,⟨675876, by decide⟩,⟨675897, by decide⟩,⟨675915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22245_675916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22245 ⟨675916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22245
    ⟨675916, by decide⟩ (by decide) (![⟨675860, by decide⟩,⟨675876, by decide⟩,⟨675897, by decide⟩,⟨675915, by decide⟩]) unmarked_context_11_22245_675916 node_context_11_22245_675916
  intro a
  fin_cases a
  · exact context_12_88980_675860
  · exact context_12_88981_675876
  · exact context_12_88982_675897
  · exact context_12_88983_675915

theorem selected_cut_26734 : selected 9 ⟨675937, by decide⟩
    (prefixPartial 12 88984) = some ⟨12, 2, 0, 675937, 88984, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_88984_675937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88984 ⟨675937, by decide⟩ :=
  accepted_of_selected 12 88984 ⟨675937, by decide⟩ ⟨12, 2, 0, 675937, 88984, 1769, 65536⟩
    (by decide) selected_cut_26734

theorem selected_cut_26735 : selected 9 ⟨675956, by decide⟩
    (prefixPartial 12 88985) = some ⟨12, 2, 0, 675956, 88985, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_88985_675956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88985 ⟨675956, by decide⟩ :=
  accepted_of_selected 12 88985 ⟨675956, by decide⟩ ⟨12, 2, 0, 675956, 88985, 1685, 65536⟩
    (by decide) selected_cut_26735

theorem selected_cut_26736 : selected 9 ⟨675984, by decide⟩
    (prefixPartial 12 88986) = some ⟨12, 2, 0, 675984, 88986, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_88986_675984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88986 ⟨675984, by decide⟩ :=
  accepted_of_selected 12 88986 ⟨675984, by decide⟩ ⟨12, 2, 0, 675984, 88986, 1841, 65536⟩
    (by decide) selected_cut_26736

theorem selected_cut_26737 : selected 9 ⟨676003, by decide⟩
    (prefixPartial 12 88987) = some ⟨12, 2, 0, 676003, 88987, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_88987_676003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88987 ⟨676003, by decide⟩ :=
  accepted_of_selected 12 88987 ⟨676003, by decide⟩ ⟨12, 2, 0, 676003, 88987, 1517, 65536⟩
    (by decide) selected_cut_26737

theorem unmarked_context_11_22246_676004 : frontier 10 ⟨676004, by decide⟩
    (prefixCache 11 22246) (prefixPartial 11 22246) = false := by
  decide +kernel

theorem node_context_11_22246_676004 : EJMOriginalGlobalDAGData.nodes 10 ⟨676004, by decide⟩ =
    .split (coordinate 11) (![⟨675937, by decide⟩,⟨675956, by decide⟩,⟨675984, by decide⟩,⟨676003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22246_676004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22246 ⟨676004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22246
    ⟨676004, by decide⟩ (by decide) (![⟨675937, by decide⟩,⟨675956, by decide⟩,⟨675984, by decide⟩,⟨676003, by decide⟩]) unmarked_context_11_22246_676004 node_context_11_22246_676004
  intro a
  fin_cases a
  · exact context_12_88984_675937
  · exact context_12_88985_675956
  · exact context_12_88986_675984
  · exact context_12_88987_676003

theorem selected_cut_26738 : selected 9 ⟨676021, by decide⟩
    (prefixPartial 12 88988) = some ⟨12, 2, 0, 676021, 88988, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_88988_676021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88988 ⟨676021, by decide⟩ :=
  accepted_of_selected 12 88988 ⟨676021, by decide⟩ ⟨12, 2, 0, 676021, 88988, 1533, 65536⟩
    (by decide) selected_cut_26738

theorem selected_cut_26739 : selected 9 ⟨676038, by decide⟩
    (prefixPartial 12 88989) = some ⟨12, 2, 0, 676038, 88989, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_88989_676038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88989 ⟨676038, by decide⟩ :=
  accepted_of_selected 12 88989 ⟨676038, by decide⟩ ⟨12, 2, 0, 676038, 88989, 1433, 65536⟩
    (by decide) selected_cut_26739

theorem selected_cut_26740 : selected 9 ⟨676056, by decide⟩
    (prefixPartial 12 88990) = some ⟨12, 2, 0, 676056, 88990, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_88990_676056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88990 ⟨676056, by decide⟩ :=
  accepted_of_selected 12 88990 ⟨676056, by decide⟩ ⟨12, 2, 0, 676056, 88990, 1537, 65536⟩
    (by decide) selected_cut_26740

theorem selected_cut_26741 : selected 9 ⟨676075, by decide⟩
    (prefixPartial 12 88991) = some ⟨12, 2, 0, 676075, 88991, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_88991_676075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88991 ⟨676075, by decide⟩ :=
  accepted_of_selected 12 88991 ⟨676075, by decide⟩ ⟨12, 2, 0, 676075, 88991, 1921, 65536⟩
    (by decide) selected_cut_26741

theorem unmarked_context_11_22247_676076 : frontier 10 ⟨676076, by decide⟩
    (prefixCache 11 22247) (prefixPartial 11 22247) = false := by
  decide +kernel

theorem node_context_11_22247_676076 : EJMOriginalGlobalDAGData.nodes 10 ⟨676076, by decide⟩ =
    .split (coordinate 11) (![⟨676021, by decide⟩,⟨676038, by decide⟩,⟨676056, by decide⟩,⟨676075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22247_676076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22247 ⟨676076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22247
    ⟨676076, by decide⟩ (by decide) (![⟨676021, by decide⟩,⟨676038, by decide⟩,⟨676056, by decide⟩,⟨676075, by decide⟩]) unmarked_context_11_22247_676076 node_context_11_22247_676076
  intro a
  fin_cases a
  · exact context_12_88988_676021
  · exact context_12_88989_676038
  · exact context_12_88990_676056
  · exact context_12_88991_676075

theorem unmarked_context_10_5561_676077 : frontier 11 ⟨676077, by decide⟩
    (prefixCache 10 5561) (prefixPartial 10 5561) = false := by
  decide +kernel

theorem node_context_10_5561_676077 : EJMOriginalGlobalDAGData.nodes 11 ⟨676077, by decide⟩ =
    .split (coordinate 10) (![⟨675841, by decide⟩,⟨675916, by decide⟩,⟨676004, by decide⟩,⟨676076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5561_676077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5561 ⟨676077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5561
    ⟨676077, by decide⟩ (by decide) (![⟨675841, by decide⟩,⟨675916, by decide⟩,⟨676004, by decide⟩,⟨676076, by decide⟩]) unmarked_context_10_5561_676077 node_context_10_5561_676077
  intro a
  fin_cases a
  · exact context_11_22244_675841
  · exact context_11_22245_675916
  · exact context_11_22246_676004
  · exact context_11_22247_676076

theorem selected_cut_26742 : selected 9 ⟨676090, by decide⟩
    (prefixPartial 12 88992) = some ⟨12, 2, 0, 676090, 88992, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_88992_676090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88992 ⟨676090, by decide⟩ :=
  accepted_of_selected 12 88992 ⟨676090, by decide⟩ ⟨12, 2, 0, 676090, 88992, 1153, 65536⟩
    (by decide) selected_cut_26742

theorem selected_cut_26743 : selected 9 ⟨676104, by decide⟩
    (prefixPartial 12 88993) = some ⟨12, 2, 0, 676104, 88993, 1129, 65536⟩ := by
  decide +kernel

theorem context_12_88993_676104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88993 ⟨676104, by decide⟩ :=
  accepted_of_selected 12 88993 ⟨676104, by decide⟩ ⟨12, 2, 0, 676104, 88993, 1129, 65536⟩
    (by decide) selected_cut_26743

theorem selected_cut_26744 : selected 9 ⟨676122, by decide⟩
    (prefixPartial 12 88994) = some ⟨12, 2, 0, 676122, 88994, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_88994_676122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88994 ⟨676122, by decide⟩ :=
  accepted_of_selected 12 88994 ⟨676122, by decide⟩ ⟨12, 2, 0, 676122, 88994, 1321, 65536⟩
    (by decide) selected_cut_26744

theorem selected_cut_26745 : selected 9 ⟨676135, by decide⟩
    (prefixPartial 12 88995) = some ⟨12, 2, 0, 676135, 88995, 1013, 65536⟩ := by
  decide +kernel

theorem context_12_88995_676135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88995 ⟨676135, by decide⟩ :=
  accepted_of_selected 12 88995 ⟨676135, by decide⟩ ⟨12, 2, 0, 676135, 88995, 1013, 65536⟩
    (by decide) selected_cut_26745

theorem unmarked_context_11_22248_676136 : frontier 10 ⟨676136, by decide⟩
    (prefixCache 11 22248) (prefixPartial 11 22248) = false := by
  decide +kernel

theorem node_context_11_22248_676136 : EJMOriginalGlobalDAGData.nodes 10 ⟨676136, by decide⟩ =
    .split (coordinate 11) (![⟨676090, by decide⟩,⟨676104, by decide⟩,⟨676122, by decide⟩,⟨676135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22248_676136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22248 ⟨676136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22248
    ⟨676136, by decide⟩ (by decide) (![⟨676090, by decide⟩,⟨676104, by decide⟩,⟨676122, by decide⟩,⟨676135, by decide⟩]) unmarked_context_11_22248_676136 node_context_11_22248_676136
  intro a
  fin_cases a
  · exact context_12_88992_676090
  · exact context_12_88993_676104
  · exact context_12_88994_676122
  · exact context_12_88995_676135

theorem selected_cut_26746 : selected 9 ⟨676156, by decide⟩
    (prefixPartial 12 88996) = some ⟨12, 2, 0, 676156, 88996, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_88996_676156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88996 ⟨676156, by decide⟩ :=
  accepted_of_selected 12 88996 ⟨676156, by decide⟩ ⟨12, 2, 0, 676156, 88996, 1241, 65536⟩
    (by decide) selected_cut_26746

theorem selected_cut_26747 : selected 9 ⟨676174, by decide⟩
    (prefixPartial 12 88997) = some ⟨12, 2, 0, 676174, 88997, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_88997_676174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88997 ⟨676174, by decide⟩ :=
  accepted_of_selected 12 88997 ⟨676174, by decide⟩ ⟨12, 2, 0, 676174, 88997, 1097, 65536⟩
    (by decide) selected_cut_26747

theorem selected_cut_26748 : selected 9 ⟨676190, by decide⟩
    (prefixPartial 12 88998) = some ⟨12, 2, 0, 676190, 88998, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_88998_676190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88998 ⟨676190, by decide⟩ :=
  accepted_of_selected 12 88998 ⟨676190, by decide⟩ ⟨12, 2, 0, 676190, 88998, 1265, 65536⟩
    (by decide) selected_cut_26748

theorem selected_cut_26749 : selected 9 ⟨676202, by decide⟩
    (prefixPartial 12 88999) = some ⟨12, 2, 0, 676202, 88999, 1045, 65536⟩ := by
  decide +kernel

theorem context_12_88999_676202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88999 ⟨676202, by decide⟩ :=
  accepted_of_selected 12 88999 ⟨676202, by decide⟩ ⟨12, 2, 0, 676202, 88999, 1045, 65536⟩
    (by decide) selected_cut_26749

theorem unmarked_context_11_22249_676203 : frontier 10 ⟨676203, by decide⟩
    (prefixCache 11 22249) (prefixPartial 11 22249) = false := by
  decide +kernel

theorem node_context_11_22249_676203 : EJMOriginalGlobalDAGData.nodes 10 ⟨676203, by decide⟩ =
    .split (coordinate 11) (![⟨676156, by decide⟩,⟨676174, by decide⟩,⟨676190, by decide⟩,⟨676202, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22249_676203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22249 ⟨676203, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22249
    ⟨676203, by decide⟩ (by decide) (![⟨676156, by decide⟩,⟨676174, by decide⟩,⟨676190, by decide⟩,⟨676202, by decide⟩]) unmarked_context_11_22249_676203 node_context_11_22249_676203
  intro a
  fin_cases a
  · exact context_12_88996_676156
  · exact context_12_88997_676174
  · exact context_12_88998_676190
  · exact context_12_88999_676202

theorem selected_cut_26750 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 22250) = some ⟨11, 1, 0, 479708, 22250, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22250_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22250 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 22250 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 22250, 1, 262144⟩
    (by decide) selected_cut_26750

theorem selected_cut_26751 : selected 10 ⟨676252, by decide⟩
    (prefixPartial 11 22251) = some ⟨11, 2, 0, 676252, 22251, 3721, 262144⟩ := by
  decide +kernel

theorem context_11_22251_676252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22251 ⟨676252, by decide⟩ :=
  accepted_of_selected 11 22251 ⟨676252, by decide⟩ ⟨11, 2, 0, 676252, 22251, 3721, 262144⟩
    (by decide) selected_cut_26751

theorem unmarked_context_10_5562_676253 : frontier 11 ⟨676253, by decide⟩
    (prefixCache 10 5562) (prefixPartial 10 5562) = false := by
  decide +kernel

theorem node_context_10_5562_676253 : EJMOriginalGlobalDAGData.nodes 11 ⟨676253, by decide⟩ =
    .split (coordinate 10) (![⟨676136, by decide⟩,⟨676203, by decide⟩,⟨479708, by decide⟩,⟨676252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5562_676253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5562 ⟨676253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5562
    ⟨676253, by decide⟩ (by decide) (![⟨676136, by decide⟩,⟨676203, by decide⟩,⟨479708, by decide⟩,⟨676252, by decide⟩]) unmarked_context_10_5562_676253 node_context_10_5562_676253
  intro a
  fin_cases a
  · exact context_11_22248_676136
  · exact context_11_22249_676203
  · exact context_11_22250_479708
  · exact context_11_22251_676252

theorem selected_cut_26752 : selected 9 ⟨676264, by decide⟩
    (prefixPartial 12 89008) = some ⟨12, 2, 0, 676264, 89008, 1201, 65536⟩ := by
  decide +kernel

theorem context_12_89008_676264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89008 ⟨676264, by decide⟩ :=
  accepted_of_selected 12 89008 ⟨676264, by decide⟩ ⟨12, 2, 0, 676264, 89008, 1201, 65536⟩
    (by decide) selected_cut_26752

theorem selected_cut_26753 : selected 9 ⟨676275, by decide⟩
    (prefixPartial 12 89009) = some ⟨12, 2, 0, 676275, 89009, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_89009_676275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89009 ⟨676275, by decide⟩ :=
  accepted_of_selected 12 89009 ⟨676275, by decide⟩ ⟨12, 2, 0, 676275, 89009, 1217, 65536⟩
    (by decide) selected_cut_26753

theorem selected_cut_26754 : selected 9 ⟨676290, by decide⟩
    (prefixPartial 12 89010) = some ⟨12, 2, 0, 676290, 89010, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_89010_676290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89010 ⟨676290, by decide⟩ :=
  accepted_of_selected 12 89010 ⟨676290, by decide⟩ ⟨12, 2, 0, 676290, 89010, 1213, 65536⟩
    (by decide) selected_cut_26754

theorem selected_cut_26755 : selected 9 ⟨676302, by decide⟩
    (prefixPartial 12 89011) = some ⟨12, 2, 0, 676302, 89011, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_89011_676302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89011 ⟨676302, by decide⟩ :=
  accepted_of_selected 12 89011 ⟨676302, by decide⟩ ⟨12, 2, 0, 676302, 89011, 1101, 65536⟩
    (by decide) selected_cut_26755

theorem unmarked_context_11_22252_676303 : frontier 10 ⟨676303, by decide⟩
    (prefixCache 11 22252) (prefixPartial 11 22252) = false := by
  decide +kernel

theorem node_context_11_22252_676303 : EJMOriginalGlobalDAGData.nodes 10 ⟨676303, by decide⟩ =
    .split (coordinate 11) (![⟨676264, by decide⟩,⟨676275, by decide⟩,⟨676290, by decide⟩,⟨676302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22252_676303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22252 ⟨676303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22252
    ⟨676303, by decide⟩ (by decide) (![⟨676264, by decide⟩,⟨676275, by decide⟩,⟨676290, by decide⟩,⟨676302, by decide⟩]) unmarked_context_11_22252_676303 node_context_11_22252_676303
  intro a
  fin_cases a
  · exact context_12_89008_676264
  · exact context_12_89009_676275
  · exact context_12_89010_676290
  · exact context_12_89011_676302

theorem selected_cut_26756 : selected 9 ⟨676318, by decide⟩
    (prefixPartial 12 89012) = some ⟨12, 2, 0, 676318, 89012, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_89012_676318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89012 ⟨676318, by decide⟩ :=
  accepted_of_selected 12 89012 ⟨676318, by decide⟩ ⟨12, 2, 0, 676318, 89012, 1237, 65536⟩
    (by decide) selected_cut_26756

theorem selected_cut_26757 : selected 9 ⟨676332, by decide⟩
    (prefixPartial 12 89013) = some ⟨12, 2, 0, 676332, 89013, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_89013_676332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89013 ⟨676332, by decide⟩ :=
  accepted_of_selected 12 89013 ⟨676332, by decide⟩ ⟨12, 2, 0, 676332, 89013, 1213, 65536⟩
    (by decide) selected_cut_26757

theorem selected_cut_26758 : selected 9 ⟨676351, by decide⟩
    (prefixPartial 12 89014) = some ⟨12, 2, 0, 676351, 89014, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_89014_676351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89014 ⟨676351, by decide⟩ :=
  accepted_of_selected 12 89014 ⟨676351, by decide⟩ ⟨12, 2, 0, 676351, 89014, 1213, 65536⟩
    (by decide) selected_cut_26758

theorem selected_cut_26759 : selected 9 ⟨676363, by decide⟩
    (prefixPartial 12 89015) = some ⟨12, 2, 0, 676363, 89015, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_89015_676363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89015 ⟨676363, by decide⟩ :=
  accepted_of_selected 12 89015 ⟨676363, by decide⟩ ⟨12, 2, 0, 676363, 89015, 1117, 65536⟩
    (by decide) selected_cut_26759

theorem unmarked_context_11_22253_676364 : frontier 10 ⟨676364, by decide⟩
    (prefixCache 11 22253) (prefixPartial 11 22253) = false := by
  decide +kernel

theorem node_context_11_22253_676364 : EJMOriginalGlobalDAGData.nodes 10 ⟨676364, by decide⟩ =
    .split (coordinate 11) (![⟨676318, by decide⟩,⟨676332, by decide⟩,⟨676351, by decide⟩,⟨676363, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22253_676364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22253 ⟨676364, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22253
    ⟨676364, by decide⟩ (by decide) (![⟨676318, by decide⟩,⟨676332, by decide⟩,⟨676351, by decide⟩,⟨676363, by decide⟩]) unmarked_context_11_22253_676364 node_context_11_22253_676364
  intro a
  fin_cases a
  · exact context_12_89012_676318
  · exact context_12_89013_676332
  · exact context_12_89014_676351
  · exact context_12_89015_676363

theorem selected_cut_26760 : selected 9 ⟨676375, by decide⟩
    (prefixPartial 12 89016) = some ⟨12, 2, 0, 676375, 89016, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_89016_676375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89016 ⟨676375, by decide⟩ :=
  accepted_of_selected 12 89016 ⟨676375, by decide⟩ ⟨12, 2, 0, 676375, 89016, 1097, 65536⟩
    (by decide) selected_cut_26760

theorem selected_cut_26761 : selected 9 ⟨676388, by decide⟩
    (prefixPartial 12 89017) = some ⟨12, 2, 0, 676388, 89017, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_89017_676388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89017 ⟨676388, by decide⟩ :=
  accepted_of_selected 12 89017 ⟨676388, by decide⟩ ⟨12, 2, 0, 676388, 89017, 1145, 65536⟩
    (by decide) selected_cut_26761

theorem selected_cut_26762 : selected 9 ⟨676400, by decide⟩
    (prefixPartial 12 89018) = some ⟨12, 2, 0, 676400, 89018, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_89018_676400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89018 ⟨676400, by decide⟩ :=
  accepted_of_selected 12 89018 ⟨676400, by decide⟩ ⟨12, 2, 0, 676400, 89018, 1121, 65536⟩
    (by decide) selected_cut_26762

theorem selected_cut_26763 : selected 9 ⟨676414, by decide⟩
    (prefixPartial 12 89019) = some ⟨12, 2, 0, 676414, 89019, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_89019_676414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 89019 ⟨676414, by decide⟩ :=
  accepted_of_selected 12 89019 ⟨676414, by decide⟩ ⟨12, 2, 0, 676414, 89019, 1057, 65536⟩
    (by decide) selected_cut_26763

theorem unmarked_context_11_22254_676415 : frontier 10 ⟨676415, by decide⟩
    (prefixCache 11 22254) (prefixPartial 11 22254) = false := by
  decide +kernel

theorem node_context_11_22254_676415 : EJMOriginalGlobalDAGData.nodes 10 ⟨676415, by decide⟩ =
    .split (coordinate 11) (![⟨676375, by decide⟩,⟨676388, by decide⟩,⟨676400, by decide⟩,⟨676414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22254_676415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22254 ⟨676415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22254
    ⟨676415, by decide⟩ (by decide) (![⟨676375, by decide⟩,⟨676388, by decide⟩,⟨676400, by decide⟩,⟨676414, by decide⟩]) unmarked_context_11_22254_676415 node_context_11_22254_676415
  intro a
  fin_cases a
  · exact context_12_89016_676375
  · exact context_12_89017_676388
  · exact context_12_89018_676400
  · exact context_12_89019_676414

theorem selected_cut_26764 : selected 10 ⟨676449, by decide⟩
    (prefixPartial 11 22255) = some ⟨11, 2, 0, 676449, 22255, 2817, 262144⟩ := by
  decide +kernel

theorem context_11_22255_676449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22255 ⟨676449, by decide⟩ :=
  accepted_of_selected 11 22255 ⟨676449, by decide⟩ ⟨11, 2, 0, 676449, 22255, 2817, 262144⟩
    (by decide) selected_cut_26764

theorem unmarked_context_10_5563_676450 : frontier 11 ⟨676450, by decide⟩
    (prefixCache 10 5563) (prefixPartial 10 5563) = false := by
  decide +kernel

theorem node_context_10_5563_676450 : EJMOriginalGlobalDAGData.nodes 11 ⟨676450, by decide⟩ =
    .split (coordinate 10) (![⟨676303, by decide⟩,⟨676364, by decide⟩,⟨676415, by decide⟩,⟨676449, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5563_676450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5563 ⟨676450, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5563
    ⟨676450, by decide⟩ (by decide) (![⟨676303, by decide⟩,⟨676364, by decide⟩,⟨676415, by decide⟩,⟨676449, by decide⟩]) unmarked_context_10_5563_676450 node_context_10_5563_676450
  intro a
  fin_cases a
  · exact context_11_22252_676303
  · exact context_11_22253_676364
  · exact context_11_22254_676415
  · exact context_11_22255_676449

theorem unmarked_context_9_1390_676451 : frontier 12 ⟨676451, by decide⟩
    (prefixCache 9 1390) (prefixPartial 9 1390) = false := by
  decide +kernel

theorem node_context_9_1390_676451 : EJMOriginalGlobalDAGData.nodes 12 ⟨676451, by decide⟩ =
    .split (coordinate 9) (![⟨675747, by decide⟩,⟨676077, by decide⟩,⟨676253, by decide⟩,⟨676450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1390_676451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1390 ⟨676451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1390
    ⟨676451, by decide⟩ (by decide) (![⟨675747, by decide⟩,⟨676077, by decide⟩,⟨676253, by decide⟩,⟨676450, by decide⟩]) unmarked_context_9_1390_676451 node_context_9_1390_676451
  intro a
  fin_cases a
  · exact context_10_5560_675747
  · exact context_10_5561_676077
  · exact context_10_5562_676253
  · exact context_10_5563_676450

theorem selected_cut_26765 : selected 10 ⟨676477, by decide⟩
    (prefixPartial 11 22256) = some ⟨11, 2, 0, 676477, 22256, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_22256_676477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22256 ⟨676477, by decide⟩ :=
  accepted_of_selected 11 22256 ⟨676477, by decide⟩ ⟨11, 2, 0, 676477, 22256, 2193, 262144⟩
    (by decide) selected_cut_26765

theorem selected_cut_26766 : selected 10 ⟨676501, by decide⟩
    (prefixPartial 11 22257) = some ⟨11, 2, 0, 676501, 22257, 2489, 262144⟩ := by
  decide +kernel

theorem context_11_22257_676501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22257 ⟨676501, by decide⟩ :=
  accepted_of_selected 11 22257 ⟨676501, by decide⟩ ⟨11, 2, 0, 676501, 22257, 2489, 262144⟩
    (by decide) selected_cut_26766

theorem selected_cut_26767 : selected 10 ⟨676519, by decide⟩
    (prefixPartial 11 22258) = some ⟨11, 2, 0, 676519, 22258, 2001, 262144⟩ := by
  decide +kernel

theorem context_11_22258_676519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22258 ⟨676519, by decide⟩ :=
  accepted_of_selected 11 22258 ⟨676519, by decide⟩ ⟨11, 2, 0, 676519, 22258, 2001, 262144⟩
    (by decide) selected_cut_26767

theorem selected_cut_26768 : selected 10 ⟨676541, by decide⟩
    (prefixPartial 11 22259) = some ⟨11, 2, 0, 676541, 22259, 1765, 262144⟩ := by
  decide +kernel

theorem context_11_22259_676541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22259 ⟨676541, by decide⟩ :=
  accepted_of_selected 11 22259 ⟨676541, by decide⟩ ⟨11, 2, 0, 676541, 22259, 1765, 262144⟩
    (by decide) selected_cut_26768

theorem unmarked_context_10_5564_676542 : frontier 11 ⟨676542, by decide⟩
    (prefixCache 10 5564) (prefixPartial 10 5564) = false := by
  decide +kernel

theorem node_context_10_5564_676542 : EJMOriginalGlobalDAGData.nodes 11 ⟨676542, by decide⟩ =
    .split (coordinate 10) (![⟨676477, by decide⟩,⟨676501, by decide⟩,⟨676519, by decide⟩,⟨676541, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5564_676542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5564 ⟨676542, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5564
    ⟨676542, by decide⟩ (by decide) (![⟨676477, by decide⟩,⟨676501, by decide⟩,⟨676519, by decide⟩,⟨676541, by decide⟩]) unmarked_context_10_5564_676542 node_context_10_5564_676542
  intro a
  fin_cases a
  · exact context_11_22256_676477
  · exact context_11_22257_676501
  · exact context_11_22258_676519
  · exact context_11_22259_676541

theorem selected_cut_26769 : selected 10 ⟨676562, by decide⟩
    (prefixPartial 11 22260) = some ⟨11, 2, 0, 676562, 22260, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_22260_676562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22260 ⟨676562, by decide⟩ :=
  accepted_of_selected 11 22260 ⟨676562, by decide⟩ ⟨11, 2, 0, 676562, 22260, 2089, 262144⟩
    (by decide) selected_cut_26769

theorem selected_cut_26770 : selected 10 ⟨676590, by decide⟩
    (prefixPartial 11 22261) = some ⟨11, 2, 0, 676590, 22261, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_22261_676590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22261 ⟨676590, by decide⟩ :=
  accepted_of_selected 11 22261 ⟨676590, by decide⟩ ⟨11, 2, 0, 676590, 22261, 2125, 262144⟩
    (by decide) selected_cut_26770

theorem selected_cut_26771 : selected 10 ⟨676616, by decide⟩
    (prefixPartial 11 22262) = some ⟨11, 2, 0, 676616, 22262, 1881, 262144⟩ := by
  decide +kernel

theorem context_11_22262_676616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22262 ⟨676616, by decide⟩ :=
  accepted_of_selected 11 22262 ⟨676616, by decide⟩ ⟨11, 2, 0, 676616, 22262, 1881, 262144⟩
    (by decide) selected_cut_26771

theorem selected_cut_26772 : selected 10 ⟨676640, by decide⟩
    (prefixPartial 11 22263) = some ⟨11, 2, 0, 676640, 22263, 1325, 262144⟩ := by
  decide +kernel

theorem context_11_22263_676640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22263 ⟨676640, by decide⟩ :=
  accepted_of_selected 11 22263 ⟨676640, by decide⟩ ⟨11, 2, 0, 676640, 22263, 1325, 262144⟩
    (by decide) selected_cut_26772

theorem unmarked_context_10_5565_676641 : frontier 11 ⟨676641, by decide⟩
    (prefixCache 10 5565) (prefixPartial 10 5565) = false := by
  decide +kernel

theorem node_context_10_5565_676641 : EJMOriginalGlobalDAGData.nodes 11 ⟨676641, by decide⟩ =
    .split (coordinate 10) (![⟨676562, by decide⟩,⟨676590, by decide⟩,⟨676616, by decide⟩,⟨676640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5565_676641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5565 ⟨676641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5565
    ⟨676641, by decide⟩ (by decide) (![⟨676562, by decide⟩,⟨676590, by decide⟩,⟨676616, by decide⟩,⟨676640, by decide⟩]) unmarked_context_10_5565_676641 node_context_10_5565_676641
  intro a
  fin_cases a
  · exact context_11_22260_676562
  · exact context_11_22261_676590
  · exact context_11_22262_676616
  · exact context_11_22263_676640

theorem selected_cut_26773 : selected 11 ⟨676698, by decide⟩
    (prefixPartial 10 5566) = some ⟨10, 2, 0, 676698, 5566, 3625, 1048576⟩ := by
  decide +kernel

theorem context_10_5566_676698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5566 ⟨676698, by decide⟩ :=
  accepted_of_selected 10 5566 ⟨676698, by decide⟩ ⟨10, 2, 0, 676698, 5566, 3625, 1048576⟩
    (by decide) selected_cut_26773

theorem selected_cut_26774 : selected 11 ⟨676727, by decide⟩
    (prefixPartial 10 5567) = some ⟨10, 2, 0, 676727, 5567, 1357, 1048576⟩ := by
  decide +kernel

theorem context_10_5567_676727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5567 ⟨676727, by decide⟩ :=
  accepted_of_selected 10 5567 ⟨676727, by decide⟩ ⟨10, 2, 0, 676727, 5567, 1357, 1048576⟩
    (by decide) selected_cut_26774

theorem unmarked_context_9_1391_676728 : frontier 12 ⟨676728, by decide⟩
    (prefixCache 9 1391) (prefixPartial 9 1391) = false := by
  decide +kernel

theorem node_context_9_1391_676728 : EJMOriginalGlobalDAGData.nodes 12 ⟨676728, by decide⟩ =
    .split (coordinate 9) (![⟨676542, by decide⟩,⟨676641, by decide⟩,⟨676698, by decide⟩,⟨676727, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1391_676728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1391 ⟨676728, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1391
    ⟨676728, by decide⟩ (by decide) (![⟨676542, by decide⟩,⟨676641, by decide⟩,⟨676698, by decide⟩,⟨676727, by decide⟩]) unmarked_context_9_1391_676728 node_context_9_1391_676728
  intro a
  fin_cases a
  · exact context_10_5564_676542
  · exact context_10_5565_676641
  · exact context_10_5566_676698
  · exact context_10_5567_676727

theorem unmarked_context_8_347_676729 : frontier 13 ⟨676729, by decide⟩
    (prefixCache 8 347) (prefixPartial 8 347) = false := by
  decide +kernel

theorem node_context_8_347_676729 : EJMOriginalGlobalDAGData.nodes 13 ⟨676729, by decide⟩ =
    .split (coordinate 8) (![⟨672487, by decide⟩,⟨675297, by decide⟩,⟨676451, by decide⟩,⟨676728, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_347_676729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 347 ⟨676729, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 347
    ⟨676729, by decide⟩ (by decide) (![⟨672487, by decide⟩,⟨675297, by decide⟩,⟨676451, by decide⟩,⟨676728, by decide⟩]) unmarked_context_8_347_676729 node_context_8_347_676729
  intro a
  fin_cases a
  · exact context_9_1388_672487
  · exact context_9_1389_675297
  · exact context_9_1390_676451
  · exact context_9_1391_676728

theorem unmarked_context_7_86_676730 : frontier 14 ⟨676730, by decide⟩
    (prefixCache 7 86) (prefixPartial 7 86) = false := by
  decide +kernel

theorem node_context_7_86_676730 : EJMOriginalGlobalDAGData.nodes 14 ⟨676730, by decide⟩ =
    .split (coordinate 7) (![⟨657998, by decide⟩,⟨643294, by decide⟩,⟨666727, by decide⟩,⟨676729, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_86_676730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 86 ⟨676730, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 86
    ⟨676730, by decide⟩ (by decide) (![⟨657998, by decide⟩,⟨643294, by decide⟩,⟨666727, by decide⟩,⟨676729, by decide⟩]) unmarked_context_7_86_676730 node_context_7_86_676730
  intro a
  fin_cases a
  · exact context_8_344_657998
  · exact context_8_345_643294
  · exact context_8_346_666727
  · exact context_8_347_676729

theorem selected_cut_26775 : selected 14 ⟨34032, by decide⟩
    (prefixPartial 7 87) = some ⟨7, 1, 0, 34032, 87, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_87_34032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 87 ⟨34032, by decide⟩ :=
  accepted_of_selected 7 87 ⟨34032, by decide⟩ ⟨7, 1, 0, 34032, 87, 1, 67108864⟩
    (by decide) selected_cut_26775

theorem unmarked_context_6_21_676731 : frontier 15 ⟨676731, by decide⟩
    (prefixCache 6 21) (prefixPartial 6 21) = false := by
  decide +kernel

theorem node_context_6_21_676731 : EJMOriginalGlobalDAGData.nodes 15 ⟨676731, by decide⟩ =
    .split (coordinate 6) (![⟨116316, by decide⟩,⟨648653, by decide⟩,⟨676730, by decide⟩,⟨34032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_21_676731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 21 ⟨676731, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 21
    ⟨676731, by decide⟩ (by decide) (![⟨116316, by decide⟩,⟨648653, by decide⟩,⟨676730, by decide⟩,⟨34032, by decide⟩]) unmarked_context_6_21_676731 node_context_6_21_676731
  intro a
  fin_cases a
  · exact context_7_84_116316
  · exact context_7_85_648653
  · exact context_7_86_676730
  · exact context_7_87_34032

theorem selected_cut_26776 : selected 14 ⟨676732, by decide⟩
    (prefixPartial 7 88) = some ⟨7, 1, 0, 676732, 88, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_88_676732 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 88 ⟨676732, by decide⟩ :=
  accepted_of_selected 7 88 ⟨676732, by decide⟩ ⟨7, 1, 0, 676732, 88, 1, 67108864⟩
    (by decide) selected_cut_26776

theorem selected_cut_26777 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 22784) = some ⟨11, 1, 0, 434745, 22784, 1, 262144⟩ := by
  decide +kernel

theorem context_11_22784_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22784 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 22784 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 22784, 1, 262144⟩
    (by decide) selected_cut_26777

theorem selected_cut_26778 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 91140) = some ⟨12, 1, 0, 448748, 91140, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91140_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91140 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 91140 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 91140, 1, 65536⟩
    (by decide) selected_cut_26778

theorem selected_cut_26779 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 91141) = some ⟨12, 1, 0, 34034, 91141, 1, 65536⟩ := by
  decide +kernel

theorem context_12_91141_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91141 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 91141 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 91141, 1, 65536⟩
    (by decide) selected_cut_26779

theorem selected_cut_26780 : selected 8 ⟨676806, by decide⟩
    (prefixPartial 13 364568) = some ⟨13, 2, 0, 676806, 364568, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_364568_676806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364568 ⟨676806, by decide⟩ :=
  accepted_of_selected 13 364568 ⟨676806, by decide⟩ ⟨13, 2, 0, 676806, 364568, 2685, 16384⟩
    (by decide) selected_cut_26780

theorem selected_cut_26781 : selected 8 ⟨676849, by decide⟩
    (prefixPartial 13 364569) = some ⟨13, 2, 0, 676849, 364569, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_364569_676849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364569 ⟨676849, by decide⟩ :=
  accepted_of_selected 13 364569 ⟨676849, by decide⟩ ⟨13, 2, 0, 676849, 364569, 1577, 16384⟩
    (by decide) selected_cut_26781

theorem selected_cut_26782 : selected 8 ⟨676862, by decide⟩
    (prefixPartial 13 364570) = some ⟨13, 2, 0, 676862, 364570, 661, 16384⟩ := by
  decide +kernel

theorem context_13_364570_676862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364570 ⟨676862, by decide⟩ :=
  accepted_of_selected 13 364570 ⟨676862, by decide⟩ ⟨13, 2, 0, 676862, 364570, 661, 16384⟩
    (by decide) selected_cut_26782

theorem selected_cut_26783 : selected 8 ⟨676864, by decide⟩
    (prefixPartial 13 364571) = some ⟨13, 2, 0, 676864, 364571, 145, 16384⟩ := by
  decide +kernel

theorem context_13_364571_676864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364571 ⟨676864, by decide⟩ :=
  accepted_of_selected 13 364571 ⟨676864, by decide⟩ ⟨13, 2, 0, 676864, 364571, 145, 16384⟩
    (by decide) selected_cut_26783

theorem unmarked_context_12_91142_676865 : frontier 9 ⟨676865, by decide⟩
    (prefixCache 12 91142) (prefixPartial 12 91142) = false := by
  decide +kernel

theorem node_context_12_91142_676865 : EJMOriginalGlobalDAGData.nodes 9 ⟨676865, by decide⟩ =
    .split (coordinate 12) (![⟨676806, by decide⟩,⟨676849, by decide⟩,⟨676862, by decide⟩,⟨676864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_91142_676865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 91142 ⟨676865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 91142
    ⟨676865, by decide⟩ (by decide) (![⟨676806, by decide⟩,⟨676849, by decide⟩,⟨676862, by decide⟩,⟨676864, by decide⟩]) unmarked_context_12_91142_676865 node_context_12_91142_676865
  intro a
  fin_cases a
  · exact context_13_364568_676806
  · exact context_13_364569_676849
  · exact context_13_364570_676862
  · exact context_13_364571_676864

theorem selected_cut_26784 : selected 8 ⟨676944, by decide⟩
    (prefixPartial 13 364572) = some ⟨13, 2, 0, 676944, 364572, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_364572_676944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364572 ⟨676944, by decide⟩ :=
  accepted_of_selected 13 364572 ⟨676944, by decide⟩ ⟨13, 2, 0, 676944, 364572, 2909, 16384⟩
    (by decide) selected_cut_26784

theorem selected_cut_26785 : selected 8 ⟨676981, by decide⟩
    (prefixPartial 13 364573) = some ⟨13, 2, 0, 676981, 364573, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_364573_676981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364573 ⟨676981, by decide⟩ :=
  accepted_of_selected 13 364573 ⟨676981, by decide⟩ ⟨13, 2, 0, 676981, 364573, 1749, 16384⟩
    (by decide) selected_cut_26785

theorem selected_cut_26786 : selected 8 ⟨676993, by decide⟩
    (prefixPartial 13 364574) = some ⟨13, 2, 0, 676993, 364574, 713, 16384⟩ := by
  decide +kernel

theorem context_13_364574_676993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 364574 ⟨676993, by decide⟩ :=
  accepted_of_selected 13 364574 ⟨676993, by decide⟩ ⟨13, 2, 0, 676993, 364574, 713, 16384⟩
    (by decide) selected_cut_26786

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
