/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover291
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28035 : selected 9 ⟨707900, by decide⟩
    (prefixPartial 12 92004) = some ⟨12, 2, 0, 707900, 92004, 2745, 65536⟩ := by
  decide +kernel

theorem context_12_92004_707900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92004 ⟨707900, by decide⟩ :=
  accepted_of_selected 12 92004 ⟨707900, by decide⟩ ⟨12, 2, 0, 707900, 92004, 2745, 65536⟩
    (by decide) selected_cut_28035

theorem selected_cut_28036 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 92005) = some ⟨12, 1, 0, 642794, 92005, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92005_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92005 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 92005 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 92005, 1, 65536⟩
    (by decide) selected_cut_28036

theorem selected_cut_28037 : selected 9 ⟨707947, by decide⟩
    (prefixPartial 12 92006) = some ⟨12, 2, 0, 707947, 92006, 2833, 65536⟩ := by
  decide +kernel

theorem context_12_92006_707947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92006 ⟨707947, by decide⟩ :=
  accepted_of_selected 12 92006 ⟨707947, by decide⟩ ⟨12, 2, 0, 707947, 92006, 2833, 65536⟩
    (by decide) selected_cut_28037

theorem selected_cut_28038 : selected 9 ⟨707986, by decide⟩
    (prefixPartial 12 92007) = some ⟨12, 2, 0, 707986, 92007, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_92007_707986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92007 ⟨707986, by decide⟩ :=
  accepted_of_selected 12 92007 ⟨707986, by decide⟩ ⟨12, 2, 0, 707986, 92007, 2453, 65536⟩
    (by decide) selected_cut_28038

theorem unmarked_context_11_23001_707987 : frontier 10 ⟨707987, by decide⟩
    (prefixCache 11 23001) (prefixPartial 11 23001) = false := by
  decide +kernel

theorem node_context_11_23001_707987 : EJMOriginalGlobalDAGData.nodes 10 ⟨707987, by decide⟩ =
    .split (coordinate 11) (![⟨707900, by decide⟩,⟨642794, by decide⟩,⟨707947, by decide⟩,⟨707986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23001_707987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23001 ⟨707987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23001
    ⟨707987, by decide⟩ (by decide) (![⟨707900, by decide⟩,⟨642794, by decide⟩,⟨707947, by decide⟩,⟨707986, by decide⟩]) unmarked_context_11_23001_707987 node_context_11_23001_707987
  intro a
  fin_cases a
  · exact context_12_92004_707900
  · exact context_12_92005_642794
  · exact context_12_92006_707947
  · exact context_12_92007_707986

theorem selected_cut_28039 : selected 9 ⟨708029, by decide⟩
    (prefixPartial 12 92008) = some ⟨12, 2, 0, 708029, 92008, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_92008_708029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92008 ⟨708029, by decide⟩ :=
  accepted_of_selected 12 92008 ⟨708029, by decide⟩ ⟨12, 2, 0, 708029, 92008, 2977, 65536⟩
    (by decide) selected_cut_28039

theorem selected_cut_28040 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 368036) = some ⟨13, 1, 0, 3444, 368036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_368036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 368036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 368036, 1, 16384⟩
    (by decide) selected_cut_28040

theorem selected_cut_28041 : selected 8 ⟨708053, by decide⟩
    (prefixPartial 13 368037) = some ⟨13, 2, 0, 708053, 368037, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_368037_708053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368037 ⟨708053, by decide⟩ :=
  accepted_of_selected 13 368037 ⟨708053, by decide⟩ ⟨13, 2, 0, 708053, 368037, 1121, 16384⟩
    (by decide) selected_cut_28041

theorem selected_cut_28042 : selected 8 ⟨708086, by decide⟩
    (prefixPartial 13 368038) = some ⟨13, 2, 0, 708086, 368038, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_368038_708086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368038 ⟨708086, by decide⟩ :=
  accepted_of_selected 13 368038 ⟨708086, by decide⟩ ⟨13, 2, 0, 708086, 368038, 2225, 16384⟩
    (by decide) selected_cut_28042

theorem selected_cut_28043 : selected 8 ⟨708110, by decide⟩
    (prefixPartial 13 368039) = some ⟨13, 2, 0, 708110, 368039, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_368039_708110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368039 ⟨708110, by decide⟩ :=
  accepted_of_selected 13 368039 ⟨708110, by decide⟩ ⟨13, 2, 0, 708110, 368039, 1225, 16384⟩
    (by decide) selected_cut_28043

theorem unmarked_context_12_92009_708111 : frontier 9 ⟨708111, by decide⟩
    (prefixCache 12 92009) (prefixPartial 12 92009) = false := by
  decide +kernel

theorem node_context_12_92009_708111 : EJMOriginalGlobalDAGData.nodes 9 ⟨708111, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨708053, by decide⟩,⟨708086, by decide⟩,⟨708110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92009_708111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92009 ⟨708111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92009
    ⟨708111, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨708053, by decide⟩,⟨708086, by decide⟩,⟨708110, by decide⟩]) unmarked_context_12_92009_708111 node_context_12_92009_708111
  intro a
  fin_cases a
  · exact context_13_368036_3444
  · exact context_13_368037_708053
  · exact context_13_368038_708086
  · exact context_13_368039_708110

theorem selected_cut_28044 : selected 9 ⟨708150, by decide⟩
    (prefixPartial 12 92010) = some ⟨12, 2, 0, 708150, 92010, 2845, 65536⟩ := by
  decide +kernel

theorem context_12_92010_708150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92010 ⟨708150, by decide⟩ :=
  accepted_of_selected 12 92010 ⟨708150, by decide⟩ ⟨12, 2, 0, 708150, 92010, 2845, 65536⟩
    (by decide) selected_cut_28044

theorem selected_cut_28045 : selected 9 ⟨708187, by decide⟩
    (prefixPartial 12 92011) = some ⟨12, 2, 0, 708187, 92011, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_92011_708187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92011 ⟨708187, by decide⟩ :=
  accepted_of_selected 12 92011 ⟨708187, by decide⟩ ⟨12, 2, 0, 708187, 92011, 2509, 65536⟩
    (by decide) selected_cut_28045

theorem unmarked_context_11_23002_708188 : frontier 10 ⟨708188, by decide⟩
    (prefixCache 11 23002) (prefixPartial 11 23002) = false := by
  decide +kernel

theorem node_context_11_23002_708188 : EJMOriginalGlobalDAGData.nodes 10 ⟨708188, by decide⟩ =
    .split (coordinate 11) (![⟨708029, by decide⟩,⟨708111, by decide⟩,⟨708150, by decide⟩,⟨708187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23002_708188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23002 ⟨708188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23002
    ⟨708188, by decide⟩ (by decide) (![⟨708029, by decide⟩,⟨708111, by decide⟩,⟨708150, by decide⟩,⟨708187, by decide⟩]) unmarked_context_11_23002_708188 node_context_11_23002_708188
  intro a
  fin_cases a
  · exact context_12_92008_708029
  · exact context_12_92009_708111
  · exact context_12_92010_708150
  · exact context_12_92011_708187

theorem selected_cut_28046 : selected 9 ⟨708222, by decide⟩
    (prefixPartial 12 92012) = some ⟨12, 2, 0, 708222, 92012, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_92012_708222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92012 ⟨708222, by decide⟩ :=
  accepted_of_selected 12 92012 ⟨708222, by decide⟩ ⟨12, 2, 0, 708222, 92012, 2457, 65536⟩
    (by decide) selected_cut_28046

theorem selected_cut_28047 : selected 9 ⟨708280, by decide⟩
    (prefixPartial 12 92013) = some ⟨12, 2, 0, 708280, 92013, 3865, 65536⟩ := by
  decide +kernel

theorem context_12_92013_708280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92013 ⟨708280, by decide⟩ :=
  accepted_of_selected 12 92013 ⟨708280, by decide⟩ ⟨12, 2, 0, 708280, 92013, 3865, 65536⟩
    (by decide) selected_cut_28047

theorem selected_cut_28048 : selected 9 ⟨708315, by decide⟩
    (prefixPartial 12 92014) = some ⟨12, 2, 0, 708315, 92014, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_92014_708315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92014 ⟨708315, by decide⟩ :=
  accepted_of_selected 12 92014 ⟨708315, by decide⟩ ⟨12, 2, 0, 708315, 92014, 2425, 65536⟩
    (by decide) selected_cut_28048

theorem selected_cut_28049 : selected 9 ⟨708386, by decide⟩
    (prefixPartial 12 92015) = some ⟨12, 2, 0, 708386, 92015, 1861, 65536⟩ := by
  decide +kernel

theorem context_12_92015_708386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92015 ⟨708386, by decide⟩ :=
  accepted_of_selected 12 92015 ⟨708386, by decide⟩ ⟨12, 2, 0, 708386, 92015, 1861, 65536⟩
    (by decide) selected_cut_28049

theorem unmarked_context_11_23003_708387 : frontier 10 ⟨708387, by decide⟩
    (prefixCache 11 23003) (prefixPartial 11 23003) = false := by
  decide +kernel

theorem node_context_11_23003_708387 : EJMOriginalGlobalDAGData.nodes 10 ⟨708387, by decide⟩ =
    .split (coordinate 11) (![⟨708222, by decide⟩,⟨708280, by decide⟩,⟨708315, by decide⟩,⟨708386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23003_708387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23003 ⟨708387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23003
    ⟨708387, by decide⟩ (by decide) (![⟨708222, by decide⟩,⟨708280, by decide⟩,⟨708315, by decide⟩,⟨708386, by decide⟩]) unmarked_context_11_23003_708387 node_context_11_23003_708387
  intro a
  fin_cases a
  · exact context_12_92012_708222
  · exact context_12_92013_708280
  · exact context_12_92014_708315
  · exact context_12_92015_708386

theorem unmarked_context_10_5750_708388 : frontier 11 ⟨708388, by decide⟩
    (prefixCache 10 5750) (prefixPartial 10 5750) = false := by
  decide +kernel

theorem node_context_10_5750_708388 : EJMOriginalGlobalDAGData.nodes 11 ⟨708388, by decide⟩ =
    .split (coordinate 10) (![⟨707860, by decide⟩,⟨707987, by decide⟩,⟨708188, by decide⟩,⟨708387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5750_708388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5750 ⟨708388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5750
    ⟨708388, by decide⟩ (by decide) (![⟨707860, by decide⟩,⟨707987, by decide⟩,⟨708188, by decide⟩,⟨708387, by decide⟩]) unmarked_context_10_5750_708388 node_context_10_5750_708388
  intro a
  fin_cases a
  · exact context_11_23000_707860
  · exact context_11_23001_707987
  · exact context_11_23002_708188
  · exact context_11_23003_708387

theorem selected_cut_28050 : selected 9 ⟨708429, by decide⟩
    (prefixPartial 12 92016) = some ⟨12, 2, 0, 708429, 92016, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_92016_708429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92016 ⟨708429, by decide⟩ :=
  accepted_of_selected 12 92016 ⟨708429, by decide⟩ ⟨12, 2, 0, 708429, 92016, 3289, 65536⟩
    (by decide) selected_cut_28050

theorem selected_cut_28051 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 368068) = some ⟨13, 1, 0, 3444, 368068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_368068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 368068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 368068, 1, 16384⟩
    (by decide) selected_cut_28051

theorem selected_cut_28052 : selected 8 ⟨708454, by decide⟩
    (prefixPartial 13 368069) = some ⟨13, 2, 0, 708454, 368069, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_368069_708454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368069 ⟨708454, by decide⟩ :=
  accepted_of_selected 13 368069 ⟨708454, by decide⟩ ⟨13, 2, 0, 708454, 368069, 1117, 16384⟩
    (by decide) selected_cut_28052

theorem selected_cut_28053 : selected 8 ⟨708503, by decide⟩
    (prefixPartial 13 368070) = some ⟨13, 2, 0, 708503, 368070, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_368070_708503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368070 ⟨708503, by decide⟩ :=
  accepted_of_selected 13 368070 ⟨708503, by decide⟩ ⟨13, 2, 0, 708503, 368070, 2565, 16384⟩
    (by decide) selected_cut_28053

theorem selected_cut_28054 : selected 8 ⟨708519, by decide⟩
    (prefixPartial 13 368071) = some ⟨13, 2, 0, 708519, 368071, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_368071_708519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368071 ⟨708519, by decide⟩ :=
  accepted_of_selected 13 368071 ⟨708519, by decide⟩ ⟨13, 2, 0, 708519, 368071, 1025, 16384⟩
    (by decide) selected_cut_28054

theorem unmarked_context_12_92017_708520 : frontier 9 ⟨708520, by decide⟩
    (prefixCache 12 92017) (prefixPartial 12 92017) = false := by
  decide +kernel

theorem node_context_12_92017_708520 : EJMOriginalGlobalDAGData.nodes 9 ⟨708520, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨708454, by decide⟩,⟨708503, by decide⟩,⟨708519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92017_708520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92017 ⟨708520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92017
    ⟨708520, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨708454, by decide⟩,⟨708503, by decide⟩,⟨708519, by decide⟩]) unmarked_context_12_92017_708520 node_context_12_92017_708520
  intro a
  fin_cases a
  · exact context_13_368068_3444
  · exact context_13_368069_708454
  · exact context_13_368070_708503
  · exact context_13_368071_708519

theorem selected_cut_28055 : selected 9 ⟨708560, by decide⟩
    (prefixPartial 12 92018) = some ⟨12, 2, 0, 708560, 92018, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_92018_708560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92018 ⟨708560, by decide⟩ :=
  accepted_of_selected 12 92018 ⟨708560, by decide⟩ ⟨12, 2, 0, 708560, 92018, 3141, 65536⟩
    (by decide) selected_cut_28055

theorem selected_cut_28056 : selected 9 ⟨708602, by decide⟩
    (prefixPartial 12 92019) = some ⟨12, 2, 0, 708602, 92019, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_92019_708602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92019 ⟨708602, by decide⟩ :=
  accepted_of_selected 12 92019 ⟨708602, by decide⟩ ⟨12, 2, 0, 708602, 92019, 3077, 65536⟩
    (by decide) selected_cut_28056

theorem unmarked_context_11_23004_708603 : frontier 10 ⟨708603, by decide⟩
    (prefixCache 11 23004) (prefixPartial 11 23004) = false := by
  decide +kernel

theorem node_context_11_23004_708603 : EJMOriginalGlobalDAGData.nodes 10 ⟨708603, by decide⟩ =
    .split (coordinate 11) (![⟨708429, by decide⟩,⟨708520, by decide⟩,⟨708560, by decide⟩,⟨708602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23004_708603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23004 ⟨708603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23004
    ⟨708603, by decide⟩ (by decide) (![⟨708429, by decide⟩,⟨708520, by decide⟩,⟨708560, by decide⟩,⟨708602, by decide⟩]) unmarked_context_11_23004_708603 node_context_11_23004_708603
  intro a
  fin_cases a
  · exact context_12_92016_708429
  · exact context_12_92017_708520
  · exact context_12_92018_708560
  · exact context_12_92019_708602

theorem selected_cut_28057 : selected 9 ⟨708642, by decide⟩
    (prefixPartial 12 92020) = some ⟨12, 2, 0, 708642, 92020, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_92020_708642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92020 ⟨708642, by decide⟩ :=
  accepted_of_selected 12 92020 ⟨708642, by decide⟩ ⟨12, 2, 0, 708642, 92020, 2709, 65536⟩
    (by decide) selected_cut_28057

theorem selected_cut_28058 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 92021) = some ⟨12, 1, 0, 642794, 92021, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92021_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92021 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 92021 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 92021, 1, 65536⟩
    (by decide) selected_cut_28058

theorem selected_cut_28059 : selected 9 ⟨708678, by decide⟩
    (prefixPartial 12 92022) = some ⟨12, 2, 0, 708678, 92022, 2577, 65536⟩ := by
  decide +kernel

theorem context_12_92022_708678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92022 ⟨708678, by decide⟩ :=
  accepted_of_selected 12 92022 ⟨708678, by decide⟩ ⟨12, 2, 0, 708678, 92022, 2577, 65536⟩
    (by decide) selected_cut_28059

theorem selected_cut_28060 : selected 9 ⟨708710, by decide⟩
    (prefixPartial 12 92023) = some ⟨12, 2, 0, 708710, 92023, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_92023_708710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92023 ⟨708710, by decide⟩ :=
  accepted_of_selected 12 92023 ⟨708710, by decide⟩ ⟨12, 2, 0, 708710, 92023, 2585, 65536⟩
    (by decide) selected_cut_28060

theorem unmarked_context_11_23005_708711 : frontier 10 ⟨708711, by decide⟩
    (prefixCache 11 23005) (prefixPartial 11 23005) = false := by
  decide +kernel

theorem node_context_11_23005_708711 : EJMOriginalGlobalDAGData.nodes 10 ⟨708711, by decide⟩ =
    .split (coordinate 11) (![⟨708642, by decide⟩,⟨642794, by decide⟩,⟨708678, by decide⟩,⟨708710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23005_708711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23005 ⟨708711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23005
    ⟨708711, by decide⟩ (by decide) (![⟨708642, by decide⟩,⟨642794, by decide⟩,⟨708678, by decide⟩,⟨708710, by decide⟩]) unmarked_context_11_23005_708711 node_context_11_23005_708711
  intro a
  fin_cases a
  · exact context_12_92020_708642
  · exact context_12_92021_642794
  · exact context_12_92022_708678
  · exact context_12_92023_708710

theorem selected_cut_28061 : selected 9 ⟨708750, by decide⟩
    (prefixPartial 12 92024) = some ⟨12, 2, 0, 708750, 92024, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_92024_708750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92024 ⟨708750, by decide⟩ :=
  accepted_of_selected 12 92024 ⟨708750, by decide⟩ ⟨12, 2, 0, 708750, 92024, 3041, 65536⟩
    (by decide) selected_cut_28061

theorem selected_cut_28062 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 368100) = some ⟨13, 1, 0, 3444, 368100, 1, 16384⟩ := by
  decide +kernel

theorem context_13_368100_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368100 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 368100 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 368100, 1, 16384⟩
    (by decide) selected_cut_28062

theorem selected_cut_28063 : selected 8 ⟨708761, by decide⟩
    (prefixPartial 13 368101) = some ⟨13, 2, 0, 708761, 368101, 457, 16384⟩ := by
  decide +kernel

theorem context_13_368101_708761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368101 ⟨708761, by decide⟩ :=
  accepted_of_selected 13 368101 ⟨708761, by decide⟩ ⟨13, 2, 0, 708761, 368101, 457, 16384⟩
    (by decide) selected_cut_28063

theorem selected_cut_28064 : selected 8 ⟨708817, by decide⟩
    (prefixPartial 13 368102) = some ⟨13, 2, 0, 708817, 368102, 2609, 16384⟩ := by
  decide +kernel

theorem context_13_368102_708817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368102 ⟨708817, by decide⟩ :=
  accepted_of_selected 13 368102 ⟨708817, by decide⟩ ⟨13, 2, 0, 708817, 368102, 2609, 16384⟩
    (by decide) selected_cut_28064

theorem selected_cut_28065 : selected 8 ⟨708843, by decide⟩
    (prefixPartial 13 368103) = some ⟨13, 2, 0, 708843, 368103, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_368103_708843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368103 ⟨708843, by decide⟩ :=
  accepted_of_selected 13 368103 ⟨708843, by decide⟩ ⟨13, 2, 0, 708843, 368103, 1277, 16384⟩
    (by decide) selected_cut_28065

theorem unmarked_context_12_92025_708844 : frontier 9 ⟨708844, by decide⟩
    (prefixCache 12 92025) (prefixPartial 12 92025) = false := by
  decide +kernel

theorem node_context_12_92025_708844 : EJMOriginalGlobalDAGData.nodes 9 ⟨708844, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨708761, by decide⟩,⟨708817, by decide⟩,⟨708843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92025_708844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92025 ⟨708844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92025
    ⟨708844, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨708761, by decide⟩,⟨708817, by decide⟩,⟨708843, by decide⟩]) unmarked_context_12_92025_708844 node_context_12_92025_708844
  intro a
  fin_cases a
  · exact context_13_368100_3444
  · exact context_13_368101_708761
  · exact context_13_368102_708817
  · exact context_13_368103_708843

theorem selected_cut_28066 : selected 9 ⟨708879, by decide⟩
    (prefixPartial 12 92026) = some ⟨12, 2, 0, 708879, 92026, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_92026_708879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92026 ⟨708879, by decide⟩ :=
  accepted_of_selected 12 92026 ⟨708879, by decide⟩ ⟨12, 2, 0, 708879, 92026, 2669, 65536⟩
    (by decide) selected_cut_28066

theorem selected_cut_28067 : selected 9 ⟨708910, by decide⟩
    (prefixPartial 12 92027) = some ⟨12, 2, 0, 708910, 92027, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_92027_708910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92027 ⟨708910, by decide⟩ :=
  accepted_of_selected 12 92027 ⟨708910, by decide⟩ ⟨12, 2, 0, 708910, 92027, 2721, 65536⟩
    (by decide) selected_cut_28067

theorem unmarked_context_11_23006_708911 : frontier 10 ⟨708911, by decide⟩
    (prefixCache 11 23006) (prefixPartial 11 23006) = false := by
  decide +kernel

theorem node_context_11_23006_708911 : EJMOriginalGlobalDAGData.nodes 10 ⟨708911, by decide⟩ =
    .split (coordinate 11) (![⟨708750, by decide⟩,⟨708844, by decide⟩,⟨708879, by decide⟩,⟨708910, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23006_708911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23006 ⟨708911, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23006
    ⟨708911, by decide⟩ (by decide) (![⟨708750, by decide⟩,⟨708844, by decide⟩,⟨708879, by decide⟩,⟨708910, by decide⟩]) unmarked_context_11_23006_708911 node_context_11_23006_708911
  intro a
  fin_cases a
  · exact context_12_92024_708750
  · exact context_12_92025_708844
  · exact context_12_92026_708879
  · exact context_12_92027_708910

theorem selected_cut_28068 : selected 9 ⟨708942, by decide⟩
    (prefixPartial 12 92028) = some ⟨12, 2, 0, 708942, 92028, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_92028_708942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92028 ⟨708942, by decide⟩ :=
  accepted_of_selected 12 92028 ⟨708942, by decide⟩ ⟨12, 2, 0, 708942, 92028, 2233, 65536⟩
    (by decide) selected_cut_28068

theorem selected_cut_28069 : selected 9 ⟨299350, by decide⟩
    (prefixPartial 12 92029) = some ⟨12, 1, 0, 299350, 92029, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92029_299350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92029 ⟨299350, by decide⟩ :=
  accepted_of_selected 12 92029 ⟨299350, by decide⟩ ⟨12, 1, 0, 299350, 92029, 1, 65536⟩
    (by decide) selected_cut_28069

theorem selected_cut_28070 : selected 9 ⟨708967, by decide⟩
    (prefixPartial 12 92030) = some ⟨12, 2, 0, 708967, 92030, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_92030_708967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92030 ⟨708967, by decide⟩ :=
  accepted_of_selected 12 92030 ⟨708967, by decide⟩ ⟨12, 2, 0, 708967, 92030, 1929, 65536⟩
    (by decide) selected_cut_28070

theorem selected_cut_28071 : selected 9 ⟨512556, by decide⟩
    (prefixPartial 12 92031) = some ⟨12, 1, 0, 512556, 92031, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92031_512556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92031 ⟨512556, by decide⟩ :=
  accepted_of_selected 12 92031 ⟨512556, by decide⟩ ⟨12, 1, 0, 512556, 92031, 1, 65536⟩
    (by decide) selected_cut_28071

theorem unmarked_context_11_23007_708968 : frontier 10 ⟨708968, by decide⟩
    (prefixCache 11 23007) (prefixPartial 11 23007) = false := by
  decide +kernel

theorem node_context_11_23007_708968 : EJMOriginalGlobalDAGData.nodes 10 ⟨708968, by decide⟩ =
    .split (coordinate 11) (![⟨708942, by decide⟩,⟨299350, by decide⟩,⟨708967, by decide⟩,⟨512556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23007_708968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23007 ⟨708968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23007
    ⟨708968, by decide⟩ (by decide) (![⟨708942, by decide⟩,⟨299350, by decide⟩,⟨708967, by decide⟩,⟨512556, by decide⟩]) unmarked_context_11_23007_708968 node_context_11_23007_708968
  intro a
  fin_cases a
  · exact context_12_92028_708942
  · exact context_12_92029_299350
  · exact context_12_92030_708967
  · exact context_12_92031_512556

theorem unmarked_context_10_5751_708969 : frontier 11 ⟨708969, by decide⟩
    (prefixCache 10 5751) (prefixPartial 10 5751) = false := by
  decide +kernel

theorem node_context_10_5751_708969 : EJMOriginalGlobalDAGData.nodes 11 ⟨708969, by decide⟩ =
    .split (coordinate 10) (![⟨708603, by decide⟩,⟨708711, by decide⟩,⟨708911, by decide⟩,⟨708968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5751_708969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5751 ⟨708969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5751
    ⟨708969, by decide⟩ (by decide) (![⟨708603, by decide⟩,⟨708711, by decide⟩,⟨708911, by decide⟩,⟨708968, by decide⟩]) unmarked_context_10_5751_708969 node_context_10_5751_708969
  intro a
  fin_cases a
  · exact context_11_23004_708603
  · exact context_11_23005_708711
  · exact context_11_23006_708911
  · exact context_11_23007_708968

theorem unmarked_context_9_1437_708970 : frontier 12 ⟨708970, by decide⟩
    (prefixCache 9 1437) (prefixPartial 9 1437) = false := by
  decide +kernel

theorem node_context_9_1437_708970 : EJMOriginalGlobalDAGData.nodes 12 ⟨708970, by decide⟩ =
    .split (coordinate 9) (![⟨707288, by decide⟩,⟨707641, by decide⟩,⟨708388, by decide⟩,⟨708969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1437_708970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1437 ⟨708970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1437
    ⟨708970, by decide⟩ (by decide) (![⟨707288, by decide⟩,⟨707641, by decide⟩,⟨708388, by decide⟩,⟨708969, by decide⟩]) unmarked_context_9_1437_708970 node_context_9_1437_708970
  intro a
  fin_cases a
  · exact context_10_5748_707288
  · exact context_10_5749_707641
  · exact context_10_5750_708388
  · exact context_10_5751_708969

theorem selected_cut_28072 : selected 9 ⟨708995, by decide⟩
    (prefixPartial 12 92032) = some ⟨12, 2, 0, 708995, 92032, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_92032_708995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92032 ⟨708995, by decide⟩ :=
  accepted_of_selected 12 92032 ⟨708995, by decide⟩ ⟨12, 2, 0, 708995, 92032, 2077, 65536⟩
    (by decide) selected_cut_28072

theorem selected_cut_28073 : selected 9 ⟨709022, by decide⟩
    (prefixPartial 12 92033) = some ⟨12, 2, 0, 709022, 92033, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_92033_709022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92033 ⟨709022, by decide⟩ :=
  accepted_of_selected 12 92033 ⟨709022, by decide⟩ ⟨12, 2, 0, 709022, 92033, 2045, 65536⟩
    (by decide) selected_cut_28073

theorem selected_cut_28074 : selected 9 ⟨709047, by decide⟩
    (prefixPartial 12 92034) = some ⟨12, 2, 0, 709047, 92034, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_92034_709047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92034 ⟨709047, by decide⟩ :=
  accepted_of_selected 12 92034 ⟨709047, by decide⟩ ⟨12, 2, 0, 709047, 92034, 1997, 65536⟩
    (by decide) selected_cut_28074

theorem selected_cut_28075 : selected 9 ⟨709075, by decide⟩
    (prefixPartial 12 92035) = some ⟨12, 2, 0, 709075, 92035, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_92035_709075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92035 ⟨709075, by decide⟩ :=
  accepted_of_selected 12 92035 ⟨709075, by decide⟩ ⟨12, 2, 0, 709075, 92035, 2013, 65536⟩
    (by decide) selected_cut_28075

theorem unmarked_context_11_23008_709076 : frontier 10 ⟨709076, by decide⟩
    (prefixCache 11 23008) (prefixPartial 11 23008) = false := by
  decide +kernel

theorem node_context_11_23008_709076 : EJMOriginalGlobalDAGData.nodes 10 ⟨709076, by decide⟩ =
    .split (coordinate 11) (![⟨708995, by decide⟩,⟨709022, by decide⟩,⟨709047, by decide⟩,⟨709075, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23008_709076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23008 ⟨709076, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23008
    ⟨709076, by decide⟩ (by decide) (![⟨708995, by decide⟩,⟨709022, by decide⟩,⟨709047, by decide⟩,⟨709075, by decide⟩]) unmarked_context_11_23008_709076 node_context_11_23008_709076
  intro a
  fin_cases a
  · exact context_12_92032_708995
  · exact context_12_92033_709022
  · exact context_12_92034_709047
  · exact context_12_92035_709075

theorem selected_cut_28076 : selected 9 ⟨709096, by decide⟩
    (prefixPartial 12 92036) = some ⟨12, 2, 0, 709096, 92036, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_92036_709096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92036 ⟨709096, by decide⟩ :=
  accepted_of_selected 12 92036 ⟨709096, by decide⟩ ⟨12, 2, 0, 709096, 92036, 2145, 65536⟩
    (by decide) selected_cut_28076

theorem selected_cut_28077 : selected 9 ⟨709122, by decide⟩
    (prefixPartial 12 92037) = some ⟨12, 2, 0, 709122, 92037, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_92037_709122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92037 ⟨709122, by decide⟩ :=
  accepted_of_selected 12 92037 ⟨709122, by decide⟩ ⟨12, 2, 0, 709122, 92037, 1937, 65536⟩
    (by decide) selected_cut_28077

theorem selected_cut_28078 : selected 9 ⟨709146, by decide⟩
    (prefixPartial 12 92038) = some ⟨12, 2, 0, 709146, 92038, 1921, 65536⟩ := by
  decide +kernel

theorem context_12_92038_709146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92038 ⟨709146, by decide⟩ :=
  accepted_of_selected 12 92038 ⟨709146, by decide⟩ ⟨12, 2, 0, 709146, 92038, 1921, 65536⟩
    (by decide) selected_cut_28078

theorem selected_cut_28079 : selected 9 ⟨709169, by decide⟩
    (prefixPartial 12 92039) = some ⟨12, 2, 0, 709169, 92039, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_92039_709169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92039 ⟨709169, by decide⟩ :=
  accepted_of_selected 12 92039 ⟨709169, by decide⟩ ⟨12, 2, 0, 709169, 92039, 2133, 65536⟩
    (by decide) selected_cut_28079

theorem unmarked_context_11_23009_709170 : frontier 10 ⟨709170, by decide⟩
    (prefixCache 11 23009) (prefixPartial 11 23009) = false := by
  decide +kernel

theorem node_context_11_23009_709170 : EJMOriginalGlobalDAGData.nodes 10 ⟨709170, by decide⟩ =
    .split (coordinate 11) (![⟨709096, by decide⟩,⟨709122, by decide⟩,⟨709146, by decide⟩,⟨709169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23009_709170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23009 ⟨709170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23009
    ⟨709170, by decide⟩ (by decide) (![⟨709096, by decide⟩,⟨709122, by decide⟩,⟨709146, by decide⟩,⟨709169, by decide⟩]) unmarked_context_11_23009_709170 node_context_11_23009_709170
  intro a
  fin_cases a
  · exact context_12_92036_709096
  · exact context_12_92037_709122
  · exact context_12_92038_709146
  · exact context_12_92039_709169

theorem selected_cut_28080 : selected 9 ⟨709196, by decide⟩
    (prefixPartial 12 92040) = some ⟨12, 2, 0, 709196, 92040, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_92040_709196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92040 ⟨709196, by decide⟩ :=
  accepted_of_selected 12 92040 ⟨709196, by decide⟩ ⟨12, 2, 0, 709196, 92040, 2305, 65536⟩
    (by decide) selected_cut_28080

theorem selected_cut_28081 : selected 9 ⟨709228, by decide⟩
    (prefixPartial 12 92041) = some ⟨12, 2, 0, 709228, 92041, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_92041_709228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92041 ⟨709228, by decide⟩ :=
  accepted_of_selected 12 92041 ⟨709228, by decide⟩ ⟨12, 2, 0, 709228, 92041, 2233, 65536⟩
    (by decide) selected_cut_28081

theorem selected_cut_28082 : selected 9 ⟨709255, by decide⟩
    (prefixPartial 12 92042) = some ⟨12, 2, 0, 709255, 92042, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_92042_709255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92042 ⟨709255, by decide⟩ :=
  accepted_of_selected 12 92042 ⟨709255, by decide⟩ ⟨12, 2, 0, 709255, 92042, 2069, 65536⟩
    (by decide) selected_cut_28082

theorem selected_cut_28083 : selected 9 ⟨709291, by decide⟩
    (prefixPartial 12 92043) = some ⟨12, 2, 0, 709291, 92043, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_92043_709291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92043 ⟨709291, by decide⟩ :=
  accepted_of_selected 12 92043 ⟨709291, by decide⟩ ⟨12, 2, 0, 709291, 92043, 2141, 65536⟩
    (by decide) selected_cut_28083

theorem unmarked_context_11_23010_709292 : frontier 10 ⟨709292, by decide⟩
    (prefixCache 11 23010) (prefixPartial 11 23010) = false := by
  decide +kernel

theorem node_context_11_23010_709292 : EJMOriginalGlobalDAGData.nodes 10 ⟨709292, by decide⟩ =
    .split (coordinate 11) (![⟨709196, by decide⟩,⟨709228, by decide⟩,⟨709255, by decide⟩,⟨709291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23010_709292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23010 ⟨709292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23010
    ⟨709292, by decide⟩ (by decide) (![⟨709196, by decide⟩,⟨709228, by decide⟩,⟨709255, by decide⟩,⟨709291, by decide⟩]) unmarked_context_11_23010_709292 node_context_11_23010_709292
  intro a
  fin_cases a
  · exact context_12_92040_709196
  · exact context_12_92041_709228
  · exact context_12_92042_709255
  · exact context_12_92043_709291

theorem selected_cut_28084 : selected 9 ⟨709309, by decide⟩
    (prefixPartial 12 92044) = some ⟨12, 2, 0, 709309, 92044, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_92044_709309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92044 ⟨709309, by decide⟩ :=
  accepted_of_selected 12 92044 ⟨709309, by decide⟩ ⟨12, 2, 0, 709309, 92044, 1749, 65536⟩
    (by decide) selected_cut_28084

theorem selected_cut_28085 : selected 9 ⟨709331, by decide⟩
    (prefixPartial 12 92045) = some ⟨12, 2, 0, 709331, 92045, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_92045_709331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92045 ⟨709331, by decide⟩ :=
  accepted_of_selected 12 92045 ⟨709331, by decide⟩ ⟨12, 2, 0, 709331, 92045, 1725, 65536⟩
    (by decide) selected_cut_28085

theorem selected_cut_28086 : selected 9 ⟨709354, by decide⟩
    (prefixPartial 12 92046) = some ⟨12, 2, 0, 709354, 92046, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_92046_709354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92046 ⟨709354, by decide⟩ :=
  accepted_of_selected 12 92046 ⟨709354, by decide⟩ ⟨12, 2, 0, 709354, 92046, 1573, 65536⟩
    (by decide) selected_cut_28086

theorem selected_cut_28087 : selected 9 ⟨709392, by decide⟩
    (prefixPartial 12 92047) = some ⟨12, 2, 0, 709392, 92047, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_92047_709392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92047 ⟨709392, by decide⟩ :=
  accepted_of_selected 12 92047 ⟨709392, by decide⟩ ⟨12, 2, 0, 709392, 92047, 2669, 65536⟩
    (by decide) selected_cut_28087

theorem unmarked_context_11_23011_709393 : frontier 10 ⟨709393, by decide⟩
    (prefixCache 11 23011) (prefixPartial 11 23011) = false := by
  decide +kernel

theorem node_context_11_23011_709393 : EJMOriginalGlobalDAGData.nodes 10 ⟨709393, by decide⟩ =
    .split (coordinate 11) (![⟨709309, by decide⟩,⟨709331, by decide⟩,⟨709354, by decide⟩,⟨709392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23011_709393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23011 ⟨709393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23011
    ⟨709393, by decide⟩ (by decide) (![⟨709309, by decide⟩,⟨709331, by decide⟩,⟨709354, by decide⟩,⟨709392, by decide⟩]) unmarked_context_11_23011_709393 node_context_11_23011_709393
  intro a
  fin_cases a
  · exact context_12_92044_709309
  · exact context_12_92045_709331
  · exact context_12_92046_709354
  · exact context_12_92047_709392

theorem unmarked_context_10_5752_709394 : frontier 11 ⟨709394, by decide⟩
    (prefixCache 10 5752) (prefixPartial 10 5752) = false := by
  decide +kernel

theorem node_context_10_5752_709394 : EJMOriginalGlobalDAGData.nodes 11 ⟨709394, by decide⟩ =
    .split (coordinate 10) (![⟨709076, by decide⟩,⟨709170, by decide⟩,⟨709292, by decide⟩,⟨709393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5752_709394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5752 ⟨709394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5752
    ⟨709394, by decide⟩ (by decide) (![⟨709076, by decide⟩,⟨709170, by decide⟩,⟨709292, by decide⟩,⟨709393, by decide⟩]) unmarked_context_10_5752_709394 node_context_10_5752_709394
  intro a
  fin_cases a
  · exact context_11_23008_709076
  · exact context_11_23009_709170
  · exact context_11_23010_709292
  · exact context_11_23011_709393

theorem selected_cut_28088 : selected 9 ⟨709417, by decide⟩
    (prefixPartial 12 92048) = some ⟨12, 2, 0, 709417, 92048, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_92048_709417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92048 ⟨709417, by decide⟩ :=
  accepted_of_selected 12 92048 ⟨709417, by decide⟩ ⟨12, 2, 0, 709417, 92048, 1881, 65536⟩
    (by decide) selected_cut_28088

theorem selected_cut_28089 : selected 9 ⟨709438, by decide⟩
    (prefixPartial 12 92049) = some ⟨12, 2, 0, 709438, 92049, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_92049_709438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92049 ⟨709438, by decide⟩ :=
  accepted_of_selected 12 92049 ⟨709438, by decide⟩ ⟨12, 2, 0, 709438, 92049, 1837, 65536⟩
    (by decide) selected_cut_28089

theorem selected_cut_28090 : selected 9 ⟨709461, by decide⟩
    (prefixPartial 12 92050) = some ⟨12, 2, 0, 709461, 92050, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_92050_709461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92050 ⟨709461, by decide⟩ :=
  accepted_of_selected 12 92050 ⟨709461, by decide⟩ ⟨12, 2, 0, 709461, 92050, 2061, 65536⟩
    (by decide) selected_cut_28090

theorem selected_cut_28091 : selected 9 ⟨709484, by decide⟩
    (prefixPartial 12 92051) = some ⟨12, 2, 0, 709484, 92051, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_92051_709484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92051 ⟨709484, by decide⟩ :=
  accepted_of_selected 12 92051 ⟨709484, by decide⟩ ⟨12, 2, 0, 709484, 92051, 1745, 65536⟩
    (by decide) selected_cut_28091

theorem unmarked_context_11_23012_709485 : frontier 10 ⟨709485, by decide⟩
    (prefixCache 11 23012) (prefixPartial 11 23012) = false := by
  decide +kernel

theorem node_context_11_23012_709485 : EJMOriginalGlobalDAGData.nodes 10 ⟨709485, by decide⟩ =
    .split (coordinate 11) (![⟨709417, by decide⟩,⟨709438, by decide⟩,⟨709461, by decide⟩,⟨709484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23012_709485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23012 ⟨709485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23012
    ⟨709485, by decide⟩ (by decide) (![⟨709417, by decide⟩,⟨709438, by decide⟩,⟨709461, by decide⟩,⟨709484, by decide⟩]) unmarked_context_11_23012_709485 node_context_11_23012_709485
  intro a
  fin_cases a
  · exact context_12_92048_709417
  · exact context_12_92049_709438
  · exact context_12_92050_709461
  · exact context_12_92051_709484

theorem selected_cut_28092 : selected 9 ⟨709525, by decide⟩
    (prefixPartial 12 92052) = some ⟨12, 2, 0, 709525, 92052, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_92052_709525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92052 ⟨709525, by decide⟩ :=
  accepted_of_selected 12 92052 ⟨709525, by decide⟩ ⟨12, 2, 0, 709525, 92052, 2661, 65536⟩
    (by decide) selected_cut_28092

theorem selected_cut_28093 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 92053) = some ⟨12, 1, 0, 449506, 92053, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92053_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92053 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 92053 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 92053, 1, 65536⟩
    (by decide) selected_cut_28093

theorem selected_cut_28094 : selected 9 ⟨709563, by decide⟩
    (prefixPartial 12 92054) = some ⟨12, 2, 0, 709563, 92054, 2677, 65536⟩ := by
  decide +kernel

theorem context_12_92054_709563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92054 ⟨709563, by decide⟩ :=
  accepted_of_selected 12 92054 ⟨709563, by decide⟩ ⟨12, 2, 0, 709563, 92054, 2677, 65536⟩
    (by decide) selected_cut_28094

theorem selected_cut_28095 : selected 9 ⟨709590, by decide⟩
    (prefixPartial 12 92055) = some ⟨12, 2, 0, 709590, 92055, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_92055_709590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92055 ⟨709590, by decide⟩ :=
  accepted_of_selected 12 92055 ⟨709590, by decide⟩ ⟨12, 2, 0, 709590, 92055, 2489, 65536⟩
    (by decide) selected_cut_28095

theorem unmarked_context_11_23013_709591 : frontier 10 ⟨709591, by decide⟩
    (prefixCache 11 23013) (prefixPartial 11 23013) = false := by
  decide +kernel

theorem node_context_11_23013_709591 : EJMOriginalGlobalDAGData.nodes 10 ⟨709591, by decide⟩ =
    .split (coordinate 11) (![⟨709525, by decide⟩,⟨449506, by decide⟩,⟨709563, by decide⟩,⟨709590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23013_709591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23013 ⟨709591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23013
    ⟨709591, by decide⟩ (by decide) (![⟨709525, by decide⟩,⟨449506, by decide⟩,⟨709563, by decide⟩,⟨709590, by decide⟩]) unmarked_context_11_23013_709591 node_context_11_23013_709591
  intro a
  fin_cases a
  · exact context_12_92052_709525
  · exact context_12_92053_449506
  · exact context_12_92054_709563
  · exact context_12_92055_709590

theorem selected_cut_28096 : selected 9 ⟨709616, by decide⟩
    (prefixPartial 12 92056) = some ⟨12, 2, 0, 709616, 92056, 1949, 65536⟩ := by
  decide +kernel

theorem context_12_92056_709616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92056 ⟨709616, by decide⟩ :=
  accepted_of_selected 12 92056 ⟨709616, by decide⟩ ⟨12, 2, 0, 709616, 92056, 1949, 65536⟩
    (by decide) selected_cut_28096

theorem selected_cut_28097 : selected 9 ⟨709642, by decide⟩
    (prefixPartial 12 92057) = some ⟨12, 2, 0, 709642, 92057, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_92057_709642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92057 ⟨709642, by decide⟩ :=
  accepted_of_selected 12 92057 ⟨709642, by decide⟩ ⟨12, 2, 0, 709642, 92057, 1853, 65536⟩
    (by decide) selected_cut_28097

theorem selected_cut_28098 : selected 9 ⟨709665, by decide⟩
    (prefixPartial 12 92058) = some ⟨12, 2, 0, 709665, 92058, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_92058_709665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92058 ⟨709665, by decide⟩ :=
  accepted_of_selected 12 92058 ⟨709665, by decide⟩ ⟨12, 2, 0, 709665, 92058, 1853, 65536⟩
    (by decide) selected_cut_28098

theorem selected_cut_28099 : selected 9 ⟨709689, by decide⟩
    (prefixPartial 12 92059) = some ⟨12, 2, 0, 709689, 92059, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_92059_709689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92059 ⟨709689, by decide⟩ :=
  accepted_of_selected 12 92059 ⟨709689, by decide⟩ ⟨12, 2, 0, 709689, 92059, 1629, 65536⟩
    (by decide) selected_cut_28099

theorem unmarked_context_11_23014_709690 : frontier 10 ⟨709690, by decide⟩
    (prefixCache 11 23014) (prefixPartial 11 23014) = false := by
  decide +kernel

theorem node_context_11_23014_709690 : EJMOriginalGlobalDAGData.nodes 10 ⟨709690, by decide⟩ =
    .split (coordinate 11) (![⟨709616, by decide⟩,⟨709642, by decide⟩,⟨709665, by decide⟩,⟨709689, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23014_709690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23014 ⟨709690, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23014
    ⟨709690, by decide⟩ (by decide) (![⟨709616, by decide⟩,⟨709642, by decide⟩,⟨709665, by decide⟩,⟨709689, by decide⟩]) unmarked_context_11_23014_709690 node_context_11_23014_709690
  intro a
  fin_cases a
  · exact context_12_92056_709616
  · exact context_12_92057_709642
  · exact context_12_92058_709665
  · exact context_12_92059_709689

theorem selected_cut_28100 : selected 9 ⟨709706, by decide⟩
    (prefixPartial 12 92060) = some ⟨12, 2, 0, 709706, 92060, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_92060_709706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92060 ⟨709706, by decide⟩ :=
  accepted_of_selected 12 92060 ⟨709706, by decide⟩ ⟨12, 2, 0, 709706, 92060, 1437, 65536⟩
    (by decide) selected_cut_28100

theorem selected_cut_28101 : selected 9 ⟨709726, by decide⟩
    (prefixPartial 12 92061) = some ⟨12, 2, 0, 709726, 92061, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_92061_709726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92061 ⟨709726, by decide⟩ :=
  accepted_of_selected 12 92061 ⟨709726, by decide⟩ ⟨12, 2, 0, 709726, 92061, 1369, 65536⟩
    (by decide) selected_cut_28101

theorem selected_cut_28102 : selected 9 ⟨709747, by decide⟩
    (prefixPartial 12 92062) = some ⟨12, 2, 0, 709747, 92062, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_92062_709747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92062 ⟨709747, by decide⟩ :=
  accepted_of_selected 12 92062 ⟨709747, by decide⟩ ⟨12, 2, 0, 709747, 92062, 1449, 65536⟩
    (by decide) selected_cut_28102

theorem selected_cut_28103 : selected 9 ⟨709776, by decide⟩
    (prefixPartial 12 92063) = some ⟨12, 2, 0, 709776, 92063, 601, 65536⟩ := by
  decide +kernel

theorem context_12_92063_709776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92063 ⟨709776, by decide⟩ :=
  accepted_of_selected 12 92063 ⟨709776, by decide⟩ ⟨12, 2, 0, 709776, 92063, 601, 65536⟩
    (by decide) selected_cut_28103

theorem unmarked_context_11_23015_709777 : frontier 10 ⟨709777, by decide⟩
    (prefixCache 11 23015) (prefixPartial 11 23015) = false := by
  decide +kernel

theorem node_context_11_23015_709777 : EJMOriginalGlobalDAGData.nodes 10 ⟨709777, by decide⟩ =
    .split (coordinate 11) (![⟨709706, by decide⟩,⟨709726, by decide⟩,⟨709747, by decide⟩,⟨709776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23015_709777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23015 ⟨709777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23015
    ⟨709777, by decide⟩ (by decide) (![⟨709706, by decide⟩,⟨709726, by decide⟩,⟨709747, by decide⟩,⟨709776, by decide⟩]) unmarked_context_11_23015_709777 node_context_11_23015_709777
  intro a
  fin_cases a
  · exact context_12_92060_709706
  · exact context_12_92061_709726
  · exact context_12_92062_709747
  · exact context_12_92063_709776

theorem unmarked_context_10_5753_709778 : frontier 11 ⟨709778, by decide⟩
    (prefixCache 10 5753) (prefixPartial 10 5753) = false := by
  decide +kernel

theorem node_context_10_5753_709778 : EJMOriginalGlobalDAGData.nodes 11 ⟨709778, by decide⟩ =
    .split (coordinate 10) (![⟨709485, by decide⟩,⟨709591, by decide⟩,⟨709690, by decide⟩,⟨709777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5753_709778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5753 ⟨709778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5753
    ⟨709778, by decide⟩ (by decide) (![⟨709485, by decide⟩,⟨709591, by decide⟩,⟨709690, by decide⟩,⟨709777, by decide⟩]) unmarked_context_10_5753_709778 node_context_10_5753_709778
  intro a
  fin_cases a
  · exact context_11_23012_709485
  · exact context_11_23013_709591
  · exact context_11_23014_709690
  · exact context_11_23015_709777

theorem selected_cut_28104 : selected 9 ⟨709794, by decide⟩
    (prefixPartial 12 92064) = some ⟨12, 2, 0, 709794, 92064, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_92064_709794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92064 ⟨709794, by decide⟩ :=
  accepted_of_selected 12 92064 ⟨709794, by decide⟩ ⟨12, 2, 0, 709794, 92064, 1353, 65536⟩
    (by decide) selected_cut_28104

theorem selected_cut_28105 : selected 9 ⟨709810, by decide⟩
    (prefixPartial 12 92065) = some ⟨12, 2, 0, 709810, 92065, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_92065_709810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92065 ⟨709810, by decide⟩ :=
  accepted_of_selected 12 92065 ⟨709810, by decide⟩ ⟨12, 2, 0, 709810, 92065, 1333, 65536⟩
    (by decide) selected_cut_28105

theorem selected_cut_28106 : selected 9 ⟨709829, by decide⟩
    (prefixPartial 12 92066) = some ⟨12, 2, 0, 709829, 92066, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_92066_709829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92066 ⟨709829, by decide⟩ :=
  accepted_of_selected 12 92066 ⟨709829, by decide⟩ ⟨12, 2, 0, 709829, 92066, 1329, 65536⟩
    (by decide) selected_cut_28106

theorem selected_cut_28107 : selected 9 ⟨709842, by decide⟩
    (prefixPartial 12 92067) = some ⟨12, 2, 0, 709842, 92067, 1125, 65536⟩ := by
  decide +kernel

theorem context_12_92067_709842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92067 ⟨709842, by decide⟩ :=
  accepted_of_selected 12 92067 ⟨709842, by decide⟩ ⟨12, 2, 0, 709842, 92067, 1125, 65536⟩
    (by decide) selected_cut_28107

theorem unmarked_context_11_23016_709843 : frontier 10 ⟨709843, by decide⟩
    (prefixCache 11 23016) (prefixPartial 11 23016) = false := by
  decide +kernel

theorem node_context_11_23016_709843 : EJMOriginalGlobalDAGData.nodes 10 ⟨709843, by decide⟩ =
    .split (coordinate 11) (![⟨709794, by decide⟩,⟨709810, by decide⟩,⟨709829, by decide⟩,⟨709842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23016_709843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23016 ⟨709843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23016
    ⟨709843, by decide⟩ (by decide) (![⟨709794, by decide⟩,⟨709810, by decide⟩,⟨709829, by decide⟩,⟨709842, by decide⟩]) unmarked_context_11_23016_709843 node_context_11_23016_709843
  intro a
  fin_cases a
  · exact context_12_92064_709794
  · exact context_12_92065_709810
  · exact context_12_92066_709829
  · exact context_12_92067_709842

theorem selected_cut_28108 : selected 9 ⟨709855, by decide⟩
    (prefixPartial 12 92068) = some ⟨12, 2, 0, 709855, 92068, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_92068_709855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92068 ⟨709855, by decide⟩ :=
  accepted_of_selected 12 92068 ⟨709855, by decide⟩ ⟨12, 2, 0, 709855, 92068, 1297, 65536⟩
    (by decide) selected_cut_28108

theorem selected_cut_28109 : selected 9 ⟨709868, by decide⟩
    (prefixPartial 12 92069) = some ⟨12, 2, 0, 709868, 92069, 1209, 65536⟩ := by
  decide +kernel

theorem context_12_92069_709868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92069 ⟨709868, by decide⟩ :=
  accepted_of_selected 12 92069 ⟨709868, by decide⟩ ⟨12, 2, 0, 709868, 92069, 1209, 65536⟩
    (by decide) selected_cut_28109

theorem selected_cut_28110 : selected 9 ⟨709886, by decide⟩
    (prefixPartial 12 92070) = some ⟨12, 2, 0, 709886, 92070, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_92070_709886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92070 ⟨709886, by decide⟩ :=
  accepted_of_selected 12 92070 ⟨709886, by decide⟩ ⟨12, 2, 0, 709886, 92070, 1285, 65536⟩
    (by decide) selected_cut_28110

theorem selected_cut_28111 : selected 9 ⟨709897, by decide⟩
    (prefixPartial 12 92071) = some ⟨12, 2, 0, 709897, 92071, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_92071_709897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92071 ⟨709897, by decide⟩ :=
  accepted_of_selected 12 92071 ⟨709897, by decide⟩ ⟨12, 2, 0, 709897, 92071, 1121, 65536⟩
    (by decide) selected_cut_28111

theorem unmarked_context_11_23017_709898 : frontier 10 ⟨709898, by decide⟩
    (prefixCache 11 23017) (prefixPartial 11 23017) = false := by
  decide +kernel

theorem node_context_11_23017_709898 : EJMOriginalGlobalDAGData.nodes 10 ⟨709898, by decide⟩ =
    .split (coordinate 11) (![⟨709855, by decide⟩,⟨709868, by decide⟩,⟨709886, by decide⟩,⟨709897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23017_709898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23017 ⟨709898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23017
    ⟨709898, by decide⟩ (by decide) (![⟨709855, by decide⟩,⟨709868, by decide⟩,⟨709886, by decide⟩,⟨709897, by decide⟩]) unmarked_context_11_23017_709898 node_context_11_23017_709898
  intro a
  fin_cases a
  · exact context_12_92068_709855
  · exact context_12_92069_709868
  · exact context_12_92070_709886
  · exact context_12_92071_709897

theorem selected_cut_28112 : selected 9 ⟨709915, by decide⟩
    (prefixPartial 12 92072) = some ⟨12, 2, 0, 709915, 92072, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_92072_709915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92072 ⟨709915, by decide⟩ :=
  accepted_of_selected 12 92072 ⟨709915, by decide⟩ ⟨12, 2, 0, 709915, 92072, 1413, 65536⟩
    (by decide) selected_cut_28112

theorem selected_cut_28113 : selected 9 ⟨709934, by decide⟩
    (prefixPartial 12 92073) = some ⟨12, 2, 0, 709934, 92073, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_92073_709934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92073 ⟨709934, by decide⟩ :=
  accepted_of_selected 12 92073 ⟨709934, by decide⟩ ⟨12, 2, 0, 709934, 92073, 1373, 65536⟩
    (by decide) selected_cut_28113

theorem selected_cut_28114 : selected 9 ⟨709953, by decide⟩
    (prefixPartial 12 92074) = some ⟨12, 2, 0, 709953, 92074, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_92074_709953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92074 ⟨709953, by decide⟩ :=
  accepted_of_selected 12 92074 ⟨709953, by decide⟩ ⟨12, 2, 0, 709953, 92074, 1293, 65536⟩
    (by decide) selected_cut_28114

theorem selected_cut_28115 : selected 9 ⟨709967, by decide⟩
    (prefixPartial 12 92075) = some ⟨12, 2, 0, 709967, 92075, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_92075_709967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92075 ⟨709967, by decide⟩ :=
  accepted_of_selected 12 92075 ⟨709967, by decide⟩ ⟨12, 2, 0, 709967, 92075, 1081, 65536⟩
    (by decide) selected_cut_28115

theorem unmarked_context_11_23018_709968 : frontier 10 ⟨709968, by decide⟩
    (prefixCache 11 23018) (prefixPartial 11 23018) = false := by
  decide +kernel

theorem node_context_11_23018_709968 : EJMOriginalGlobalDAGData.nodes 10 ⟨709968, by decide⟩ =
    .split (coordinate 11) (![⟨709915, by decide⟩,⟨709934, by decide⟩,⟨709953, by decide⟩,⟨709967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23018_709968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23018 ⟨709968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23018
    ⟨709968, by decide⟩ (by decide) (![⟨709915, by decide⟩,⟨709934, by decide⟩,⟨709953, by decide⟩,⟨709967, by decide⟩]) unmarked_context_11_23018_709968 node_context_11_23018_709968
  intro a
  fin_cases a
  · exact context_12_92072_709915
  · exact context_12_92073_709934
  · exact context_12_92074_709953
  · exact context_12_92075_709967

theorem selected_cut_28116 : selected 9 ⟨709978, by decide⟩
    (prefixPartial 12 92076) = some ⟨12, 2, 0, 709978, 92076, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_92076_709978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92076 ⟨709978, by decide⟩ :=
  accepted_of_selected 12 92076 ⟨709978, by decide⟩ ⟨12, 2, 0, 709978, 92076, 1133, 65536⟩
    (by decide) selected_cut_28116

theorem selected_cut_28117 : selected 9 ⟨709990, by decide⟩
    (prefixPartial 12 92077) = some ⟨12, 2, 0, 709990, 92077, 1081, 65536⟩ := by
  decide +kernel

theorem context_12_92077_709990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92077 ⟨709990, by decide⟩ :=
  accepted_of_selected 12 92077 ⟨709990, by decide⟩ ⟨12, 2, 0, 709990, 92077, 1081, 65536⟩
    (by decide) selected_cut_28117

theorem selected_cut_28118 : selected 9 ⟨710004, by decide⟩
    (prefixPartial 12 92078) = some ⟨12, 2, 0, 710004, 92078, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_92078_710004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92078 ⟨710004, by decide⟩ :=
  accepted_of_selected 12 92078 ⟨710004, by decide⟩ ⟨12, 2, 0, 710004, 92078, 1057, 65536⟩
    (by decide) selected_cut_28118

theorem selected_cut_28119 : selected 9 ⟨710022, by decide⟩
    (prefixPartial 12 92079) = some ⟨12, 2, 0, 710022, 92079, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_92079_710022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92079 ⟨710022, by decide⟩ :=
  accepted_of_selected 12 92079 ⟨710022, by decide⟩ ⟨12, 2, 0, 710022, 92079, 1453, 65536⟩
    (by decide) selected_cut_28119

theorem unmarked_context_11_23019_710023 : frontier 10 ⟨710023, by decide⟩
    (prefixCache 11 23019) (prefixPartial 11 23019) = false := by
  decide +kernel

theorem node_context_11_23019_710023 : EJMOriginalGlobalDAGData.nodes 10 ⟨710023, by decide⟩ =
    .split (coordinate 11) (![⟨709978, by decide⟩,⟨709990, by decide⟩,⟨710004, by decide⟩,⟨710022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23019_710023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23019 ⟨710023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23019
    ⟨710023, by decide⟩ (by decide) (![⟨709978, by decide⟩,⟨709990, by decide⟩,⟨710004, by decide⟩,⟨710022, by decide⟩]) unmarked_context_11_23019_710023 node_context_11_23019_710023
  intro a
  fin_cases a
  · exact context_12_92076_709978
  · exact context_12_92077_709990
  · exact context_12_92078_710004
  · exact context_12_92079_710022

theorem unmarked_context_10_5754_710024 : frontier 11 ⟨710024, by decide⟩
    (prefixCache 10 5754) (prefixPartial 10 5754) = false := by
  decide +kernel

theorem node_context_10_5754_710024 : EJMOriginalGlobalDAGData.nodes 11 ⟨710024, by decide⟩ =
    .split (coordinate 10) (![⟨709843, by decide⟩,⟨709898, by decide⟩,⟨709968, by decide⟩,⟨710023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5754_710024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5754 ⟨710024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5754
    ⟨710024, by decide⟩ (by decide) (![⟨709843, by decide⟩,⟨709898, by decide⟩,⟨709968, by decide⟩,⟨710023, by decide⟩]) unmarked_context_10_5754_710024 node_context_10_5754_710024
  intro a
  fin_cases a
  · exact context_11_23016_709843
  · exact context_11_23017_709898
  · exact context_11_23018_709968
  · exact context_11_23019_710023

theorem selected_cut_28120 : selected 9 ⟨710040, by decide⟩
    (prefixPartial 12 92080) = some ⟨12, 2, 0, 710040, 92080, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_92080_710040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92080 ⟨710040, by decide⟩ :=
  accepted_of_selected 12 92080 ⟨710040, by decide⟩ ⟨12, 2, 0, 710040, 92080, 1437, 65536⟩
    (by decide) selected_cut_28120

theorem selected_cut_28121 : selected 9 ⟨710055, by decide⟩
    (prefixPartial 12 92081) = some ⟨12, 2, 0, 710055, 92081, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_92081_710055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92081 ⟨710055, by decide⟩ :=
  accepted_of_selected 12 92081 ⟨710055, by decide⟩ ⟨12, 2, 0, 710055, 92081, 1165, 65536⟩
    (by decide) selected_cut_28121

theorem selected_cut_28122 : selected 9 ⟨710072, by decide⟩
    (prefixPartial 12 92082) = some ⟨12, 2, 0, 710072, 92082, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_92082_710072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92082 ⟨710072, by decide⟩ :=
  accepted_of_selected 12 92082 ⟨710072, by decide⟩ ⟨12, 2, 0, 710072, 92082, 1321, 65536⟩
    (by decide) selected_cut_28122

theorem selected_cut_28123 : selected 9 ⟨710080, by decide⟩
    (prefixPartial 12 92083) = some ⟨12, 2, 0, 710080, 92083, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_92083_710080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92083 ⟨710080, by decide⟩ :=
  accepted_of_selected 12 92083 ⟨710080, by decide⟩ ⟨12, 2, 0, 710080, 92083, 1153, 65536⟩
    (by decide) selected_cut_28123

theorem unmarked_context_11_23020_710081 : frontier 10 ⟨710081, by decide⟩
    (prefixCache 11 23020) (prefixPartial 11 23020) = false := by
  decide +kernel

theorem node_context_11_23020_710081 : EJMOriginalGlobalDAGData.nodes 10 ⟨710081, by decide⟩ =
    .split (coordinate 11) (![⟨710040, by decide⟩,⟨710055, by decide⟩,⟨710072, by decide⟩,⟨710080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23020_710081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23020 ⟨710081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23020
    ⟨710081, by decide⟩ (by decide) (![⟨710040, by decide⟩,⟨710055, by decide⟩,⟨710072, by decide⟩,⟨710080, by decide⟩]) unmarked_context_11_23020_710081 node_context_11_23020_710081
  intro a
  fin_cases a
  · exact context_12_92080_710040
  · exact context_12_92081_710055
  · exact context_12_92082_710072
  · exact context_12_92083_710080

theorem selected_cut_28124 : selected 9 ⟨710097, by decide⟩
    (prefixPartial 12 92084) = some ⟨12, 2, 0, 710097, 92084, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_92084_710097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92084 ⟨710097, by decide⟩ :=
  accepted_of_selected 12 92084 ⟨710097, by decide⟩ ⟨12, 2, 0, 710097, 92084, 1229, 65536⟩
    (by decide) selected_cut_28124

theorem selected_cut_28125 : selected 9 ⟨710107, by decide⟩
    (prefixPartial 12 92085) = some ⟨12, 2, 0, 710107, 92085, 965, 65536⟩ := by
  decide +kernel

theorem context_12_92085_710107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92085 ⟨710107, by decide⟩ :=
  accepted_of_selected 12 92085 ⟨710107, by decide⟩ ⟨12, 2, 0, 710107, 92085, 965, 65536⟩
    (by decide) selected_cut_28125

theorem selected_cut_28126 : selected 9 ⟨710118, by decide⟩
    (prefixPartial 12 92086) = some ⟨12, 2, 0, 710118, 92086, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_92086_710118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92086 ⟨710118, by decide⟩ :=
  accepted_of_selected 12 92086 ⟨710118, by decide⟩ ⟨12, 2, 0, 710118, 92086, 1213, 65536⟩
    (by decide) selected_cut_28126

theorem selected_cut_28127 : selected 9 ⟨710126, by decide⟩
    (prefixPartial 12 92087) = some ⟨12, 2, 0, 710126, 92087, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_92087_710126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92087 ⟨710126, by decide⟩ :=
  accepted_of_selected 12 92087 ⟨710126, by decide⟩ ⟨12, 2, 0, 710126, 92087, 1037, 65536⟩
    (by decide) selected_cut_28127

theorem unmarked_context_11_23021_710127 : frontier 10 ⟨710127, by decide⟩
    (prefixCache 11 23021) (prefixPartial 11 23021) = false := by
  decide +kernel

theorem node_context_11_23021_710127 : EJMOriginalGlobalDAGData.nodes 10 ⟨710127, by decide⟩ =
    .split (coordinate 11) (![⟨710097, by decide⟩,⟨710107, by decide⟩,⟨710118, by decide⟩,⟨710126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23021_710127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23021 ⟨710127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23021
    ⟨710127, by decide⟩ (by decide) (![⟨710097, by decide⟩,⟨710107, by decide⟩,⟨710118, by decide⟩,⟨710126, by decide⟩]) unmarked_context_11_23021_710127 node_context_11_23021_710127
  intro a
  fin_cases a
  · exact context_12_92084_710097
  · exact context_12_92085_710107
  · exact context_12_92086_710118
  · exact context_12_92087_710126

theorem selected_cut_28128 : selected 9 ⟨710139, by decide⟩
    (prefixPartial 12 92088) = some ⟨12, 2, 0, 710139, 92088, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_92088_710139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92088 ⟨710139, by decide⟩ :=
  accepted_of_selected 12 92088 ⟨710139, by decide⟩ ⟨12, 2, 0, 710139, 92088, 1237, 65536⟩
    (by decide) selected_cut_28128

theorem selected_cut_28129 : selected 9 ⟨710158, by decide⟩
    (prefixPartial 12 92089) = some ⟨12, 2, 0, 710158, 92089, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_92089_710158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92089 ⟨710158, by decide⟩ :=
  accepted_of_selected 12 92089 ⟨710158, by decide⟩ ⟨12, 2, 0, 710158, 92089, 1121, 65536⟩
    (by decide) selected_cut_28129

theorem selected_cut_28130 : selected 9 ⟨710170, by decide⟩
    (prefixPartial 12 92090) = some ⟨12, 2, 0, 710170, 92090, 1121, 65536⟩ := by
  decide +kernel

theorem context_12_92090_710170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92090 ⟨710170, by decide⟩ :=
  accepted_of_selected 12 92090 ⟨710170, by decide⟩ ⟨12, 2, 0, 710170, 92090, 1121, 65536⟩
    (by decide) selected_cut_28130

theorem selected_cut_28131 : selected 9 ⟨710184, by decide⟩
    (prefixPartial 12 92091) = some ⟨12, 2, 0, 710184, 92091, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_92091_710184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92091 ⟨710184, by decide⟩ :=
  accepted_of_selected 12 92091 ⟨710184, by decide⟩ ⟨12, 2, 0, 710184, 92091, 1049, 65536⟩
    (by decide) selected_cut_28131

theorem unmarked_context_11_23022_710185 : frontier 10 ⟨710185, by decide⟩
    (prefixCache 11 23022) (prefixPartial 11 23022) = false := by
  decide +kernel

theorem node_context_11_23022_710185 : EJMOriginalGlobalDAGData.nodes 10 ⟨710185, by decide⟩ =
    .split (coordinate 11) (![⟨710139, by decide⟩,⟨710158, by decide⟩,⟨710170, by decide⟩,⟨710184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23022_710185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23022 ⟨710185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23022
    ⟨710185, by decide⟩ (by decide) (![⟨710139, by decide⟩,⟨710158, by decide⟩,⟨710170, by decide⟩,⟨710184, by decide⟩]) unmarked_context_11_23022_710185 node_context_11_23022_710185
  intro a
  fin_cases a
  · exact context_12_92088_710139
  · exact context_12_92089_710158
  · exact context_12_92090_710170
  · exact context_12_92091_710184

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
