/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover384
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_36962 : selected 9 ⟨986705, by decide⟩
    (prefixPartial 12 299060) = some ⟨12, 2, 0, 986705, 299060, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_299060_986705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299060 ⟨986705, by decide⟩ :=
  accepted_of_selected 12 299060 ⟨986705, by decide⟩ ⟨12, 2, 0, 986705, 299060, 2769, 65536⟩
    (by decide) selected_cut_36962

theorem selected_cut_36963 : selected 9 ⟨986747, by decide⟩
    (prefixPartial 12 299061) = some ⟨12, 2, 0, 986747, 299061, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_299061_986747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299061 ⟨986747, by decide⟩ :=
  accepted_of_selected 12 299061 ⟨986747, by decide⟩ ⟨12, 2, 0, 986747, 299061, 2701, 65536⟩
    (by decide) selected_cut_36963

theorem selected_cut_36964 : selected 9 ⟨986785, by decide⟩
    (prefixPartial 12 299062) = some ⟨12, 2, 0, 986785, 299062, 2693, 65536⟩ := by
  decide +kernel

theorem context_12_299062_986785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299062 ⟨986785, by decide⟩ :=
  accepted_of_selected 12 299062 ⟨986785, by decide⟩ ⟨12, 2, 0, 986785, 299062, 2693, 65536⟩
    (by decide) selected_cut_36964

theorem selected_cut_36965 : selected 9 ⟨986829, by decide⟩
    (prefixPartial 12 299063) = some ⟨12, 2, 0, 986829, 299063, 2861, 65536⟩ := by
  decide +kernel

theorem context_12_299063_986829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299063 ⟨986829, by decide⟩ :=
  accepted_of_selected 12 299063 ⟨986829, by decide⟩ ⟨12, 2, 0, 986829, 299063, 2861, 65536⟩
    (by decide) selected_cut_36965

theorem unmarked_context_11_74765_986830 : frontier 10 ⟨986830, by decide⟩
    (prefixCache 11 74765) (prefixPartial 11 74765) = false := by
  decide +kernel

theorem node_context_11_74765_986830 : EJMOriginalGlobalDAGData.nodes 10 ⟨986830, by decide⟩ =
    .split (coordinate 11) (![⟨986705, by decide⟩,⟨986747, by decide⟩,⟨986785, by decide⟩,⟨986829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74765_986830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74765 ⟨986830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74765
    ⟨986830, by decide⟩ (by decide) (![⟨986705, by decide⟩,⟨986747, by decide⟩,⟨986785, by decide⟩,⟨986829, by decide⟩]) unmarked_context_11_74765_986830 node_context_11_74765_986830
  intro a
  fin_cases a
  · exact context_12_299060_986705
  · exact context_12_299061_986747
  · exact context_12_299062_986785
  · exact context_12_299063_986829

theorem selected_cut_36966 : selected 9 ⟨986870, by decide⟩
    (prefixPartial 12 299064) = some ⟨12, 2, 0, 986870, 299064, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_299064_986870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299064 ⟨986870, by decide⟩ :=
  accepted_of_selected 12 299064 ⟨986870, by decide⟩ ⟨12, 2, 0, 986870, 299064, 2493, 65536⟩
    (by decide) selected_cut_36966

theorem selected_cut_36967 : selected 9 ⟨986911, by decide⟩
    (prefixPartial 12 299065) = some ⟨12, 2, 0, 986911, 299065, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_299065_986911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299065 ⟨986911, by decide⟩ :=
  accepted_of_selected 12 299065 ⟨986911, by decide⟩ ⟨12, 2, 0, 986911, 299065, 2497, 65536⟩
    (by decide) selected_cut_36967

theorem selected_cut_36968 : selected 9 ⟨986948, by decide⟩
    (prefixPartial 12 299066) = some ⟨12, 2, 0, 986948, 299066, 2417, 65536⟩ := by
  decide +kernel

theorem context_12_299066_986948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299066 ⟨986948, by decide⟩ :=
  accepted_of_selected 12 299066 ⟨986948, by decide⟩ ⟨12, 2, 0, 986948, 299066, 2417, 65536⟩
    (by decide) selected_cut_36968

theorem selected_cut_36969 : selected 9 ⟨986993, by decide⟩
    (prefixPartial 12 299067) = some ⟨12, 2, 0, 986993, 299067, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_299067_986993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299067 ⟨986993, by decide⟩ :=
  accepted_of_selected 12 299067 ⟨986993, by decide⟩ ⟨12, 2, 0, 986993, 299067, 2785, 65536⟩
    (by decide) selected_cut_36969

theorem unmarked_context_11_74766_986994 : frontier 10 ⟨986994, by decide⟩
    (prefixCache 11 74766) (prefixPartial 11 74766) = false := by
  decide +kernel

theorem node_context_11_74766_986994 : EJMOriginalGlobalDAGData.nodes 10 ⟨986994, by decide⟩ =
    .split (coordinate 11) (![⟨986870, by decide⟩,⟨986911, by decide⟩,⟨986948, by decide⟩,⟨986993, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74766_986994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74766 ⟨986994, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74766
    ⟨986994, by decide⟩ (by decide) (![⟨986870, by decide⟩,⟨986911, by decide⟩,⟨986948, by decide⟩,⟨986993, by decide⟩]) unmarked_context_11_74766_986994 node_context_11_74766_986994
  intro a
  fin_cases a
  · exact context_12_299064_986870
  · exact context_12_299065_986911
  · exact context_12_299066_986948
  · exact context_12_299067_986993

theorem selected_cut_36970 : selected 9 ⟨987027, by decide⟩
    (prefixPartial 12 299068) = some ⟨12, 2, 0, 987027, 299068, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_299068_987027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299068 ⟨987027, by decide⟩ :=
  accepted_of_selected 12 299068 ⟨987027, by decide⟩ ⟨12, 2, 0, 987027, 299068, 2437, 65536⟩
    (by decide) selected_cut_36970

theorem selected_cut_36971 : selected 9 ⟨987063, by decide⟩
    (prefixPartial 12 299069) = some ⟨12, 2, 0, 987063, 299069, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_299069_987063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299069 ⟨987063, by decide⟩ :=
  accepted_of_selected 12 299069 ⟨987063, by decide⟩ ⟨12, 2, 0, 987063, 299069, 2565, 65536⟩
    (by decide) selected_cut_36971

theorem selected_cut_36972 : selected 9 ⟨987098, by decide⟩
    (prefixPartial 12 299070) = some ⟨12, 2, 0, 987098, 299070, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_299070_987098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299070 ⟨987098, by decide⟩ :=
  accepted_of_selected 12 299070 ⟨987098, by decide⟩ ⟨12, 2, 0, 987098, 299070, 2569, 65536⟩
    (by decide) selected_cut_36972

theorem selected_cut_36973 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 299071) = some ⟨12, 1, 0, 429285, 299071, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299071_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299071 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 299071 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 299071, 1, 65536⟩
    (by decide) selected_cut_36973

theorem unmarked_context_11_74767_987099 : frontier 10 ⟨987099, by decide⟩
    (prefixCache 11 74767) (prefixPartial 11 74767) = false := by
  decide +kernel

theorem node_context_11_74767_987099 : EJMOriginalGlobalDAGData.nodes 10 ⟨987099, by decide⟩ =
    .split (coordinate 11) (![⟨987027, by decide⟩,⟨987063, by decide⟩,⟨987098, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74767_987099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74767 ⟨987099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74767
    ⟨987099, by decide⟩ (by decide) (![⟨987027, by decide⟩,⟨987063, by decide⟩,⟨987098, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_74767_987099 node_context_11_74767_987099
  intro a
  fin_cases a
  · exact context_12_299068_987027
  · exact context_12_299069_987063
  · exact context_12_299070_987098
  · exact context_12_299071_429285

theorem unmarked_context_10_18691_987100 : frontier 11 ⟨987100, by decide⟩
    (prefixCache 10 18691) (prefixPartial 10 18691) = false := by
  decide +kernel

theorem node_context_10_18691_987100 : EJMOriginalGlobalDAGData.nodes 11 ⟨987100, by decide⟩ =
    .split (coordinate 10) (![⟨986666, by decide⟩,⟨986830, by decide⟩,⟨986994, by decide⟩,⟨987099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18691_987100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18691 ⟨987100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18691
    ⟨987100, by decide⟩ (by decide) (![⟨986666, by decide⟩,⟨986830, by decide⟩,⟨986994, by decide⟩,⟨987099, by decide⟩]) unmarked_context_10_18691_987100 node_context_10_18691_987100
  intro a
  fin_cases a
  · exact context_11_74764_986666
  · exact context_11_74765_986830
  · exact context_11_74766_986994
  · exact context_11_74767_987099

theorem unmarked_context_9_4672_987101 : frontier 12 ⟨987101, by decide⟩
    (prefixCache 9 4672) (prefixPartial 9 4672) = false := by
  decide +kernel

theorem node_context_9_4672_987101 : EJMOriginalGlobalDAGData.nodes 12 ⟨987101, by decide⟩ =
    .split (coordinate 9) (![⟨985389, by decide⟩,⟨986009, by decide⟩,⟨986570, by decide⟩,⟨987100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4672_987101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4672 ⟨987101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4672
    ⟨987101, by decide⟩ (by decide) (![⟨985389, by decide⟩,⟨986009, by decide⟩,⟨986570, by decide⟩,⟨987100, by decide⟩]) unmarked_context_9_4672_987101 node_context_9_4672_987101
  intro a
  fin_cases a
  · exact context_10_18688_985389
  · exact context_10_18689_986009
  · exact context_10_18690_986570
  · exact context_10_18691_987100

theorem selected_cut_36974 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74768) = some ⟨11, 1, 0, 907917, 74768, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74768_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74768 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74768 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74768, 1, 262144⟩
    (by decide) selected_cut_36974

theorem selected_cut_36975 : selected 9 ⟨987130, by decide⟩
    (prefixPartial 12 299076) = some ⟨12, 2, 0, 987130, 299076, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_299076_987130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299076 ⟨987130, by decide⟩ :=
  accepted_of_selected 12 299076 ⟨987130, by decide⟩ ⟨12, 2, 0, 987130, 299076, 2029, 65536⟩
    (by decide) selected_cut_36975

theorem selected_cut_36976 : selected 9 ⟨987166, by decide⟩
    (prefixPartial 12 299077) = some ⟨12, 2, 0, 987166, 299077, 2165, 65536⟩ := by
  decide +kernel

theorem context_12_299077_987166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299077 ⟨987166, by decide⟩ :=
  accepted_of_selected 12 299077 ⟨987166, by decide⟩ ⟨12, 2, 0, 987166, 299077, 2165, 65536⟩
    (by decide) selected_cut_36976

theorem selected_cut_36977 : selected 9 ⟨987197, by decide⟩
    (prefixPartial 12 299078) = some ⟨12, 2, 0, 987197, 299078, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_299078_987197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299078 ⟨987197, by decide⟩ :=
  accepted_of_selected 12 299078 ⟨987197, by decide⟩ ⟨12, 2, 0, 987197, 299078, 2137, 65536⟩
    (by decide) selected_cut_36977

theorem selected_cut_36978 : selected 9 ⟨987231, by decide⟩
    (prefixPartial 12 299079) = some ⟨12, 2, 0, 987231, 299079, 2257, 65536⟩ := by
  decide +kernel

theorem context_12_299079_987231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299079 ⟨987231, by decide⟩ :=
  accepted_of_selected 12 299079 ⟨987231, by decide⟩ ⟨12, 2, 0, 987231, 299079, 2257, 65536⟩
    (by decide) selected_cut_36978

theorem unmarked_context_11_74769_987232 : frontier 10 ⟨987232, by decide⟩
    (prefixCache 11 74769) (prefixPartial 11 74769) = false := by
  decide +kernel

theorem node_context_11_74769_987232 : EJMOriginalGlobalDAGData.nodes 10 ⟨987232, by decide⟩ =
    .split (coordinate 11) (![⟨987130, by decide⟩,⟨987166, by decide⟩,⟨987197, by decide⟩,⟨987231, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74769_987232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74769 ⟨987232, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74769
    ⟨987232, by decide⟩ (by decide) (![⟨987130, by decide⟩,⟨987166, by decide⟩,⟨987197, by decide⟩,⟨987231, by decide⟩]) unmarked_context_11_74769_987232 node_context_11_74769_987232
  intro a
  fin_cases a
  · exact context_12_299076_987130
  · exact context_12_299077_987166
  · exact context_12_299078_987197
  · exact context_12_299079_987231

theorem selected_cut_36979 : selected 9 ⟨987262, by decide⟩
    (prefixPartial 12 299080) = some ⟨12, 2, 0, 987262, 299080, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_299080_987262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299080 ⟨987262, by decide⟩ :=
  accepted_of_selected 12 299080 ⟨987262, by decide⟩ ⟨12, 2, 0, 987262, 299080, 1833, 65536⟩
    (by decide) selected_cut_36979

theorem selected_cut_36980 : selected 9 ⟨987298, by decide⟩
    (prefixPartial 12 299081) = some ⟨12, 2, 0, 987298, 299081, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_299081_987298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299081 ⟨987298, by decide⟩ :=
  accepted_of_selected 12 299081 ⟨987298, by decide⟩ ⟨12, 2, 0, 987298, 299081, 2113, 65536⟩
    (by decide) selected_cut_36980

theorem selected_cut_36981 : selected 9 ⟨987330, by decide⟩
    (prefixPartial 12 299082) = some ⟨12, 2, 0, 987330, 299082, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_299082_987330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299082 ⟨987330, by decide⟩ :=
  accepted_of_selected 12 299082 ⟨987330, by decide⟩ ⟨12, 2, 0, 987330, 299082, 1993, 65536⟩
    (by decide) selected_cut_36981

theorem selected_cut_36982 : selected 9 ⟨987366, by decide⟩
    (prefixPartial 12 299083) = some ⟨12, 2, 0, 987366, 299083, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_299083_987366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299083 ⟨987366, by decide⟩ :=
  accepted_of_selected 12 299083 ⟨987366, by decide⟩ ⟨12, 2, 0, 987366, 299083, 2305, 65536⟩
    (by decide) selected_cut_36982

theorem unmarked_context_11_74770_987367 : frontier 10 ⟨987367, by decide⟩
    (prefixCache 11 74770) (prefixPartial 11 74770) = false := by
  decide +kernel

theorem node_context_11_74770_987367 : EJMOriginalGlobalDAGData.nodes 10 ⟨987367, by decide⟩ =
    .split (coordinate 11) (![⟨987262, by decide⟩,⟨987298, by decide⟩,⟨987330, by decide⟩,⟨987366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74770_987367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74770 ⟨987367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74770
    ⟨987367, by decide⟩ (by decide) (![⟨987262, by decide⟩,⟨987298, by decide⟩,⟨987330, by decide⟩,⟨987366, by decide⟩]) unmarked_context_11_74770_987367 node_context_11_74770_987367
  intro a
  fin_cases a
  · exact context_12_299080_987262
  · exact context_12_299081_987298
  · exact context_12_299082_987330
  · exact context_12_299083_987366

theorem selected_cut_36983 : selected 9 ⟨987395, by decide⟩
    (prefixPartial 12 299084) = some ⟨12, 2, 0, 987395, 299084, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_299084_987395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299084 ⟨987395, by decide⟩ :=
  accepted_of_selected 12 299084 ⟨987395, by decide⟩ ⟨12, 2, 0, 987395, 299084, 1785, 65536⟩
    (by decide) selected_cut_36983

theorem selected_cut_36984 : selected 9 ⟨987428, by decide⟩
    (prefixPartial 12 299085) = some ⟨12, 2, 0, 987428, 299085, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_299085_987428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299085 ⟨987428, by decide⟩ :=
  accepted_of_selected 12 299085 ⟨987428, by decide⟩ ⟨12, 2, 0, 987428, 299085, 2029, 65536⟩
    (by decide) selected_cut_36984

theorem selected_cut_36985 : selected 9 ⟨987462, by decide⟩
    (prefixPartial 12 299086) = some ⟨12, 2, 0, 987462, 299086, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_299086_987462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299086 ⟨987462, by decide⟩ :=
  accepted_of_selected 12 299086 ⟨987462, by decide⟩ ⟨12, 2, 0, 987462, 299086, 2141, 65536⟩
    (by decide) selected_cut_36985

theorem selected_cut_36986 : selected 9 ⟨987495, by decide⟩
    (prefixPartial 12 299087) = some ⟨12, 2, 0, 987495, 299087, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_299087_987495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299087 ⟨987495, by decide⟩ :=
  accepted_of_selected 12 299087 ⟨987495, by decide⟩ ⟨12, 2, 0, 987495, 299087, 1985, 65536⟩
    (by decide) selected_cut_36986

theorem unmarked_context_11_74771_987496 : frontier 10 ⟨987496, by decide⟩
    (prefixCache 11 74771) (prefixPartial 11 74771) = false := by
  decide +kernel

theorem node_context_11_74771_987496 : EJMOriginalGlobalDAGData.nodes 10 ⟨987496, by decide⟩ =
    .split (coordinate 11) (![⟨987395, by decide⟩,⟨987428, by decide⟩,⟨987462, by decide⟩,⟨987495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74771_987496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74771 ⟨987496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74771
    ⟨987496, by decide⟩ (by decide) (![⟨987395, by decide⟩,⟨987428, by decide⟩,⟨987462, by decide⟩,⟨987495, by decide⟩]) unmarked_context_11_74771_987496 node_context_11_74771_987496
  intro a
  fin_cases a
  · exact context_12_299084_987395
  · exact context_12_299085_987428
  · exact context_12_299086_987462
  · exact context_12_299087_987495

theorem unmarked_context_10_18692_987497 : frontier 11 ⟨987497, by decide⟩
    (prefixCache 10 18692) (prefixPartial 10 18692) = false := by
  decide +kernel

theorem node_context_10_18692_987497 : EJMOriginalGlobalDAGData.nodes 11 ⟨987497, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨987232, by decide⟩,⟨987367, by decide⟩,⟨987496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18692_987497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18692 ⟨987497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18692
    ⟨987497, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨987232, by decide⟩,⟨987367, by decide⟩,⟨987496, by decide⟩]) unmarked_context_10_18692_987497 node_context_10_18692_987497
  intro a
  fin_cases a
  · exact context_11_74768_907917
  · exact context_11_74769_987232
  · exact context_11_74770_987367
  · exact context_11_74771_987496

theorem selected_cut_36987 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18693) = some ⟨10, 1, 0, 893098, 18693, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18693_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18693 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18693 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18693, 1, 1048576⟩
    (by decide) selected_cut_36987

theorem selected_cut_36988 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 299104) = some ⟨12, 1, 0, 985390, 299104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299104_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299104 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 299104 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 299104, 1, 65536⟩
    (by decide) selected_cut_36988

theorem selected_cut_36989 : selected 9 ⟨987515, by decide⟩
    (prefixPartial 12 299105) = some ⟨12, 2, 0, 987515, 299105, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_299105_987515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299105 ⟨987515, by decide⟩ :=
  accepted_of_selected 12 299105 ⟨987515, by decide⟩ ⟨12, 2, 0, 987515, 299105, 1665, 65536⟩
    (by decide) selected_cut_36989

theorem selected_cut_36990 : selected 9 ⟨987534, by decide⟩
    (prefixPartial 12 299106) = some ⟨12, 2, 0, 987534, 299106, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_299106_987534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299106 ⟨987534, by decide⟩ :=
  accepted_of_selected 12 299106 ⟨987534, by decide⟩ ⟨12, 2, 0, 987534, 299106, 1529, 65536⟩
    (by decide) selected_cut_36990

theorem selected_cut_36991 : selected 9 ⟨987551, by decide⟩
    (prefixPartial 12 299107) = some ⟨12, 2, 0, 987551, 299107, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_299107_987551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299107 ⟨987551, by decide⟩ :=
  accepted_of_selected 12 299107 ⟨987551, by decide⟩ ⟨12, 2, 0, 987551, 299107, 1585, 65536⟩
    (by decide) selected_cut_36991

theorem unmarked_context_11_74776_987552 : frontier 10 ⟨987552, by decide⟩
    (prefixCache 11 74776) (prefixPartial 11 74776) = false := by
  decide +kernel

theorem node_context_11_74776_987552 : EJMOriginalGlobalDAGData.nodes 10 ⟨987552, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨987515, by decide⟩,⟨987534, by decide⟩,⟨987551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74776_987552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74776 ⟨987552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74776
    ⟨987552, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨987515, by decide⟩,⟨987534, by decide⟩,⟨987551, by decide⟩]) unmarked_context_11_74776_987552 node_context_11_74776_987552
  intro a
  fin_cases a
  · exact context_12_299104_985390
  · exact context_12_299105_987515
  · exact context_12_299106_987534
  · exact context_12_299107_987551

theorem selected_cut_36992 : selected 9 ⟨987577, by decide⟩
    (prefixPartial 12 299108) = some ⟨12, 2, 0, 987577, 299108, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_299108_987577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299108 ⟨987577, by decide⟩ :=
  accepted_of_selected 12 299108 ⟨987577, by decide⟩ ⟨12, 2, 0, 987577, 299108, 1733, 65536⟩
    (by decide) selected_cut_36992

theorem selected_cut_36993 : selected 9 ⟨987603, by decide⟩
    (prefixPartial 12 299109) = some ⟨12, 2, 0, 987603, 299109, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_299109_987603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299109 ⟨987603, by decide⟩ :=
  accepted_of_selected 12 299109 ⟨987603, by decide⟩ ⟨12, 2, 0, 987603, 299109, 1737, 65536⟩
    (by decide) selected_cut_36993

theorem selected_cut_36994 : selected 9 ⟨987628, by decide⟩
    (prefixPartial 12 299110) = some ⟨12, 2, 0, 987628, 299110, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_299110_987628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299110 ⟨987628, by decide⟩ :=
  accepted_of_selected 12 299110 ⟨987628, by decide⟩ ⟨12, 2, 0, 987628, 299110, 1693, 65536⟩
    (by decide) selected_cut_36994

theorem selected_cut_36995 : selected 9 ⟨987652, by decide⟩
    (prefixPartial 12 299111) = some ⟨12, 2, 0, 987652, 299111, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_299111_987652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299111 ⟨987652, by decide⟩ :=
  accepted_of_selected 12 299111 ⟨987652, by decide⟩ ⟨12, 2, 0, 987652, 299111, 1749, 65536⟩
    (by decide) selected_cut_36995

theorem unmarked_context_11_74777_987653 : frontier 10 ⟨987653, by decide⟩
    (prefixCache 11 74777) (prefixPartial 11 74777) = false := by
  decide +kernel

theorem node_context_11_74777_987653 : EJMOriginalGlobalDAGData.nodes 10 ⟨987653, by decide⟩ =
    .split (coordinate 11) (![⟨987577, by decide⟩,⟨987603, by decide⟩,⟨987628, by decide⟩,⟨987652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74777_987653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74777 ⟨987653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74777
    ⟨987653, by decide⟩ (by decide) (![⟨987577, by decide⟩,⟨987603, by decide⟩,⟨987628, by decide⟩,⟨987652, by decide⟩]) unmarked_context_11_74777_987653 node_context_11_74777_987653
  intro a
  fin_cases a
  · exact context_12_299108_987577
  · exact context_12_299109_987603
  · exact context_12_299110_987628
  · exact context_12_299111_987652

theorem selected_cut_36996 : selected 9 ⟨987675, by decide⟩
    (prefixPartial 12 299112) = some ⟨12, 2, 0, 987675, 299112, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_299112_987675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299112 ⟨987675, by decide⟩ :=
  accepted_of_selected 12 299112 ⟨987675, by decide⟩ ⟨12, 2, 0, 987675, 299112, 1657, 65536⟩
    (by decide) selected_cut_36996

theorem selected_cut_36997 : selected 9 ⟨987706, by decide⟩
    (prefixPartial 12 299113) = some ⟨12, 2, 0, 987706, 299113, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_299113_987706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299113 ⟨987706, by decide⟩ :=
  accepted_of_selected 12 299113 ⟨987706, by decide⟩ ⟨12, 2, 0, 987706, 299113, 1853, 65536⟩
    (by decide) selected_cut_36997

theorem selected_cut_36998 : selected 9 ⟨242157, by decide⟩
    (prefixPartial 12 299114) = some ⟨12, 1, 0, 242157, 299114, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299114_242157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299114 ⟨242157, by decide⟩ :=
  accepted_of_selected 12 299114 ⟨242157, by decide⟩ ⟨12, 1, 0, 242157, 299114, 1, 65536⟩
    (by decide) selected_cut_36998

theorem selected_cut_36999 : selected 9 ⟨987737, by decide⟩
    (prefixPartial 12 299115) = some ⟨12, 2, 0, 987737, 299115, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_299115_987737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299115 ⟨987737, by decide⟩ :=
  accepted_of_selected 12 299115 ⟨987737, by decide⟩ ⟨12, 2, 0, 987737, 299115, 1973, 65536⟩
    (by decide) selected_cut_36999

theorem unmarked_context_11_74778_987738 : frontier 10 ⟨987738, by decide⟩
    (prefixCache 11 74778) (prefixPartial 11 74778) = false := by
  decide +kernel

theorem node_context_11_74778_987738 : EJMOriginalGlobalDAGData.nodes 10 ⟨987738, by decide⟩ =
    .split (coordinate 11) (![⟨987675, by decide⟩,⟨987706, by decide⟩,⟨242157, by decide⟩,⟨987737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74778_987738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74778 ⟨987738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74778
    ⟨987738, by decide⟩ (by decide) (![⟨987675, by decide⟩,⟨987706, by decide⟩,⟨242157, by decide⟩,⟨987737, by decide⟩]) unmarked_context_11_74778_987738 node_context_11_74778_987738
  intro a
  fin_cases a
  · exact context_12_299112_987675
  · exact context_12_299113_987706
  · exact context_12_299114_242157
  · exact context_12_299115_987737

theorem selected_cut_37000 : selected 9 ⟨987757, by decide⟩
    (prefixPartial 12 299116) = some ⟨12, 2, 0, 987757, 299116, 1609, 65536⟩ := by
  decide +kernel

theorem context_12_299116_987757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299116 ⟨987757, by decide⟩ :=
  accepted_of_selected 12 299116 ⟨987757, by decide⟩ ⟨12, 2, 0, 987757, 299116, 1609, 65536⟩
    (by decide) selected_cut_37000

theorem selected_cut_37001 : selected 9 ⟨987788, by decide⟩
    (prefixPartial 12 299117) = some ⟨12, 2, 0, 987788, 299117, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_299117_987788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299117 ⟨987788, by decide⟩ :=
  accepted_of_selected 12 299117 ⟨987788, by decide⟩ ⟨12, 2, 0, 987788, 299117, 1813, 65536⟩
    (by decide) selected_cut_37001

theorem selected_cut_37002 : selected 9 ⟨987819, by decide⟩
    (prefixPartial 12 299118) = some ⟨12, 2, 0, 987819, 299118, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_299118_987819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299118 ⟨987819, by decide⟩ :=
  accepted_of_selected 12 299118 ⟨987819, by decide⟩ ⟨12, 2, 0, 987819, 299118, 1821, 65536⟩
    (by decide) selected_cut_37002

theorem selected_cut_37003 : selected 9 ⟨987846, by decide⟩
    (prefixPartial 12 299119) = some ⟨12, 2, 0, 987846, 299119, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_299119_987846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299119 ⟨987846, by decide⟩ :=
  accepted_of_selected 12 299119 ⟨987846, by decide⟩ ⟨12, 2, 0, 987846, 299119, 1689, 65536⟩
    (by decide) selected_cut_37003

theorem unmarked_context_11_74779_987847 : frontier 10 ⟨987847, by decide⟩
    (prefixCache 11 74779) (prefixPartial 11 74779) = false := by
  decide +kernel

theorem node_context_11_74779_987847 : EJMOriginalGlobalDAGData.nodes 10 ⟨987847, by decide⟩ =
    .split (coordinate 11) (![⟨987757, by decide⟩,⟨987788, by decide⟩,⟨987819, by decide⟩,⟨987846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74779_987847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74779 ⟨987847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74779
    ⟨987847, by decide⟩ (by decide) (![⟨987757, by decide⟩,⟨987788, by decide⟩,⟨987819, by decide⟩,⟨987846, by decide⟩]) unmarked_context_11_74779_987847 node_context_11_74779_987847
  intro a
  fin_cases a
  · exact context_12_299116_987757
  · exact context_12_299117_987788
  · exact context_12_299118_987819
  · exact context_12_299119_987846

theorem unmarked_context_10_18694_987848 : frontier 11 ⟨987848, by decide⟩
    (prefixCache 10 18694) (prefixPartial 10 18694) = false := by
  decide +kernel

theorem node_context_10_18694_987848 : EJMOriginalGlobalDAGData.nodes 11 ⟨987848, by decide⟩ =
    .split (coordinate 10) (![⟨987552, by decide⟩,⟨987653, by decide⟩,⟨987738, by decide⟩,⟨987847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18694_987848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18694 ⟨987848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18694
    ⟨987848, by decide⟩ (by decide) (![⟨987552, by decide⟩,⟨987653, by decide⟩,⟨987738, by decide⟩,⟨987847, by decide⟩]) unmarked_context_10_18694_987848 node_context_10_18694_987848
  intro a
  fin_cases a
  · exact context_11_74776_987552
  · exact context_11_74777_987653
  · exact context_11_74778_987738
  · exact context_11_74779_987847

theorem selected_cut_37004 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 299120) = some ⟨12, 1, 0, 985390, 299120, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299120_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299120 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 299120 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 299120, 1, 65536⟩
    (by decide) selected_cut_37004

theorem selected_cut_37005 : selected 9 ⟨987868, by decide⟩
    (prefixPartial 12 299121) = some ⟨12, 2, 0, 987868, 299121, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_299121_987868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299121 ⟨987868, by decide⟩ :=
  accepted_of_selected 12 299121 ⟨987868, by decide⟩ ⟨12, 2, 0, 987868, 299121, 1429, 65536⟩
    (by decide) selected_cut_37005

theorem selected_cut_37006 : selected 9 ⟨987882, by decide⟩
    (prefixPartial 12 299122) = some ⟨12, 2, 0, 987882, 299122, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_299122_987882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299122 ⟨987882, by decide⟩ :=
  accepted_of_selected 12 299122 ⟨987882, by decide⟩ ⟨12, 2, 0, 987882, 299122, 1249, 65536⟩
    (by decide) selected_cut_37006

theorem selected_cut_37007 : selected 9 ⟨987907, by decide⟩
    (prefixPartial 12 299123) = some ⟨12, 2, 0, 987907, 299123, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_299123_987907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299123 ⟨987907, by decide⟩ :=
  accepted_of_selected 12 299123 ⟨987907, by decide⟩ ⟨12, 2, 0, 987907, 299123, 1433, 65536⟩
    (by decide) selected_cut_37007

theorem unmarked_context_11_74780_987908 : frontier 10 ⟨987908, by decide⟩
    (prefixCache 11 74780) (prefixPartial 11 74780) = false := by
  decide +kernel

theorem node_context_11_74780_987908 : EJMOriginalGlobalDAGData.nodes 10 ⟨987908, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨987868, by decide⟩,⟨987882, by decide⟩,⟨987907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74780_987908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74780 ⟨987908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74780
    ⟨987908, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨987868, by decide⟩,⟨987882, by decide⟩,⟨987907, by decide⟩]) unmarked_context_11_74780_987908 node_context_11_74780_987908
  intro a
  fin_cases a
  · exact context_12_299120_985390
  · exact context_12_299121_987868
  · exact context_12_299122_987882
  · exact context_12_299123_987907

theorem selected_cut_37008 : selected 9 ⟨987931, by decide⟩
    (prefixPartial 12 299124) = some ⟨12, 2, 0, 987931, 299124, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_299124_987931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299124 ⟨987931, by decide⟩ :=
  accepted_of_selected 12 299124 ⟨987931, by decide⟩ ⟨12, 2, 0, 987931, 299124, 1581, 65536⟩
    (by decide) selected_cut_37008

theorem selected_cut_37009 : selected 9 ⟨987958, by decide⟩
    (prefixPartial 12 299125) = some ⟨12, 2, 0, 987958, 299125, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_299125_987958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299125 ⟨987958, by decide⟩ :=
  accepted_of_selected 12 299125 ⟨987958, by decide⟩ ⟨12, 2, 0, 987958, 299125, 1573, 65536⟩
    (by decide) selected_cut_37009

theorem selected_cut_37010 : selected 9 ⟨987980, by decide⟩
    (prefixPartial 12 299126) = some ⟨12, 2, 0, 987980, 299126, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_299126_987980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299126 ⟨987980, by decide⟩ :=
  accepted_of_selected 12 299126 ⟨987980, by decide⟩ ⟨12, 2, 0, 987980, 299126, 1437, 65536⟩
    (by decide) selected_cut_37010

theorem selected_cut_37011 : selected 9 ⟨988006, by decide⟩
    (prefixPartial 12 299127) = some ⟨12, 2, 0, 988006, 299127, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_299127_988006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299127 ⟨988006, by decide⟩ :=
  accepted_of_selected 12 299127 ⟨988006, by decide⟩ ⟨12, 2, 0, 988006, 299127, 1661, 65536⟩
    (by decide) selected_cut_37011

theorem unmarked_context_11_74781_988007 : frontier 10 ⟨988007, by decide⟩
    (prefixCache 11 74781) (prefixPartial 11 74781) = false := by
  decide +kernel

theorem node_context_11_74781_988007 : EJMOriginalGlobalDAGData.nodes 10 ⟨988007, by decide⟩ =
    .split (coordinate 11) (![⟨987931, by decide⟩,⟨987958, by decide⟩,⟨987980, by decide⟩,⟨988006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74781_988007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74781 ⟨988007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74781
    ⟨988007, by decide⟩ (by decide) (![⟨987931, by decide⟩,⟨987958, by decide⟩,⟨987980, by decide⟩,⟨988006, by decide⟩]) unmarked_context_11_74781_988007 node_context_11_74781_988007
  intro a
  fin_cases a
  · exact context_12_299124_987931
  · exact context_12_299125_987958
  · exact context_12_299126_987980
  · exact context_12_299127_988006

theorem selected_cut_37012 : selected 9 ⟨988031, by decide⟩
    (prefixPartial 12 299128) = some ⟨12, 2, 0, 988031, 299128, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_299128_988031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299128 ⟨988031, by decide⟩ :=
  accepted_of_selected 12 299128 ⟨988031, by decide⟩ ⟨12, 2, 0, 988031, 299128, 1429, 65536⟩
    (by decide) selected_cut_37012

theorem selected_cut_37013 : selected 9 ⟨988056, by decide⟩
    (prefixPartial 12 299129) = some ⟨12, 2, 0, 988056, 299129, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_299129_988056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299129 ⟨988056, by decide⟩ :=
  accepted_of_selected 12 299129 ⟨988056, by decide⟩ ⟨12, 2, 0, 988056, 299129, 1585, 65536⟩
    (by decide) selected_cut_37013

theorem selected_cut_37014 : selected 9 ⟨988078, by decide⟩
    (prefixPartial 12 299130) = some ⟨12, 2, 0, 988078, 299130, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_299130_988078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299130 ⟨988078, by decide⟩ :=
  accepted_of_selected 12 299130 ⟨988078, by decide⟩ ⟨12, 2, 0, 988078, 299130, 1421, 65536⟩
    (by decide) selected_cut_37014

theorem selected_cut_37015 : selected 9 ⟨988107, by decide⟩
    (prefixPartial 12 299131) = some ⟨12, 2, 0, 988107, 299131, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_299131_988107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299131 ⟨988107, by decide⟩ :=
  accepted_of_selected 12 299131 ⟨988107, by decide⟩ ⟨12, 2, 0, 988107, 299131, 1829, 65536⟩
    (by decide) selected_cut_37015

theorem unmarked_context_11_74782_988108 : frontier 10 ⟨988108, by decide⟩
    (prefixCache 11 74782) (prefixPartial 11 74782) = false := by
  decide +kernel

theorem node_context_11_74782_988108 : EJMOriginalGlobalDAGData.nodes 10 ⟨988108, by decide⟩ =
    .split (coordinate 11) (![⟨988031, by decide⟩,⟨988056, by decide⟩,⟨988078, by decide⟩,⟨988107, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74782_988108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74782 ⟨988108, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74782
    ⟨988108, by decide⟩ (by decide) (![⟨988031, by decide⟩,⟨988056, by decide⟩,⟨988078, by decide⟩,⟨988107, by decide⟩]) unmarked_context_11_74782_988108 node_context_11_74782_988108
  intro a
  fin_cases a
  · exact context_12_299128_988031
  · exact context_12_299129_988056
  · exact context_12_299130_988078
  · exact context_12_299131_988107

theorem selected_cut_37016 : selected 9 ⟨988130, by decide⟩
    (prefixPartial 12 299132) = some ⟨12, 2, 0, 988130, 299132, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_299132_988130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299132 ⟨988130, by decide⟩ :=
  accepted_of_selected 12 299132 ⟨988130, by decide⟩ ⟨12, 2, 0, 988130, 299132, 1381, 65536⟩
    (by decide) selected_cut_37016

theorem selected_cut_37017 : selected 9 ⟨988156, by decide⟩
    (prefixPartial 12 299133) = some ⟨12, 2, 0, 988156, 299133, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_299133_988156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299133 ⟨988156, by decide⟩ :=
  accepted_of_selected 12 299133 ⟨988156, by decide⟩ ⟨12, 2, 0, 988156, 299133, 1589, 65536⟩
    (by decide) selected_cut_37017

theorem selected_cut_37018 : selected 9 ⟨988183, by decide⟩
    (prefixPartial 12 299134) = some ⟨12, 2, 0, 988183, 299134, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_299134_988183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299134 ⟨988183, by decide⟩ :=
  accepted_of_selected 12 299134 ⟨988183, by decide⟩ ⟨12, 2, 0, 988183, 299134, 1517, 65536⟩
    (by decide) selected_cut_37018

theorem selected_cut_37019 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 299135) = some ⟨12, 1, 0, 429285, 299135, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299135_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299135 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 299135 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 299135, 1, 65536⟩
    (by decide) selected_cut_37019

theorem unmarked_context_11_74783_988184 : frontier 10 ⟨988184, by decide⟩
    (prefixCache 11 74783) (prefixPartial 11 74783) = false := by
  decide +kernel

theorem node_context_11_74783_988184 : EJMOriginalGlobalDAGData.nodes 10 ⟨988184, by decide⟩ =
    .split (coordinate 11) (![⟨988130, by decide⟩,⟨988156, by decide⟩,⟨988183, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74783_988184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74783 ⟨988184, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74783
    ⟨988184, by decide⟩ (by decide) (![⟨988130, by decide⟩,⟨988156, by decide⟩,⟨988183, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_74783_988184 node_context_11_74783_988184
  intro a
  fin_cases a
  · exact context_12_299132_988130
  · exact context_12_299133_988156
  · exact context_12_299134_988183
  · exact context_12_299135_429285

theorem unmarked_context_10_18695_988185 : frontier 11 ⟨988185, by decide⟩
    (prefixCache 10 18695) (prefixPartial 10 18695) = false := by
  decide +kernel

theorem node_context_10_18695_988185 : EJMOriginalGlobalDAGData.nodes 11 ⟨988185, by decide⟩ =
    .split (coordinate 10) (![⟨987908, by decide⟩,⟨988007, by decide⟩,⟨988108, by decide⟩,⟨988184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18695_988185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18695 ⟨988185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18695
    ⟨988185, by decide⟩ (by decide) (![⟨987908, by decide⟩,⟨988007, by decide⟩,⟨988108, by decide⟩,⟨988184, by decide⟩]) unmarked_context_10_18695_988185 node_context_10_18695_988185
  intro a
  fin_cases a
  · exact context_11_74780_987908
  · exact context_11_74781_988007
  · exact context_11_74782_988108
  · exact context_11_74783_988184

theorem unmarked_context_9_4673_988186 : frontier 12 ⟨988186, by decide⟩
    (prefixCache 9 4673) (prefixPartial 9 4673) = false := by
  decide +kernel

theorem node_context_9_4673_988186 : EJMOriginalGlobalDAGData.nodes 12 ⟨988186, by decide⟩ =
    .split (coordinate 9) (![⟨987497, by decide⟩,⟨893098, by decide⟩,⟨987848, by decide⟩,⟨988185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4673_988186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4673 ⟨988186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4673
    ⟨988186, by decide⟩ (by decide) (![⟨987497, by decide⟩,⟨893098, by decide⟩,⟨987848, by decide⟩,⟨988185, by decide⟩]) unmarked_context_9_4673_988186 node_context_9_4673_988186
  intro a
  fin_cases a
  · exact context_10_18692_987497
  · exact context_10_18693_893098
  · exact context_10_18694_987848
  · exact context_10_18695_988185

theorem selected_cut_37020 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74784) = some ⟨11, 1, 0, 907917, 74784, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74784_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74784 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74784 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74784, 1, 262144⟩
    (by decide) selected_cut_37020

theorem selected_cut_37021 : selected 9 ⟨988203, by decide⟩
    (prefixPartial 12 299140) = some ⟨12, 2, 0, 988203, 299140, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_299140_988203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299140 ⟨988203, by decide⟩ :=
  accepted_of_selected 12 299140 ⟨988203, by decide⟩ ⟨12, 2, 0, 988203, 299140, 1221, 65536⟩
    (by decide) selected_cut_37021

theorem selected_cut_37022 : selected 9 ⟨988233, by decide⟩
    (prefixPartial 12 299141) = some ⟨12, 2, 0, 988233, 299141, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_299141_988233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299141 ⟨988233, by decide⟩ :=
  accepted_of_selected 12 299141 ⟨988233, by decide⟩ ⟨12, 2, 0, 988233, 299141, 1421, 65536⟩
    (by decide) selected_cut_37022

theorem selected_cut_37023 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 299142) = some ⟨12, 1, 0, 984676, 299142, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299142_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299142 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 299142 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 299142, 1, 65536⟩
    (by decide) selected_cut_37023

theorem selected_cut_37024 : selected 9 ⟨988261, by decide⟩
    (prefixPartial 12 299143) = some ⟨12, 2, 0, 988261, 299143, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_299143_988261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299143 ⟨988261, by decide⟩ :=
  accepted_of_selected 12 299143 ⟨988261, by decide⟩ ⟨12, 2, 0, 988261, 299143, 1477, 65536⟩
    (by decide) selected_cut_37024

theorem unmarked_context_11_74785_988262 : frontier 10 ⟨988262, by decide⟩
    (prefixCache 11 74785) (prefixPartial 11 74785) = false := by
  decide +kernel

theorem node_context_11_74785_988262 : EJMOriginalGlobalDAGData.nodes 10 ⟨988262, by decide⟩ =
    .split (coordinate 11) (![⟨988203, by decide⟩,⟨988233, by decide⟩,⟨984676, by decide⟩,⟨988261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74785_988262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74785 ⟨988262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74785
    ⟨988262, by decide⟩ (by decide) (![⟨988203, by decide⟩,⟨988233, by decide⟩,⟨984676, by decide⟩,⟨988261, by decide⟩]) unmarked_context_11_74785_988262 node_context_11_74785_988262
  intro a
  fin_cases a
  · exact context_12_299140_988203
  · exact context_12_299141_988233
  · exact context_12_299142_984676
  · exact context_12_299143_988261

theorem selected_cut_37025 : selected 9 ⟨988275, by decide⟩
    (prefixPartial 12 299144) = some ⟨12, 2, 0, 988275, 299144, 1093, 65536⟩ := by
  decide +kernel

theorem context_12_299144_988275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299144 ⟨988275, by decide⟩ :=
  accepted_of_selected 12 299144 ⟨988275, by decide⟩ ⟨12, 2, 0, 988275, 299144, 1093, 65536⟩
    (by decide) selected_cut_37025

theorem selected_cut_37026 : selected 9 ⟨988300, by decide⟩
    (prefixPartial 12 299145) = some ⟨12, 2, 0, 988300, 299145, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_299145_988300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299145 ⟨988300, by decide⟩ :=
  accepted_of_selected 12 299145 ⟨988300, by decide⟩ ⟨12, 2, 0, 988300, 299145, 1453, 65536⟩
    (by decide) selected_cut_37026

theorem selected_cut_37027 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 299146) = some ⟨12, 1, 0, 984676, 299146, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299146_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299146 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 299146 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 299146, 1, 65536⟩
    (by decide) selected_cut_37027

theorem selected_cut_37028 : selected 9 ⟨988323, by decide⟩
    (prefixPartial 12 299147) = some ⟨12, 2, 0, 988323, 299147, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_299147_988323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299147 ⟨988323, by decide⟩ :=
  accepted_of_selected 12 299147 ⟨988323, by decide⟩ ⟨12, 2, 0, 988323, 299147, 1613, 65536⟩
    (by decide) selected_cut_37028

theorem unmarked_context_11_74786_988324 : frontier 10 ⟨988324, by decide⟩
    (prefixCache 11 74786) (prefixPartial 11 74786) = false := by
  decide +kernel

theorem node_context_11_74786_988324 : EJMOriginalGlobalDAGData.nodes 10 ⟨988324, by decide⟩ =
    .split (coordinate 11) (![⟨988275, by decide⟩,⟨988300, by decide⟩,⟨984676, by decide⟩,⟨988323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74786_988324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74786 ⟨988324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74786
    ⟨988324, by decide⟩ (by decide) (![⟨988275, by decide⟩,⟨988300, by decide⟩,⟨984676, by decide⟩,⟨988323, by decide⟩]) unmarked_context_11_74786_988324 node_context_11_74786_988324
  intro a
  fin_cases a
  · exact context_12_299144_988275
  · exact context_12_299145_988300
  · exact context_12_299146_984676
  · exact context_12_299147_988323

theorem selected_cut_37029 : selected 10 ⟨988378, by decide⟩
    (prefixPartial 11 74787) = some ⟨11, 2, 0, 988378, 74787, 3757, 262144⟩ := by
  decide +kernel

theorem context_11_74787_988378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74787 ⟨988378, by decide⟩ :=
  accepted_of_selected 11 74787 ⟨988378, by decide⟩ ⟨11, 2, 0, 988378, 74787, 3757, 262144⟩
    (by decide) selected_cut_37029

theorem unmarked_context_10_18696_988379 : frontier 11 ⟨988379, by decide⟩
    (prefixCache 10 18696) (prefixPartial 10 18696) = false := by
  decide +kernel

theorem node_context_10_18696_988379 : EJMOriginalGlobalDAGData.nodes 11 ⟨988379, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨988262, by decide⟩,⟨988324, by decide⟩,⟨988378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18696_988379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18696 ⟨988379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18696
    ⟨988379, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨988262, by decide⟩,⟨988324, by decide⟩,⟨988378, by decide⟩]) unmarked_context_10_18696_988379 node_context_10_18696_988379
  intro a
  fin_cases a
  · exact context_11_74784_907917
  · exact context_11_74785_988262
  · exact context_11_74786_988324
  · exact context_11_74787_988378

theorem selected_cut_37030 : selected 10 ⟨988412, by decide⟩
    (prefixPartial 11 74788) = some ⟨11, 2, 0, 988412, 74788, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_74788_988412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74788 ⟨988412, by decide⟩ :=
  accepted_of_selected 11 74788 ⟨988412, by decide⟩ ⟨11, 2, 0, 988412, 74788, 2113, 262144⟩
    (by decide) selected_cut_37030

theorem selected_cut_37031 : selected 10 ⟨988441, by decide⟩
    (prefixPartial 11 74789) = some ⟨11, 2, 0, 988441, 74789, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_74789_988441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74789 ⟨988441, by decide⟩ :=
  accepted_of_selected 11 74789 ⟨988441, by decide⟩ ⟨11, 2, 0, 988441, 74789, 2057, 262144⟩
    (by decide) selected_cut_37031

theorem selected_cut_37032 : selected 10 ⟨988492, by decide⟩
    (prefixPartial 11 74790) = some ⟨11, 2, 0, 988492, 74790, 3325, 262144⟩ := by
  decide +kernel

theorem context_11_74790_988492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74790 ⟨988492, by decide⟩ :=
  accepted_of_selected 11 74790 ⟨988492, by decide⟩ ⟨11, 2, 0, 988492, 74790, 3325, 262144⟩
    (by decide) selected_cut_37032

theorem selected_cut_37033 : selected 10 ⟨988537, by decide⟩
    (prefixPartial 11 74791) = some ⟨11, 2, 0, 988537, 74791, 3337, 262144⟩ := by
  decide +kernel

theorem context_11_74791_988537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74791 ⟨988537, by decide⟩ :=
  accepted_of_selected 11 74791 ⟨988537, by decide⟩ ⟨11, 2, 0, 988537, 74791, 3337, 262144⟩
    (by decide) selected_cut_37033

theorem unmarked_context_10_18697_988538 : frontier 11 ⟨988538, by decide⟩
    (prefixCache 10 18697) (prefixPartial 10 18697) = false := by
  decide +kernel

theorem node_context_10_18697_988538 : EJMOriginalGlobalDAGData.nodes 11 ⟨988538, by decide⟩ =
    .split (coordinate 10) (![⟨988412, by decide⟩,⟨988441, by decide⟩,⟨988492, by decide⟩,⟨988537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18697_988538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18697 ⟨988538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18697
    ⟨988538, by decide⟩ (by decide) (![⟨988412, by decide⟩,⟨988441, by decide⟩,⟨988492, by decide⟩,⟨988537, by decide⟩]) unmarked_context_10_18697_988538 node_context_10_18697_988538
  intro a
  fin_cases a
  · exact context_11_74788_988412
  · exact context_11_74789_988441
  · exact context_11_74790_988492
  · exact context_11_74791_988537

theorem selected_cut_37034 : selected 10 ⟨988560, by decide⟩
    (prefixPartial 11 74792) = some ⟨11, 2, 0, 988560, 74792, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_74792_988560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74792 ⟨988560, by decide⟩ :=
  accepted_of_selected 11 74792 ⟨988560, by decide⟩ ⟨11, 2, 0, 988560, 74792, 1821, 262144⟩
    (by decide) selected_cut_37034

theorem selected_cut_37035 : selected 10 ⟨988603, by decide⟩
    (prefixPartial 11 74793) = some ⟨11, 2, 0, 988603, 74793, 2881, 262144⟩ := by
  decide +kernel

theorem context_11_74793_988603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74793 ⟨988603, by decide⟩ :=
  accepted_of_selected 11 74793 ⟨988603, by decide⟩ ⟨11, 2, 0, 988603, 74793, 2881, 262144⟩
    (by decide) selected_cut_37035

theorem selected_cut_37036 : selected 10 ⟨988643, by decide⟩
    (prefixPartial 11 74794) = some ⟨11, 2, 0, 988643, 74794, 2917, 262144⟩ := by
  decide +kernel

theorem context_11_74794_988643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74794 ⟨988643, by decide⟩ :=
  accepted_of_selected 11 74794 ⟨988643, by decide⟩ ⟨11, 2, 0, 988643, 74794, 2917, 262144⟩
    (by decide) selected_cut_37036

theorem selected_cut_37037 : selected 10 ⟨988678, by decide⟩
    (prefixPartial 11 74795) = some ⟨11, 2, 0, 988678, 74795, 2541, 262144⟩ := by
  decide +kernel

theorem context_11_74795_988678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74795 ⟨988678, by decide⟩ :=
  accepted_of_selected 11 74795 ⟨988678, by decide⟩ ⟨11, 2, 0, 988678, 74795, 2541, 262144⟩
    (by decide) selected_cut_37037

theorem unmarked_context_10_18698_988679 : frontier 11 ⟨988679, by decide⟩
    (prefixCache 10 18698) (prefixPartial 10 18698) = false := by
  decide +kernel

theorem node_context_10_18698_988679 : EJMOriginalGlobalDAGData.nodes 11 ⟨988679, by decide⟩ =
    .split (coordinate 10) (![⟨988560, by decide⟩,⟨988603, by decide⟩,⟨988643, by decide⟩,⟨988678, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18698_988679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18698 ⟨988679, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18698
    ⟨988679, by decide⟩ (by decide) (![⟨988560, by decide⟩,⟨988603, by decide⟩,⟨988643, by decide⟩,⟨988678, by decide⟩]) unmarked_context_10_18698_988679 node_context_10_18698_988679
  intro a
  fin_cases a
  · exact context_11_74792_988560
  · exact context_11_74793_988603
  · exact context_11_74794_988643
  · exact context_11_74795_988678

theorem selected_cut_37038 : selected 10 ⟨988702, by decide⟩
    (prefixPartial 11 74796) = some ⟨11, 2, 0, 988702, 74796, 1505, 262144⟩ := by
  decide +kernel

theorem context_11_74796_988702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74796 ⟨988702, by decide⟩ :=
  accepted_of_selected 11 74796 ⟨988702, by decide⟩ ⟨11, 2, 0, 988702, 74796, 1505, 262144⟩
    (by decide) selected_cut_37038

theorem selected_cut_37039 : selected 10 ⟨988736, by decide⟩
    (prefixPartial 11 74797) = some ⟨11, 2, 0, 988736, 74797, 2385, 262144⟩ := by
  decide +kernel

theorem context_11_74797_988736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74797 ⟨988736, by decide⟩ :=
  accepted_of_selected 11 74797 ⟨988736, by decide⟩ ⟨11, 2, 0, 988736, 74797, 2385, 262144⟩
    (by decide) selected_cut_37039

theorem selected_cut_37040 : selected 10 ⟨988771, by decide⟩
    (prefixPartial 11 74798) = some ⟨11, 2, 0, 988771, 74798, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_74798_988771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74798 ⟨988771, by decide⟩ :=
  accepted_of_selected 11 74798 ⟨988771, by decide⟩ ⟨11, 2, 0, 988771, 74798, 2397, 262144⟩
    (by decide) selected_cut_37040

theorem selected_cut_37041 : selected 10 ⟨988793, by decide⟩
    (prefixPartial 11 74799) = some ⟨11, 2, 0, 988793, 74799, 1413, 262144⟩ := by
  decide +kernel

theorem context_11_74799_988793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74799 ⟨988793, by decide⟩ :=
  accepted_of_selected 11 74799 ⟨988793, by decide⟩ ⟨11, 2, 0, 988793, 74799, 1413, 262144⟩
    (by decide) selected_cut_37041

theorem unmarked_context_10_18699_988794 : frontier 11 ⟨988794, by decide⟩
    (prefixCache 10 18699) (prefixPartial 10 18699) = false := by
  decide +kernel

theorem node_context_10_18699_988794 : EJMOriginalGlobalDAGData.nodes 11 ⟨988794, by decide⟩ =
    .split (coordinate 10) (![⟨988702, by decide⟩,⟨988736, by decide⟩,⟨988771, by decide⟩,⟨988793, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18699_988794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18699 ⟨988794, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18699
    ⟨988794, by decide⟩ (by decide) (![⟨988702, by decide⟩,⟨988736, by decide⟩,⟨988771, by decide⟩,⟨988793, by decide⟩]) unmarked_context_10_18699_988794 node_context_10_18699_988794
  intro a
  fin_cases a
  · exact context_11_74796_988702
  · exact context_11_74797_988736
  · exact context_11_74798_988771
  · exact context_11_74799_988793

theorem unmarked_context_9_4674_988795 : frontier 12 ⟨988795, by decide⟩
    (prefixCache 9 4674) (prefixPartial 9 4674) = false := by
  decide +kernel

theorem node_context_9_4674_988795 : EJMOriginalGlobalDAGData.nodes 12 ⟨988795, by decide⟩ =
    .split (coordinate 9) (![⟨988379, by decide⟩,⟨988538, by decide⟩,⟨988679, by decide⟩,⟨988794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4674_988795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4674 ⟨988795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4674
    ⟨988795, by decide⟩ (by decide) (![⟨988379, by decide⟩,⟨988538, by decide⟩,⟨988679, by decide⟩,⟨988794, by decide⟩]) unmarked_context_9_4674_988795 node_context_9_4674_988795
  intro a
  fin_cases a
  · exact context_10_18696_988379
  · exact context_10_18697_988538
  · exact context_10_18698_988679
  · exact context_10_18699_988794

theorem selected_cut_37042 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74800) = some ⟨11, 1, 0, 907917, 74800, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74800_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74800 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74800 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74800, 1, 262144⟩
    (by decide) selected_cut_37042

theorem selected_cut_37043 : selected 10 ⟨988818, by decide⟩
    (prefixPartial 11 74801) = some ⟨11, 2, 0, 988818, 74801, 2157, 262144⟩ := by
  decide +kernel

theorem context_11_74801_988818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74801 ⟨988818, by decide⟩ :=
  accepted_of_selected 11 74801 ⟨988818, by decide⟩ ⟨11, 2, 0, 988818, 74801, 2157, 262144⟩
    (by decide) selected_cut_37043

theorem selected_cut_37044 : selected 10 ⟨988842, by decide⟩
    (prefixPartial 11 74802) = some ⟨11, 2, 0, 988842, 74802, 2041, 262144⟩ := by
  decide +kernel

theorem context_11_74802_988842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74802 ⟨988842, by decide⟩ :=
  accepted_of_selected 11 74802 ⟨988842, by decide⟩ ⟨11, 2, 0, 988842, 74802, 2041, 262144⟩
    (by decide) selected_cut_37044

theorem selected_cut_37045 : selected 10 ⟨988867, by decide⟩
    (prefixPartial 11 74803) = some ⟨11, 2, 0, 988867, 74803, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_74803_988867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74803 ⟨988867, by decide⟩ :=
  accepted_of_selected 11 74803 ⟨988867, by decide⟩ ⟨11, 2, 0, 988867, 74803, 2057, 262144⟩
    (by decide) selected_cut_37045

theorem unmarked_context_10_18700_988868 : frontier 11 ⟨988868, by decide⟩
    (prefixCache 10 18700) (prefixPartial 10 18700) = false := by
  decide +kernel

theorem node_context_10_18700_988868 : EJMOriginalGlobalDAGData.nodes 11 ⟨988868, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨988818, by decide⟩,⟨988842, by decide⟩,⟨988867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18700_988868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18700 ⟨988868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18700
    ⟨988868, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨988818, by decide⟩,⟨988842, by decide⟩,⟨988867, by decide⟩]) unmarked_context_10_18700_988868 node_context_10_18700_988868
  intro a
  fin_cases a
  · exact context_11_74800_907917
  · exact context_11_74801_988818
  · exact context_11_74802_988842
  · exact context_11_74803_988867

theorem selected_cut_37046 : selected 10 ⟨988878, by decide⟩
    (prefixPartial 11 74804) = some ⟨11, 2, 0, 988878, 74804, 1173, 262144⟩ := by
  decide +kernel

theorem context_11_74804_988878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74804 ⟨988878, by decide⟩ :=
  accepted_of_selected 11 74804 ⟨988878, by decide⟩ ⟨11, 2, 0, 988878, 74804, 1173, 262144⟩
    (by decide) selected_cut_37046

theorem selected_cut_37047 : selected 10 ⟨988889, by decide⟩
    (prefixPartial 11 74805) = some ⟨11, 2, 0, 988889, 74805, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_74805_988889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74805 ⟨988889, by decide⟩ :=
  accepted_of_selected 11 74805 ⟨988889, by decide⟩ ⟨11, 2, 0, 988889, 74805, 1093, 262144⟩
    (by decide) selected_cut_37047

theorem selected_cut_37048 : selected 10 ⟨988903, by decide⟩
    (prefixPartial 11 74806) = some ⟨11, 2, 0, 988903, 74806, 1349, 262144⟩ := by
  decide +kernel

theorem context_11_74806_988903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74806 ⟨988903, by decide⟩ :=
  accepted_of_selected 11 74806 ⟨988903, by decide⟩ ⟨11, 2, 0, 988903, 74806, 1349, 262144⟩
    (by decide) selected_cut_37048

theorem selected_cut_37049 : selected 10 ⟨988924, by decide⟩
    (prefixPartial 11 74807) = some ⟨11, 2, 0, 988924, 74807, 1393, 262144⟩ := by
  decide +kernel

theorem context_11_74807_988924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74807 ⟨988924, by decide⟩ :=
  accepted_of_selected 11 74807 ⟨988924, by decide⟩ ⟨11, 2, 0, 988924, 74807, 1393, 262144⟩
    (by decide) selected_cut_37049

theorem unmarked_context_10_18701_988925 : frontier 11 ⟨988925, by decide⟩
    (prefixCache 10 18701) (prefixPartial 10 18701) = false := by
  decide +kernel

theorem node_context_10_18701_988925 : EJMOriginalGlobalDAGData.nodes 11 ⟨988925, by decide⟩ =
    .split (coordinate 10) (![⟨988878, by decide⟩,⟨988889, by decide⟩,⟨988903, by decide⟩,⟨988924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18701_988925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18701 ⟨988925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18701
    ⟨988925, by decide⟩ (by decide) (![⟨988878, by decide⟩,⟨988889, by decide⟩,⟨988903, by decide⟩,⟨988924, by decide⟩]) unmarked_context_10_18701_988925 node_context_10_18701_988925
  intro a
  fin_cases a
  · exact context_11_74804_988878
  · exact context_11_74805_988889
  · exact context_11_74806_988903
  · exact context_11_74807_988924

theorem selected_cut_37050 : selected 11 ⟨988975, by decide⟩
    (prefixPartial 10 18702) = some ⟨10, 2, 0, 988975, 18702, 3177, 1048576⟩ := by
  decide +kernel

theorem context_10_18702_988975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18702 ⟨988975, by decide⟩ :=
  accepted_of_selected 10 18702 ⟨988975, by decide⟩ ⟨10, 2, 0, 988975, 18702, 3177, 1048576⟩
    (by decide) selected_cut_37050

theorem selected_cut_37051 : selected 11 ⟨989025, by decide⟩
    (prefixPartial 10 18703) = some ⟨10, 2, 0, 989025, 18703, 1241, 1048576⟩ := by
  decide +kernel

theorem context_10_18703_989025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18703 ⟨989025, by decide⟩ :=
  accepted_of_selected 10 18703 ⟨989025, by decide⟩ ⟨10, 2, 0, 989025, 18703, 1241, 1048576⟩
    (by decide) selected_cut_37051

theorem unmarked_context_9_4675_989026 : frontier 12 ⟨989026, by decide⟩
    (prefixCache 9 4675) (prefixPartial 9 4675) = false := by
  decide +kernel

theorem node_context_9_4675_989026 : EJMOriginalGlobalDAGData.nodes 12 ⟨989026, by decide⟩ =
    .split (coordinate 9) (![⟨988868, by decide⟩,⟨988925, by decide⟩,⟨988975, by decide⟩,⟨989025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4675_989026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4675 ⟨989026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4675
    ⟨989026, by decide⟩ (by decide) (![⟨988868, by decide⟩,⟨988925, by decide⟩,⟨988975, by decide⟩,⟨989025, by decide⟩]) unmarked_context_9_4675_989026 node_context_9_4675_989026
  intro a
  fin_cases a
  · exact context_10_18700_988868
  · exact context_10_18701_988925
  · exact context_10_18702_988975
  · exact context_10_18703_989025

theorem unmarked_context_8_1168_989027 : frontier 13 ⟨989027, by decide⟩
    (prefixCache 8 1168) (prefixPartial 8 1168) = false := by
  decide +kernel

theorem node_context_8_1168_989027 : EJMOriginalGlobalDAGData.nodes 13 ⟨989027, by decide⟩ =
    .split (coordinate 8) (![⟨987101, by decide⟩,⟨988186, by decide⟩,⟨988795, by decide⟩,⟨989026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1168_989027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1168 ⟨989027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1168
    ⟨989027, by decide⟩ (by decide) (![⟨987101, by decide⟩,⟨988186, by decide⟩,⟨988795, by decide⟩,⟨989026, by decide⟩]) unmarked_context_8_1168_989027 node_context_8_1168_989027
  intro a
  fin_cases a
  · exact context_9_4672_987101
  · exact context_9_4673_988186
  · exact context_9_4674_988795
  · exact context_9_4675_989026

theorem selected_cut_37052 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 74816) = some ⟨11, 1, 0, 167448, 74816, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74816_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74816 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 74816 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 74816, 1, 262144⟩
    (by decide) selected_cut_37052

theorem selected_cut_37053 : selected 8 ⟨989078, by decide⟩
    (prefixPartial 13 1197072) = some ⟨13, 2, 0, 989078, 1197072, 1821, 16384⟩ := by
  decide +kernel

theorem context_13_1197072_989078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197072 ⟨989078, by decide⟩ :=
  accepted_of_selected 13 1197072 ⟨989078, by decide⟩ ⟨13, 2, 0, 989078, 1197072, 1821, 16384⟩
    (by decide) selected_cut_37053

theorem selected_cut_37054 : selected 8 ⟨989110, by decide⟩
    (prefixPartial 13 1197073) = some ⟨13, 2, 0, 989110, 1197073, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_1197073_989110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197073 ⟨989110, by decide⟩ :=
  accepted_of_selected 13 1197073 ⟨989110, by decide⟩ ⟨13, 2, 0, 989110, 1197073, 1445, 16384⟩
    (by decide) selected_cut_37054

theorem selected_cut_37055 : selected 8 ⟨989131, by decide⟩
    (prefixPartial 13 1197074) = some ⟨13, 2, 0, 989131, 1197074, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_1197074_989131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197074 ⟨989131, by decide⟩ :=
  accepted_of_selected 13 1197074 ⟨989131, by decide⟩ ⟨13, 2, 0, 989131, 1197074, 1033, 16384⟩
    (by decide) selected_cut_37055

theorem selected_cut_37056 : selected 8 ⟨989138, by decide⟩
    (prefixPartial 13 1197075) = some ⟨13, 2, 0, 989138, 1197075, 625, 16384⟩ := by
  decide +kernel

theorem context_13_1197075_989138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1197075 ⟨989138, by decide⟩ :=
  accepted_of_selected 13 1197075 ⟨989138, by decide⟩ ⟨13, 2, 0, 989138, 1197075, 625, 16384⟩
    (by decide) selected_cut_37056

theorem unmarked_context_12_299268_989139 : frontier 9 ⟨989139, by decide⟩
    (prefixCache 12 299268) (prefixPartial 12 299268) = false := by
  decide +kernel

theorem node_context_12_299268_989139 : EJMOriginalGlobalDAGData.nodes 9 ⟨989139, by decide⟩ =
    .split (coordinate 12) (![⟨989078, by decide⟩,⟨989110, by decide⟩,⟨989131, by decide⟩,⟨989138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299268_989139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299268 ⟨989139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299268
    ⟨989139, by decide⟩ (by decide) (![⟨989078, by decide⟩,⟨989110, by decide⟩,⟨989131, by decide⟩,⟨989138, by decide⟩]) unmarked_context_12_299268_989139 node_context_12_299268_989139
  intro a
  fin_cases a
  · exact context_13_1197072_989078
  · exact context_13_1197073_989110
  · exact context_13_1197074_989131
  · exact context_13_1197075_989138

theorem selected_cut_37057 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 299269) = some ⟨12, 1, 0, 891951, 299269, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299269_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299269 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 299269 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 299269, 1, 65536⟩
    (by decide) selected_cut_37057

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
