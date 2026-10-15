/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover540
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_51938 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71360) = some ⟨10, 1, 0, 1468246, 71360, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71360_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71360 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71360 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71360, 1, 1048576⟩
    (by decide) selected_cut_51938

theorem selected_cut_51939 : selected 10 ⟨1503698, by decide⟩
    (prefixPartial 11 285444) = some ⟨11, 2, 0, 1503698, 285444, 2929, 262144⟩ := by
  decide +kernel

theorem context_11_285444_1503698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285444 ⟨1503698, by decide⟩ :=
  accepted_of_selected 11 285444 ⟨1503698, by decide⟩ ⟨11, 2, 0, 1503698, 285444, 2929, 262144⟩
    (by decide) selected_cut_51939

theorem selected_cut_51940 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285445) = some ⟨11, 1, 0, 1468419, 285445, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285445_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285445 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285445 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285445, 1, 262144⟩
    (by decide) selected_cut_51940

theorem selected_cut_51941 : selected 10 ⟨1503788, by decide⟩
    (prefixPartial 11 285446) = some ⟨11, 2, 0, 1503788, 285446, 2953, 262144⟩ := by
  decide +kernel

theorem context_11_285446_1503788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285446 ⟨1503788, by decide⟩ :=
  accepted_of_selected 11 285446 ⟨1503788, by decide⟩ ⟨11, 2, 0, 1503788, 285446, 2953, 262144⟩
    (by decide) selected_cut_51941

theorem selected_cut_51942 : selected 10 ⟨1503813, by decide⟩
    (prefixPartial 11 285447) = some ⟨11, 2, 0, 1503813, 285447, 1237, 262144⟩ := by
  decide +kernel

theorem context_11_285447_1503813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285447 ⟨1503813, by decide⟩ :=
  accepted_of_selected 11 285447 ⟨1503813, by decide⟩ ⟨11, 2, 0, 1503813, 285447, 1237, 262144⟩
    (by decide) selected_cut_51942

theorem unmarked_context_10_71361_1503814 : frontier 11 ⟨1503814, by decide⟩
    (prefixCache 10 71361) (prefixPartial 10 71361) = false := by
  decide +kernel

theorem node_context_10_71361_1503814 : EJMOriginalGlobalDAGData.nodes 11 ⟨1503814, by decide⟩ =
    .split (coordinate 10) (![⟨1503698, by decide⟩,⟨1468419, by decide⟩,⟨1503788, by decide⟩,⟨1503813, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71361_1503814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71361 ⟨1503814, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71361
    ⟨1503814, by decide⟩ (by decide) (![⟨1503698, by decide⟩,⟨1468419, by decide⟩,⟨1503788, by decide⟩,⟨1503813, by decide⟩]) unmarked_context_10_71361_1503814 node_context_10_71361_1503814
  intro a
  fin_cases a
  · exact context_11_285444_1503698
  · exact context_11_285445_1468419
  · exact context_11_285446_1503788
  · exact context_11_285447_1503813

theorem selected_cut_51943 : selected 10 ⟨1503869, by decide⟩
    (prefixPartial 11 285448) = some ⟨11, 2, 0, 1503869, 285448, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_285448_1503869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285448 ⟨1503869, by decide⟩ :=
  accepted_of_selected 11 285448 ⟨1503869, by decide⟩ ⟨11, 2, 0, 1503869, 285448, 2521, 262144⟩
    (by decide) selected_cut_51943

theorem selected_cut_51944 : selected 10 ⟨1503923, by decide⟩
    (prefixPartial 11 285449) = some ⟨11, 2, 0, 1503923, 285449, 2409, 262144⟩ := by
  decide +kernel

theorem context_11_285449_1503923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285449 ⟨1503923, by decide⟩ :=
  accepted_of_selected 11 285449 ⟨1503923, by decide⟩ ⟨11, 2, 0, 1503923, 285449, 2409, 262144⟩
    (by decide) selected_cut_51944

theorem selected_cut_51945 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285450) = some ⟨11, 1, 0, 1468743, 285450, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285450_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285450 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285450 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285450, 1, 262144⟩
    (by decide) selected_cut_51945

theorem selected_cut_51946 : selected 10 ⟨1503962, by decide⟩
    (prefixPartial 11 285451) = some ⟨11, 2, 0, 1503962, 285451, 2069, 262144⟩ := by
  decide +kernel

theorem context_11_285451_1503962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285451 ⟨1503962, by decide⟩ :=
  accepted_of_selected 11 285451 ⟨1503962, by decide⟩ ⟨11, 2, 0, 1503962, 285451, 2069, 262144⟩
    (by decide) selected_cut_51946

theorem unmarked_context_10_71362_1503963 : frontier 11 ⟨1503963, by decide⟩
    (prefixCache 10 71362) (prefixPartial 10 71362) = false := by
  decide +kernel

theorem node_context_10_71362_1503963 : EJMOriginalGlobalDAGData.nodes 11 ⟨1503963, by decide⟩ =
    .split (coordinate 10) (![⟨1503869, by decide⟩,⟨1503923, by decide⟩,⟨1468743, by decide⟩,⟨1503962, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71362_1503963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71362 ⟨1503963, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71362
    ⟨1503963, by decide⟩ (by decide) (![⟨1503869, by decide⟩,⟨1503923, by decide⟩,⟨1468743, by decide⟩,⟨1503962, by decide⟩]) unmarked_context_10_71362_1503963 node_context_10_71362_1503963
  intro a
  fin_cases a
  · exact context_11_285448_1503869
  · exact context_11_285449_1503923
  · exact context_11_285450_1468743
  · exact context_11_285451_1503962

theorem selected_cut_51947 : selected 10 ⟨1503964, by decide⟩
    (prefixPartial 11 285452) = some ⟨11, 2, 0, 1503964, 285452, 5, 262144⟩ := by
  decide +kernel

theorem context_11_285452_1503964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285452 ⟨1503964, by decide⟩ :=
  accepted_of_selected 11 285452 ⟨1503964, by decide⟩ ⟨11, 2, 0, 1503964, 285452, 5, 262144⟩
    (by decide) selected_cut_51947

theorem selected_cut_51948 : selected 10 ⟨1504011, by decide⟩
    (prefixPartial 11 285453) = some ⟨11, 2, 0, 1504011, 285453, 2305, 262144⟩ := by
  decide +kernel

theorem context_11_285453_1504011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285453 ⟨1504011, by decide⟩ :=
  accepted_of_selected 11 285453 ⟨1504011, by decide⟩ ⟨11, 2, 0, 1504011, 285453, 2305, 262144⟩
    (by decide) selected_cut_51948

theorem selected_cut_51949 : selected 10 ⟨1504058, by decide⟩
    (prefixPartial 11 285454) = some ⟨11, 2, 0, 1504058, 285454, 2137, 262144⟩ := by
  decide +kernel

theorem context_11_285454_1504058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285454 ⟨1504058, by decide⟩ :=
  accepted_of_selected 11 285454 ⟨1504058, by decide⟩ ⟨11, 2, 0, 1504058, 285454, 2137, 262144⟩
    (by decide) selected_cut_51949

theorem selected_cut_51950 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285455) = some ⟨11, 1, 0, 1470044, 285455, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285455_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285455 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285455 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285455, 1, 262144⟩
    (by decide) selected_cut_51950

theorem unmarked_context_10_71363_1504059 : frontier 11 ⟨1504059, by decide⟩
    (prefixCache 10 71363) (prefixPartial 10 71363) = false := by
  decide +kernel

theorem node_context_10_71363_1504059 : EJMOriginalGlobalDAGData.nodes 11 ⟨1504059, by decide⟩ =
    .split (coordinate 10) (![⟨1503964, by decide⟩,⟨1504011, by decide⟩,⟨1504058, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71363_1504059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71363 ⟨1504059, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71363
    ⟨1504059, by decide⟩ (by decide) (![⟨1503964, by decide⟩,⟨1504011, by decide⟩,⟨1504058, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71363_1504059 node_context_10_71363_1504059
  intro a
  fin_cases a
  · exact context_11_285452_1503964
  · exact context_11_285453_1504011
  · exact context_11_285454_1504058
  · exact context_11_285455_1470044

theorem unmarked_context_9_17840_1504060 : frontier 12 ⟨1504060, by decide⟩
    (prefixCache 9 17840) (prefixPartial 9 17840) = false := by
  decide +kernel

theorem node_context_9_17840_1504060 : EJMOriginalGlobalDAGData.nodes 12 ⟨1504060, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1503814, by decide⟩,⟨1503963, by decide⟩,⟨1504059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17840_1504060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17840 ⟨1504060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17840
    ⟨1504060, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1503814, by decide⟩,⟨1503963, by decide⟩,⟨1504059, by decide⟩]) unmarked_context_9_17840_1504060 node_context_9_17840_1504060
  intro a
  fin_cases a
  · exact context_10_71360_1468246
  · exact context_10_71361_1503814
  · exact context_10_71362_1503963
  · exact context_10_71363_1504059

theorem selected_cut_51951 : selected 11 ⟨1504119, by decide⟩
    (prefixPartial 10 71364) = some ⟨10, 2, 0, 1504119, 71364, 3025, 1048576⟩ := by
  decide +kernel

theorem context_10_71364_1504119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71364 ⟨1504119, by decide⟩ :=
  accepted_of_selected 10 71364 ⟨1504119, by decide⟩ ⟨10, 2, 0, 1504119, 71364, 3025, 1048576⟩
    (by decide) selected_cut_51951

theorem selected_cut_51952 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71365) = some ⟨10, 1, 0, 1468874, 71365, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71365_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71365 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71365 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71365, 1, 1048576⟩
    (by decide) selected_cut_51952

theorem selected_cut_51953 : selected 10 ⟨1504149, by decide⟩
    (prefixPartial 11 285464) = some ⟨11, 2, 0, 1504149, 285464, 1409, 262144⟩ := by
  decide +kernel

theorem context_11_285464_1504149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285464 ⟨1504149, by decide⟩ :=
  accepted_of_selected 11 285464 ⟨1504149, by decide⟩ ⟨11, 2, 0, 1504149, 285464, 1409, 262144⟩
    (by decide) selected_cut_51953

theorem selected_cut_51954 : selected 10 ⟨1504197, by decide⟩
    (prefixPartial 11 285465) = some ⟨11, 2, 0, 1504197, 285465, 1713, 262144⟩ := by
  decide +kernel

theorem context_11_285465_1504197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285465 ⟨1504197, by decide⟩ :=
  accepted_of_selected 11 285465 ⟨1504197, by decide⟩ ⟨11, 2, 0, 1504197, 285465, 1713, 262144⟩
    (by decide) selected_cut_51954

theorem selected_cut_51955 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285466) = some ⟨11, 1, 0, 1468743, 285466, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285466_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285466 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285466 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285466, 1, 262144⟩
    (by decide) selected_cut_51955

theorem selected_cut_51956 : selected 10 ⟨1504221, by decide⟩
    (prefixPartial 11 285467) = some ⟨11, 2, 0, 1504221, 285467, 1161, 262144⟩ := by
  decide +kernel

theorem context_11_285467_1504221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285467 ⟨1504221, by decide⟩ :=
  accepted_of_selected 11 285467 ⟨1504221, by decide⟩ ⟨11, 2, 0, 1504221, 285467, 1161, 262144⟩
    (by decide) selected_cut_51956

theorem unmarked_context_10_71366_1504222 : frontier 11 ⟨1504222, by decide⟩
    (prefixCache 10 71366) (prefixPartial 10 71366) = false := by
  decide +kernel

theorem node_context_10_71366_1504222 : EJMOriginalGlobalDAGData.nodes 11 ⟨1504222, by decide⟩ =
    .split (coordinate 10) (![⟨1504149, by decide⟩,⟨1504197, by decide⟩,⟨1468743, by decide⟩,⟨1504221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71366_1504222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71366 ⟨1504222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71366
    ⟨1504222, by decide⟩ (by decide) (![⟨1504149, by decide⟩,⟨1504197, by decide⟩,⟨1468743, by decide⟩,⟨1504221, by decide⟩]) unmarked_context_10_71366_1504222 node_context_10_71366_1504222
  intro a
  fin_cases a
  · exact context_11_285464_1504149
  · exact context_11_285465_1504197
  · exact context_11_285466_1468743
  · exact context_11_285467_1504221

theorem selected_cut_51957 : selected 11 ⟨1504284, by decide⟩
    (prefixPartial 10 71367) = some ⟨10, 2, 0, 1504284, 71367, 2965, 1048576⟩ := by
  decide +kernel

theorem context_10_71367_1504284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71367 ⟨1504284, by decide⟩ :=
  accepted_of_selected 10 71367 ⟨1504284, by decide⟩ ⟨10, 2, 0, 1504284, 71367, 2965, 1048576⟩
    (by decide) selected_cut_51957

theorem unmarked_context_9_17841_1504285 : frontier 12 ⟨1504285, by decide⟩
    (prefixCache 9 17841) (prefixPartial 9 17841) = false := by
  decide +kernel

theorem node_context_9_17841_1504285 : EJMOriginalGlobalDAGData.nodes 12 ⟨1504285, by decide⟩ =
    .split (coordinate 9) (![⟨1504119, by decide⟩,⟨1468874, by decide⟩,⟨1504222, by decide⟩,⟨1504284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17841_1504285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17841 ⟨1504285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17841
    ⟨1504285, by decide⟩ (by decide) (![⟨1504119, by decide⟩,⟨1468874, by decide⟩,⟨1504222, by decide⟩,⟨1504284, by decide⟩]) unmarked_context_9_17841_1504285 node_context_9_17841_1504285
  intro a
  fin_cases a
  · exact context_10_71364_1504119
  · exact context_10_71365_1468874
  · exact context_10_71366_1504222
  · exact context_10_71367_1504284

theorem selected_cut_51958 : selected 11 ⟨1504360, by decide⟩
    (prefixPartial 10 71368) = some ⟨10, 2, 0, 1504360, 71368, 3245, 1048576⟩ := by
  decide +kernel

theorem context_10_71368_1504360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71368 ⟨1504360, by decide⟩ :=
  accepted_of_selected 10 71368 ⟨1504360, by decide⟩ ⟨10, 2, 0, 1504360, 71368, 3245, 1048576⟩
    (by decide) selected_cut_51958

theorem selected_cut_51959 : selected 11 ⟨1504446, by decide⟩
    (prefixPartial 10 71369) = some ⟨10, 2, 0, 1504446, 71369, 3501, 1048576⟩ := by
  decide +kernel

theorem context_10_71369_1504446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71369 ⟨1504446, by decide⟩ :=
  accepted_of_selected 10 71369 ⟨1504446, by decide⟩ ⟨10, 2, 0, 1504446, 71369, 3501, 1048576⟩
    (by decide) selected_cut_51959

theorem selected_cut_51960 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71370) = some ⟨10, 1, 0, 1469103, 71370, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71370_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71370 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71370 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71370, 1, 1048576⟩
    (by decide) selected_cut_51960

theorem selected_cut_51961 : selected 11 ⟨1504509, by decide⟩
    (prefixPartial 10 71371) = some ⟨10, 2, 0, 1504509, 71371, 2045, 1048576⟩ := by
  decide +kernel

theorem context_10_71371_1504509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71371 ⟨1504509, by decide⟩ :=
  accepted_of_selected 10 71371 ⟨1504509, by decide⟩ ⟨10, 2, 0, 1504509, 71371, 2045, 1048576⟩
    (by decide) selected_cut_51961

theorem unmarked_context_9_17842_1504510 : frontier 12 ⟨1504510, by decide⟩
    (prefixCache 9 17842) (prefixPartial 9 17842) = false := by
  decide +kernel

theorem node_context_9_17842_1504510 : EJMOriginalGlobalDAGData.nodes 12 ⟨1504510, by decide⟩ =
    .split (coordinate 9) (![⟨1504360, by decide⟩,⟨1504446, by decide⟩,⟨1469103, by decide⟩,⟨1504509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17842_1504510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17842 ⟨1504510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17842
    ⟨1504510, by decide⟩ (by decide) (![⟨1504360, by decide⟩,⟨1504446, by decide⟩,⟨1469103, by decide⟩,⟨1504509, by decide⟩]) unmarked_context_9_17842_1504510 node_context_9_17842_1504510
  intro a
  fin_cases a
  · exact context_10_71368_1504360
  · exact context_10_71369_1504446
  · exact context_10_71370_1469103
  · exact context_10_71371_1504509

theorem selected_cut_51962 : selected 12 ⟨1504562, by decide⟩
    (prefixPartial 9 17843) = some ⟨9, 2, 0, 1504562, 17843, 2109, 4194304⟩ := by
  decide +kernel

theorem context_9_17843_1504562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17843 ⟨1504562, by decide⟩ :=
  accepted_of_selected 9 17843 ⟨1504562, by decide⟩ ⟨9, 2, 0, 1504562, 17843, 2109, 4194304⟩
    (by decide) selected_cut_51962

theorem unmarked_context_8_4460_1504563 : frontier 13 ⟨1504563, by decide⟩
    (prefixCache 8 4460) (prefixPartial 8 4460) = false := by
  decide +kernel

theorem node_context_8_4460_1504563 : EJMOriginalGlobalDAGData.nodes 13 ⟨1504563, by decide⟩ =
    .split (coordinate 8) (![⟨1504060, by decide⟩,⟨1504285, by decide⟩,⟨1504510, by decide⟩,⟨1504562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4460_1504563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4460 ⟨1504563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4460
    ⟨1504563, by decide⟩ (by decide) (![⟨1504060, by decide⟩,⟨1504285, by decide⟩,⟨1504510, by decide⟩,⟨1504562, by decide⟩]) unmarked_context_8_4460_1504563 node_context_8_4460_1504563
  intro a
  fin_cases a
  · exact context_9_17840_1504060
  · exact context_9_17841_1504285
  · exact context_9_17842_1504510
  · exact context_9_17843_1504562

theorem selected_cut_51963 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71376) = some ⟨10, 1, 0, 1468246, 71376, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71376_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71376 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71376 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71376, 1, 1048576⟩
    (by decide) selected_cut_51963

theorem selected_cut_51964 : selected 10 ⟨1504634, by decide⟩
    (prefixPartial 11 285508) = some ⟨11, 2, 0, 1504634, 285508, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_285508_1504634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285508 ⟨1504634, by decide⟩ :=
  accepted_of_selected 11 285508 ⟨1504634, by decide⟩ ⟨11, 2, 0, 1504634, 285508, 2857, 262144⟩
    (by decide) selected_cut_51964

theorem selected_cut_51965 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285509) = some ⟨11, 1, 0, 1468419, 285509, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285509_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285509 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285509 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285509, 1, 262144⟩
    (by decide) selected_cut_51965

theorem selected_cut_51966 : selected 10 ⟨1504690, by decide⟩
    (prefixPartial 11 285510) = some ⟨11, 2, 0, 1504690, 285510, 2517, 262144⟩ := by
  decide +kernel

theorem context_11_285510_1504690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285510 ⟨1504690, by decide⟩ :=
  accepted_of_selected 11 285510 ⟨1504690, by decide⟩ ⟨11, 2, 0, 1504690, 285510, 2517, 262144⟩
    (by decide) selected_cut_51966

theorem selected_cut_51967 : selected 10 ⟨1504714, by decide⟩
    (prefixPartial 11 285511) = some ⟨11, 2, 0, 1504714, 285511, 1257, 262144⟩ := by
  decide +kernel

theorem context_11_285511_1504714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285511 ⟨1504714, by decide⟩ :=
  accepted_of_selected 11 285511 ⟨1504714, by decide⟩ ⟨11, 2, 0, 1504714, 285511, 1257, 262144⟩
    (by decide) selected_cut_51967

theorem unmarked_context_10_71377_1504715 : frontier 11 ⟨1504715, by decide⟩
    (prefixCache 10 71377) (prefixPartial 10 71377) = false := by
  decide +kernel

theorem node_context_10_71377_1504715 : EJMOriginalGlobalDAGData.nodes 11 ⟨1504715, by decide⟩ =
    .split (coordinate 10) (![⟨1504634, by decide⟩,⟨1468419, by decide⟩,⟨1504690, by decide⟩,⟨1504714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71377_1504715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71377 ⟨1504715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71377
    ⟨1504715, by decide⟩ (by decide) (![⟨1504634, by decide⟩,⟨1468419, by decide⟩,⟨1504690, by decide⟩,⟨1504714, by decide⟩]) unmarked_context_10_71377_1504715 node_context_10_71377_1504715
  intro a
  fin_cases a
  · exact context_11_285508_1504634
  · exact context_11_285509_1468419
  · exact context_11_285510_1504690
  · exact context_11_285511_1504714

theorem selected_cut_51968 : selected 10 ⟨1504773, by decide⟩
    (prefixPartial 11 285512) = some ⟨11, 2, 0, 1504773, 285512, 2717, 262144⟩ := by
  decide +kernel

theorem context_11_285512_1504773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285512 ⟨1504773, by decide⟩ :=
  accepted_of_selected 11 285512 ⟨1504773, by decide⟩ ⟨11, 2, 0, 1504773, 285512, 2717, 262144⟩
    (by decide) selected_cut_51968

theorem selected_cut_51969 : selected 10 ⟨1504820, by decide⟩
    (prefixPartial 11 285513) = some ⟨11, 2, 0, 1504820, 285513, 2153, 262144⟩ := by
  decide +kernel

theorem context_11_285513_1504820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285513 ⟨1504820, by decide⟩ :=
  accepted_of_selected 11 285513 ⟨1504820, by decide⟩ ⟨11, 2, 0, 1504820, 285513, 2153, 262144⟩
    (by decide) selected_cut_51969

theorem selected_cut_51970 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285514) = some ⟨11, 1, 0, 1468743, 285514, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285514_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285514 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285514 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285514, 1, 262144⟩
    (by decide) selected_cut_51970

theorem selected_cut_51971 : selected 10 ⟨1504858, by decide⟩
    (prefixPartial 11 285515) = some ⟨11, 2, 0, 1504858, 285515, 2089, 262144⟩ := by
  decide +kernel

theorem context_11_285515_1504858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285515 ⟨1504858, by decide⟩ :=
  accepted_of_selected 11 285515 ⟨1504858, by decide⟩ ⟨11, 2, 0, 1504858, 285515, 2089, 262144⟩
    (by decide) selected_cut_51971

theorem unmarked_context_10_71378_1504859 : frontier 11 ⟨1504859, by decide⟩
    (prefixCache 10 71378) (prefixPartial 10 71378) = false := by
  decide +kernel

theorem node_context_10_71378_1504859 : EJMOriginalGlobalDAGData.nodes 11 ⟨1504859, by decide⟩ =
    .split (coordinate 10) (![⟨1504773, by decide⟩,⟨1504820, by decide⟩,⟨1468743, by decide⟩,⟨1504858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71378_1504859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71378 ⟨1504859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71378
    ⟨1504859, by decide⟩ (by decide) (![⟨1504773, by decide⟩,⟨1504820, by decide⟩,⟨1468743, by decide⟩,⟨1504858, by decide⟩]) unmarked_context_10_71378_1504859 node_context_10_71378_1504859
  intro a
  fin_cases a
  · exact context_11_285512_1504773
  · exact context_11_285513_1504820
  · exact context_11_285514_1468743
  · exact context_11_285515_1504858

theorem selected_cut_51972 : selected 11 ⟨1504938, by decide⟩
    (prefixPartial 10 71379) = some ⟨10, 2, 0, 1504938, 71379, 4045, 1048576⟩ := by
  decide +kernel

theorem context_10_71379_1504938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71379 ⟨1504938, by decide⟩ :=
  accepted_of_selected 10 71379 ⟨1504938, by decide⟩ ⟨10, 2, 0, 1504938, 71379, 4045, 1048576⟩
    (by decide) selected_cut_51972

theorem unmarked_context_9_17844_1504939 : frontier 12 ⟨1504939, by decide⟩
    (prefixCache 9 17844) (prefixPartial 9 17844) = false := by
  decide +kernel

theorem node_context_9_17844_1504939 : EJMOriginalGlobalDAGData.nodes 12 ⟨1504939, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1504715, by decide⟩,⟨1504859, by decide⟩,⟨1504938, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17844_1504939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17844 ⟨1504939, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17844
    ⟨1504939, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1504715, by decide⟩,⟨1504859, by decide⟩,⟨1504938, by decide⟩]) unmarked_context_9_17844_1504939 node_context_9_17844_1504939
  intro a
  fin_cases a
  · exact context_10_71376_1468246
  · exact context_10_71377_1504715
  · exact context_10_71378_1504859
  · exact context_10_71379_1504938

theorem selected_cut_51973 : selected 11 ⟨1505005, by decide⟩
    (prefixPartial 10 71380) = some ⟨10, 2, 0, 1505005, 71380, 2817, 1048576⟩ := by
  decide +kernel

theorem context_10_71380_1505005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71380 ⟨1505005, by decide⟩ :=
  accepted_of_selected 10 71380 ⟨1505005, by decide⟩ ⟨10, 2, 0, 1505005, 71380, 2817, 1048576⟩
    (by decide) selected_cut_51973

theorem selected_cut_51974 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71381) = some ⟨10, 1, 0, 1468874, 71381, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71381_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71381 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71381 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71381, 1, 1048576⟩
    (by decide) selected_cut_51974

theorem selected_cut_51975 : selected 10 ⟨1505037, by decide⟩
    (prefixPartial 11 285528) = some ⟨11, 2, 0, 1505037, 285528, 1681, 262144⟩ := by
  decide +kernel

theorem context_11_285528_1505037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285528 ⟨1505037, by decide⟩ :=
  accepted_of_selected 11 285528 ⟨1505037, by decide⟩ ⟨11, 2, 0, 1505037, 285528, 1681, 262144⟩
    (by decide) selected_cut_51975

theorem selected_cut_51976 : selected 10 ⟨1505077, by decide⟩
    (prefixPartial 11 285529) = some ⟨11, 2, 0, 1505077, 285529, 1809, 262144⟩ := by
  decide +kernel

theorem context_11_285529_1505077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285529 ⟨1505077, by decide⟩ :=
  accepted_of_selected 11 285529 ⟨1505077, by decide⟩ ⟨11, 2, 0, 1505077, 285529, 1809, 262144⟩
    (by decide) selected_cut_51976

theorem selected_cut_51977 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285530) = some ⟨11, 1, 0, 1468743, 285530, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285530_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285530 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285530 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285530, 1, 262144⟩
    (by decide) selected_cut_51977

theorem selected_cut_51978 : selected 10 ⟨1505098, by decide⟩
    (prefixPartial 11 285531) = some ⟨11, 2, 0, 1505098, 285531, 1277, 262144⟩ := by
  decide +kernel

theorem context_11_285531_1505098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285531 ⟨1505098, by decide⟩ :=
  accepted_of_selected 11 285531 ⟨1505098, by decide⟩ ⟨11, 2, 0, 1505098, 285531, 1277, 262144⟩
    (by decide) selected_cut_51978

theorem unmarked_context_10_71382_1505099 : frontier 11 ⟨1505099, by decide⟩
    (prefixCache 10 71382) (prefixPartial 10 71382) = false := by
  decide +kernel

theorem node_context_10_71382_1505099 : EJMOriginalGlobalDAGData.nodes 11 ⟨1505099, by decide⟩ =
    .split (coordinate 10) (![⟨1505037, by decide⟩,⟨1505077, by decide⟩,⟨1468743, by decide⟩,⟨1505098, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71382_1505099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71382 ⟨1505099, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71382
    ⟨1505099, by decide⟩ (by decide) (![⟨1505037, by decide⟩,⟨1505077, by decide⟩,⟨1468743, by decide⟩,⟨1505098, by decide⟩]) unmarked_context_10_71382_1505099 node_context_10_71382_1505099
  intro a
  fin_cases a
  · exact context_11_285528_1505037
  · exact context_11_285529_1505077
  · exact context_11_285530_1468743
  · exact context_11_285531_1505098

theorem selected_cut_51979 : selected 11 ⟨1505171, by decide⟩
    (prefixPartial 10 71383) = some ⟨10, 2, 0, 1505171, 71383, 3437, 1048576⟩ := by
  decide +kernel

theorem context_10_71383_1505171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71383 ⟨1505171, by decide⟩ :=
  accepted_of_selected 10 71383 ⟨1505171, by decide⟩ ⟨10, 2, 0, 1505171, 71383, 3437, 1048576⟩
    (by decide) selected_cut_51979

theorem unmarked_context_9_17845_1505172 : frontier 12 ⟨1505172, by decide⟩
    (prefixCache 9 17845) (prefixPartial 9 17845) = false := by
  decide +kernel

theorem node_context_9_17845_1505172 : EJMOriginalGlobalDAGData.nodes 12 ⟨1505172, by decide⟩ =
    .split (coordinate 9) (![⟨1505005, by decide⟩,⟨1468874, by decide⟩,⟨1505099, by decide⟩,⟨1505171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17845_1505172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17845 ⟨1505172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17845
    ⟨1505172, by decide⟩ (by decide) (![⟨1505005, by decide⟩,⟨1468874, by decide⟩,⟨1505099, by decide⟩,⟨1505171, by decide⟩]) unmarked_context_9_17845_1505172 node_context_9_17845_1505172
  intro a
  fin_cases a
  · exact context_10_71380_1505005
  · exact context_10_71381_1468874
  · exact context_10_71382_1505099
  · exact context_10_71383_1505171

theorem selected_cut_51980 : selected 11 ⟨1505226, by decide⟩
    (prefixPartial 10 71384) = some ⟨10, 2, 0, 1505226, 71384, 2737, 1048576⟩ := by
  decide +kernel

theorem context_10_71384_1505226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71384 ⟨1505226, by decide⟩ :=
  accepted_of_selected 10 71384 ⟨1505226, by decide⟩ ⟨10, 2, 0, 1505226, 71384, 2737, 1048576⟩
    (by decide) selected_cut_51980

theorem selected_cut_51981 : selected 11 ⟨1505269, by decide⟩
    (prefixPartial 10 71385) = some ⟨10, 2, 0, 1505269, 71385, 1957, 1048576⟩ := by
  decide +kernel

theorem context_10_71385_1505269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71385 ⟨1505269, by decide⟩ :=
  accepted_of_selected 10 71385 ⟨1505269, by decide⟩ ⟨10, 2, 0, 1505269, 71385, 1957, 1048576⟩
    (by decide) selected_cut_51981

theorem selected_cut_51982 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71386) = some ⟨10, 1, 0, 1469103, 71386, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71386_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71386 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71386 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71386, 1, 1048576⟩
    (by decide) selected_cut_51982

theorem selected_cut_51983 : selected 11 ⟨1505300, by decide⟩
    (prefixPartial 10 71387) = some ⟨10, 2, 0, 1505300, 71387, 1385, 1048576⟩ := by
  decide +kernel

theorem context_10_71387_1505300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71387 ⟨1505300, by decide⟩ :=
  accepted_of_selected 10 71387 ⟨1505300, by decide⟩ ⟨10, 2, 0, 1505300, 71387, 1385, 1048576⟩
    (by decide) selected_cut_51983

theorem unmarked_context_9_17846_1505301 : frontier 12 ⟨1505301, by decide⟩
    (prefixCache 9 17846) (prefixPartial 9 17846) = false := by
  decide +kernel

theorem node_context_9_17846_1505301 : EJMOriginalGlobalDAGData.nodes 12 ⟨1505301, by decide⟩ =
    .split (coordinate 9) (![⟨1505226, by decide⟩,⟨1505269, by decide⟩,⟨1469103, by decide⟩,⟨1505300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17846_1505301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17846 ⟨1505301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17846
    ⟨1505301, by decide⟩ (by decide) (![⟨1505226, by decide⟩,⟨1505269, by decide⟩,⟨1469103, by decide⟩,⟨1505300, by decide⟩]) unmarked_context_9_17846_1505301 node_context_9_17846_1505301
  intro a
  fin_cases a
  · exact context_10_71384_1505226
  · exact context_10_71385_1505269
  · exact context_10_71386_1469103
  · exact context_10_71387_1505300

theorem selected_cut_51984 : selected 12 ⟨1505356, by decide⟩
    (prefixPartial 9 17847) = some ⟨9, 2, 0, 1505356, 17847, 1885, 4194304⟩ := by
  decide +kernel

theorem context_9_17847_1505356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17847 ⟨1505356, by decide⟩ :=
  accepted_of_selected 9 17847 ⟨1505356, by decide⟩ ⟨9, 2, 0, 1505356, 17847, 1885, 4194304⟩
    (by decide) selected_cut_51984

theorem unmarked_context_8_4461_1505357 : frontier 13 ⟨1505357, by decide⟩
    (prefixCache 8 4461) (prefixPartial 8 4461) = false := by
  decide +kernel

theorem node_context_8_4461_1505357 : EJMOriginalGlobalDAGData.nodes 13 ⟨1505357, by decide⟩ =
    .split (coordinate 8) (![⟨1504939, by decide⟩,⟨1505172, by decide⟩,⟨1505301, by decide⟩,⟨1505356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4461_1505357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4461 ⟨1505357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4461
    ⟨1505357, by decide⟩ (by decide) (![⟨1504939, by decide⟩,⟨1505172, by decide⟩,⟨1505301, by decide⟩,⟨1505356, by decide⟩]) unmarked_context_8_4461_1505357 node_context_8_4461_1505357
  intro a
  fin_cases a
  · exact context_9_17844_1504939
  · exact context_9_17845_1505172
  · exact context_9_17846_1505301
  · exact context_9_17847_1505356

theorem selected_cut_51985 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71392) = some ⟨10, 1, 0, 1468246, 71392, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71392_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71392 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71392 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71392, 1, 1048576⟩
    (by decide) selected_cut_51985

theorem selected_cut_51986 : selected 10 ⟨1505455, by decide⟩
    (prefixPartial 11 285572) = some ⟨11, 2, 0, 1505455, 285572, 3277, 262144⟩ := by
  decide +kernel

theorem context_11_285572_1505455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285572 ⟨1505455, by decide⟩ :=
  accepted_of_selected 11 285572 ⟨1505455, by decide⟩ ⟨11, 2, 0, 1505455, 285572, 3277, 262144⟩
    (by decide) selected_cut_51986

theorem selected_cut_51987 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285573) = some ⟨11, 1, 0, 1468419, 285573, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285573_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285573 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285573 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285573, 1, 262144⟩
    (by decide) selected_cut_51987

theorem selected_cut_51988 : selected 10 ⟨1505546, by decide⟩
    (prefixPartial 11 285574) = some ⟨11, 2, 0, 1505546, 285574, 3113, 262144⟩ := by
  decide +kernel

theorem context_11_285574_1505546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285574 ⟨1505546, by decide⟩ :=
  accepted_of_selected 11 285574 ⟨1505546, by decide⟩ ⟨11, 2, 0, 1505546, 285574, 3113, 262144⟩
    (by decide) selected_cut_51988

theorem selected_cut_51989 : selected 10 ⟨1505577, by decide⟩
    (prefixPartial 11 285575) = some ⟨11, 2, 0, 1505577, 285575, 1277, 262144⟩ := by
  decide +kernel

theorem context_11_285575_1505577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285575 ⟨1505577, by decide⟩ :=
  accepted_of_selected 11 285575 ⟨1505577, by decide⟩ ⟨11, 2, 0, 1505577, 285575, 1277, 262144⟩
    (by decide) selected_cut_51989

theorem unmarked_context_10_71393_1505578 : frontier 11 ⟨1505578, by decide⟩
    (prefixCache 10 71393) (prefixPartial 10 71393) = false := by
  decide +kernel

theorem node_context_10_71393_1505578 : EJMOriginalGlobalDAGData.nodes 11 ⟨1505578, by decide⟩ =
    .split (coordinate 10) (![⟨1505455, by decide⟩,⟨1468419, by decide⟩,⟨1505546, by decide⟩,⟨1505577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71393_1505578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71393 ⟨1505578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71393
    ⟨1505578, by decide⟩ (by decide) (![⟨1505455, by decide⟩,⟨1468419, by decide⟩,⟨1505546, by decide⟩,⟨1505577, by decide⟩]) unmarked_context_10_71393_1505578 node_context_10_71393_1505578
  intro a
  fin_cases a
  · exact context_11_285572_1505455
  · exact context_11_285573_1468419
  · exact context_11_285574_1505546
  · exact context_11_285575_1505577

theorem selected_cut_51990 : selected 10 ⟨1505668, by decide⟩
    (prefixPartial 11 285576) = some ⟨11, 2, 0, 1505668, 285576, 4037, 262144⟩ := by
  decide +kernel

theorem context_11_285576_1505668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285576 ⟨1505668, by decide⟩ :=
  accepted_of_selected 11 285576 ⟨1505668, by decide⟩ ⟨11, 2, 0, 1505668, 285576, 4037, 262144⟩
    (by decide) selected_cut_51990

theorem selected_cut_51991 : selected 10 ⟨1505723, by decide⟩
    (prefixPartial 11 285577) = some ⟨11, 2, 0, 1505723, 285577, 2321, 262144⟩ := by
  decide +kernel

theorem context_11_285577_1505723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285577 ⟨1505723, by decide⟩ :=
  accepted_of_selected 11 285577 ⟨1505723, by decide⟩ ⟨11, 2, 0, 1505723, 285577, 2321, 262144⟩
    (by decide) selected_cut_51991

theorem selected_cut_51992 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285578) = some ⟨11, 1, 0, 1468743, 285578, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285578_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285578 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285578 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285578, 1, 262144⟩
    (by decide) selected_cut_51992

theorem selected_cut_51993 : selected 10 ⟨1505750, by decide⟩
    (prefixPartial 11 285579) = some ⟨11, 2, 0, 1505750, 285579, 1029, 262144⟩ := by
  decide +kernel

theorem context_11_285579_1505750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285579 ⟨1505750, by decide⟩ :=
  accepted_of_selected 11 285579 ⟨1505750, by decide⟩ ⟨11, 2, 0, 1505750, 285579, 1029, 262144⟩
    (by decide) selected_cut_51993

theorem unmarked_context_10_71394_1505751 : frontier 11 ⟨1505751, by decide⟩
    (prefixCache 10 71394) (prefixPartial 10 71394) = false := by
  decide +kernel

theorem node_context_10_71394_1505751 : EJMOriginalGlobalDAGData.nodes 11 ⟨1505751, by decide⟩ =
    .split (coordinate 10) (![⟨1505668, by decide⟩,⟨1505723, by decide⟩,⟨1468743, by decide⟩,⟨1505750, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71394_1505751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71394 ⟨1505751, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71394
    ⟨1505751, by decide⟩ (by decide) (![⟨1505668, by decide⟩,⟨1505723, by decide⟩,⟨1468743, by decide⟩,⟨1505750, by decide⟩]) unmarked_context_10_71394_1505751 node_context_10_71394_1505751
  intro a
  fin_cases a
  · exact context_11_285576_1505668
  · exact context_11_285577_1505723
  · exact context_11_285578_1468743
  · exact context_11_285579_1505750

theorem selected_cut_51994 : selected 10 ⟨1505799, by decide⟩
    (prefixPartial 11 285580) = some ⟨11, 2, 0, 1505799, 285580, 849, 262144⟩ := by
  decide +kernel

theorem context_11_285580_1505799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285580 ⟨1505799, by decide⟩ :=
  accepted_of_selected 11 285580 ⟨1505799, by decide⟩ ⟨11, 2, 0, 1505799, 285580, 849, 262144⟩
    (by decide) selected_cut_51994

theorem selected_cut_51995 : selected 10 ⟨1505844, by decide⟩
    (prefixPartial 11 285581) = some ⟨11, 2, 0, 1505844, 285581, 2053, 262144⟩ := by
  decide +kernel

theorem context_11_285581_1505844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285581 ⟨1505844, by decide⟩ :=
  accepted_of_selected 11 285581 ⟨1505844, by decide⟩ ⟨11, 2, 0, 1505844, 285581, 2053, 262144⟩
    (by decide) selected_cut_51995

theorem selected_cut_51996 : selected 10 ⟨1505942, by decide⟩
    (prefixPartial 11 285582) = some ⟨11, 2, 0, 1505942, 285582, 1557, 262144⟩ := by
  decide +kernel

theorem context_11_285582_1505942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285582 ⟨1505942, by decide⟩ :=
  accepted_of_selected 11 285582 ⟨1505942, by decide⟩ ⟨11, 2, 0, 1505942, 285582, 1557, 262144⟩
    (by decide) selected_cut_51996

theorem selected_cut_51997 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285583) = some ⟨11, 1, 0, 1470044, 285583, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285583_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285583 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285583 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285583, 1, 262144⟩
    (by decide) selected_cut_51997

theorem unmarked_context_10_71395_1505943 : frontier 11 ⟨1505943, by decide⟩
    (prefixCache 10 71395) (prefixPartial 10 71395) = false := by
  decide +kernel

theorem node_context_10_71395_1505943 : EJMOriginalGlobalDAGData.nodes 11 ⟨1505943, by decide⟩ =
    .split (coordinate 10) (![⟨1505799, by decide⟩,⟨1505844, by decide⟩,⟨1505942, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71395_1505943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71395 ⟨1505943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71395
    ⟨1505943, by decide⟩ (by decide) (![⟨1505799, by decide⟩,⟨1505844, by decide⟩,⟨1505942, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71395_1505943 node_context_10_71395_1505943
  intro a
  fin_cases a
  · exact context_11_285580_1505799
  · exact context_11_285581_1505844
  · exact context_11_285582_1505942
  · exact context_11_285583_1470044

theorem unmarked_context_9_17848_1505944 : frontier 12 ⟨1505944, by decide⟩
    (prefixCache 9 17848) (prefixPartial 9 17848) = false := by
  decide +kernel

theorem node_context_9_17848_1505944 : EJMOriginalGlobalDAGData.nodes 12 ⟨1505944, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1505578, by decide⟩,⟨1505751, by decide⟩,⟨1505943, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17848_1505944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17848 ⟨1505944, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17848
    ⟨1505944, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1505578, by decide⟩,⟨1505751, by decide⟩,⟨1505943, by decide⟩]) unmarked_context_9_17848_1505944 node_context_9_17848_1505944
  intro a
  fin_cases a
  · exact context_10_71392_1468246
  · exact context_10_71393_1505578
  · exact context_10_71394_1505751
  · exact context_10_71395_1505943

theorem selected_cut_51998 : selected 11 ⟨1506029, by decide⟩
    (prefixPartial 10 71396) = some ⟨10, 2, 0, 1506029, 71396, 2805, 1048576⟩ := by
  decide +kernel

theorem context_10_71396_1506029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71396 ⟨1506029, by decide⟩ :=
  accepted_of_selected 10 71396 ⟨1506029, by decide⟩ ⟨10, 2, 0, 1506029, 71396, 2805, 1048576⟩
    (by decide) selected_cut_51998

theorem selected_cut_51999 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71397) = some ⟨10, 1, 0, 1468874, 71397, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71397_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71397 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71397 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71397, 1, 1048576⟩
    (by decide) selected_cut_51999

theorem selected_cut_52000 : selected 11 ⟨1506124, by decide⟩
    (prefixPartial 10 71398) = some ⟨10, 2, 0, 1506124, 71398, 3797, 1048576⟩ := by
  decide +kernel

theorem context_10_71398_1506124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71398 ⟨1506124, by decide⟩ :=
  accepted_of_selected 10 71398 ⟨1506124, by decide⟩ ⟨10, 2, 0, 1506124, 71398, 3797, 1048576⟩
    (by decide) selected_cut_52000

theorem selected_cut_52001 : selected 11 ⟨1506184, by decide⟩
    (prefixPartial 10 71399) = some ⟨10, 2, 0, 1506184, 71399, 2961, 1048576⟩ := by
  decide +kernel

theorem context_10_71399_1506184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71399 ⟨1506184, by decide⟩ :=
  accepted_of_selected 10 71399 ⟨1506184, by decide⟩ ⟨10, 2, 0, 1506184, 71399, 2961, 1048576⟩
    (by decide) selected_cut_52001

theorem unmarked_context_9_17849_1506185 : frontier 12 ⟨1506185, by decide⟩
    (prefixCache 9 17849) (prefixPartial 9 17849) = false := by
  decide +kernel

theorem node_context_9_17849_1506185 : EJMOriginalGlobalDAGData.nodes 12 ⟨1506185, by decide⟩ =
    .split (coordinate 9) (![⟨1506029, by decide⟩,⟨1468874, by decide⟩,⟨1506124, by decide⟩,⟨1506184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17849_1506185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17849 ⟨1506185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17849
    ⟨1506185, by decide⟩ (by decide) (![⟨1506029, by decide⟩,⟨1468874, by decide⟩,⟨1506124, by decide⟩,⟨1506184, by decide⟩]) unmarked_context_9_17849_1506185 node_context_9_17849_1506185
  intro a
  fin_cases a
  · exact context_10_71396_1506029
  · exact context_10_71397_1468874
  · exact context_10_71398_1506124
  · exact context_10_71399_1506184

theorem selected_cut_52002 : selected 11 ⟨1506245, by decide⟩
    (prefixPartial 10 71400) = some ⟨10, 2, 0, 1506245, 71400, 2881, 1048576⟩ := by
  decide +kernel

theorem context_10_71400_1506245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71400 ⟨1506245, by decide⟩ :=
  accepted_of_selected 10 71400 ⟨1506245, by decide⟩ ⟨10, 2, 0, 1506245, 71400, 2881, 1048576⟩
    (by decide) selected_cut_52002

theorem selected_cut_52003 : selected 11 ⟨1506311, by decide⟩
    (prefixPartial 10 71401) = some ⟨10, 2, 0, 1506311, 71401, 2685, 1048576⟩ := by
  decide +kernel

theorem context_10_71401_1506311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71401 ⟨1506311, by decide⟩ :=
  accepted_of_selected 10 71401 ⟨1506311, by decide⟩ ⟨10, 2, 0, 1506311, 71401, 2685, 1048576⟩
    (by decide) selected_cut_52003

theorem selected_cut_52004 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71402) = some ⟨10, 1, 0, 1469103, 71402, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71402_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71402 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71402 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71402, 1, 1048576⟩
    (by decide) selected_cut_52004

theorem selected_cut_52005 : selected 11 ⟨1506342, by decide⟩
    (prefixPartial 10 71403) = some ⟨10, 2, 0, 1506342, 71403, 1525, 1048576⟩ := by
  decide +kernel

theorem context_10_71403_1506342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71403 ⟨1506342, by decide⟩ :=
  accepted_of_selected 10 71403 ⟨1506342, by decide⟩ ⟨10, 2, 0, 1506342, 71403, 1525, 1048576⟩
    (by decide) selected_cut_52005

theorem unmarked_context_9_17850_1506343 : frontier 12 ⟨1506343, by decide⟩
    (prefixCache 9 17850) (prefixPartial 9 17850) = false := by
  decide +kernel

theorem node_context_9_17850_1506343 : EJMOriginalGlobalDAGData.nodes 12 ⟨1506343, by decide⟩ =
    .split (coordinate 9) (![⟨1506245, by decide⟩,⟨1506311, by decide⟩,⟨1469103, by decide⟩,⟨1506342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17850_1506343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17850 ⟨1506343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17850
    ⟨1506343, by decide⟩ (by decide) (![⟨1506245, by decide⟩,⟨1506311, by decide⟩,⟨1469103, by decide⟩,⟨1506342, by decide⟩]) unmarked_context_9_17850_1506343 node_context_9_17850_1506343
  intro a
  fin_cases a
  · exact context_10_71400_1506245
  · exact context_10_71401_1506311
  · exact context_10_71402_1469103
  · exact context_10_71403_1506342

theorem selected_cut_52006 : selected 12 ⟨1506405, by decide⟩
    (prefixPartial 9 17851) = some ⟨9, 2, 0, 1506405, 17851, 1977, 4194304⟩ := by
  decide +kernel

theorem context_9_17851_1506405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17851 ⟨1506405, by decide⟩ :=
  accepted_of_selected 9 17851 ⟨1506405, by decide⟩ ⟨9, 2, 0, 1506405, 17851, 1977, 4194304⟩
    (by decide) selected_cut_52006

theorem unmarked_context_8_4462_1506406 : frontier 13 ⟨1506406, by decide⟩
    (prefixCache 8 4462) (prefixPartial 8 4462) = false := by
  decide +kernel

theorem node_context_8_4462_1506406 : EJMOriginalGlobalDAGData.nodes 13 ⟨1506406, by decide⟩ =
    .split (coordinate 8) (![⟨1505944, by decide⟩,⟨1506185, by decide⟩,⟨1506343, by decide⟩,⟨1506405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4462_1506406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4462 ⟨1506406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4462
    ⟨1506406, by decide⟩ (by decide) (![⟨1505944, by decide⟩,⟨1506185, by decide⟩,⟨1506343, by decide⟩,⟨1506405, by decide⟩]) unmarked_context_8_4462_1506406 node_context_8_4462_1506406
  intro a
  fin_cases a
  · exact context_9_17848_1505944
  · exact context_9_17849_1506185
  · exact context_9_17850_1506343
  · exact context_9_17851_1506405

theorem selected_cut_52007 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 71408) = some ⟨10, 1, 0, 1468246, 71408, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71408_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71408 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 71408 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 71408, 1, 1048576⟩
    (by decide) selected_cut_52007

theorem selected_cut_52008 : selected 10 ⟨1506511, by decide⟩
    (prefixPartial 11 285636) = some ⟨11, 2, 0, 1506511, 285636, 3329, 262144⟩ := by
  decide +kernel

theorem context_11_285636_1506511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285636 ⟨1506511, by decide⟩ :=
  accepted_of_selected 11 285636 ⟨1506511, by decide⟩ ⟨11, 2, 0, 1506511, 285636, 3329, 262144⟩
    (by decide) selected_cut_52008

theorem selected_cut_52009 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 285637) = some ⟨11, 1, 0, 1468419, 285637, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285637_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285637 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 285637 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 285637, 1, 262144⟩
    (by decide) selected_cut_52009

theorem selected_cut_52010 : selected 10 ⟨1506598, by decide⟩
    (prefixPartial 11 285638) = some ⟨11, 2, 0, 1506598, 285638, 3257, 262144⟩ := by
  decide +kernel

theorem context_11_285638_1506598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285638 ⟨1506598, by decide⟩ :=
  accepted_of_selected 11 285638 ⟨1506598, by decide⟩ ⟨11, 2, 0, 1506598, 285638, 3257, 262144⟩
    (by decide) selected_cut_52010

theorem selected_cut_52011 : selected 10 ⟨1506628, by decide⟩
    (prefixPartial 11 285639) = some ⟨11, 2, 0, 1506628, 285639, 1381, 262144⟩ := by
  decide +kernel

theorem context_11_285639_1506628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285639 ⟨1506628, by decide⟩ :=
  accepted_of_selected 11 285639 ⟨1506628, by decide⟩ ⟨11, 2, 0, 1506628, 285639, 1381, 262144⟩
    (by decide) selected_cut_52011

theorem unmarked_context_10_71409_1506629 : frontier 11 ⟨1506629, by decide⟩
    (prefixCache 10 71409) (prefixPartial 10 71409) = false := by
  decide +kernel

theorem node_context_10_71409_1506629 : EJMOriginalGlobalDAGData.nodes 11 ⟨1506629, by decide⟩ =
    .split (coordinate 10) (![⟨1506511, by decide⟩,⟨1468419, by decide⟩,⟨1506598, by decide⟩,⟨1506628, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71409_1506629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71409 ⟨1506629, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71409
    ⟨1506629, by decide⟩ (by decide) (![⟨1506511, by decide⟩,⟨1468419, by decide⟩,⟨1506598, by decide⟩,⟨1506628, by decide⟩]) unmarked_context_10_71409_1506629 node_context_10_71409_1506629
  intro a
  fin_cases a
  · exact context_11_285636_1506511
  · exact context_11_285637_1468419
  · exact context_11_285638_1506598
  · exact context_11_285639_1506628

theorem selected_cut_52012 : selected 9 ⟨1469342, by decide⟩
    (prefixPartial 12 1142560) = some ⟨12, 1, 0, 1469342, 1142560, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1142560_1469342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1142560 ⟨1469342, by decide⟩ :=
  accepted_of_selected 12 1142560 ⟨1469342, by decide⟩ ⟨12, 1, 0, 1469342, 1142560, 1, 65536⟩
    (by decide) selected_cut_52012

theorem selected_cut_52013 : selected 9 ⟨1506653, by decide⟩
    (prefixPartial 12 1142561) = some ⟨12, 2, 0, 1506653, 1142561, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_1142561_1506653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1142561 ⟨1506653, by decide⟩ :=
  accepted_of_selected 12 1142561 ⟨1506653, by decide⟩ ⟨12, 2, 0, 1506653, 1142561, 1369, 65536⟩
    (by decide) selected_cut_52013

theorem selected_cut_52014 : selected 9 ⟨1506683, by decide⟩
    (prefixPartial 12 1142562) = some ⟨12, 2, 0, 1506683, 1142562, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_1142562_1506683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1142562 ⟨1506683, by decide⟩ :=
  accepted_of_selected 12 1142562 ⟨1506683, by decide⟩ ⟨12, 2, 0, 1506683, 1142562, 1413, 65536⟩
    (by decide) selected_cut_52014

theorem selected_cut_52015 : selected 9 ⟨1506713, by decide⟩
    (prefixPartial 12 1142563) = some ⟨12, 2, 0, 1506713, 1142563, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_1142563_1506713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1142563 ⟨1506713, by decide⟩ :=
  accepted_of_selected 12 1142563 ⟨1506713, by decide⟩ ⟨12, 2, 0, 1506713, 1142563, 1337, 65536⟩
    (by decide) selected_cut_52015

theorem unmarked_context_11_285640_1506714 : frontier 10 ⟨1506714, by decide⟩
    (prefixCache 11 285640) (prefixPartial 11 285640) = false := by
  decide +kernel

theorem node_context_11_285640_1506714 : EJMOriginalGlobalDAGData.nodes 10 ⟨1506714, by decide⟩ =
    .split (coordinate 11) (![⟨1469342, by decide⟩,⟨1506653, by decide⟩,⟨1506683, by decide⟩,⟨1506713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_285640_1506714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285640 ⟨1506714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 285640
    ⟨1506714, by decide⟩ (by decide) (![⟨1469342, by decide⟩,⟨1506653, by decide⟩,⟨1506683, by decide⟩,⟨1506713, by decide⟩]) unmarked_context_11_285640_1506714 node_context_11_285640_1506714
  intro a
  fin_cases a
  · exact context_12_1142560_1469342
  · exact context_12_1142561_1506653
  · exact context_12_1142562_1506683
  · exact context_12_1142563_1506713

theorem selected_cut_52016 : selected 10 ⟨1506767, by decide⟩
    (prefixPartial 11 285641) = some ⟨11, 2, 0, 1506767, 285641, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_285641_1506767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285641 ⟨1506767, by decide⟩ :=
  accepted_of_selected 11 285641 ⟨1506767, by decide⟩ ⟨11, 2, 0, 1506767, 285641, 2545, 262144⟩
    (by decide) selected_cut_52016

theorem selected_cut_52017 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 285642) = some ⟨11, 1, 0, 1468743, 285642, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285642_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285642 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 285642 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 285642, 1, 262144⟩
    (by decide) selected_cut_52017

theorem selected_cut_52018 : selected 10 ⟨1506790, by decide⟩
    (prefixPartial 11 285643) = some ⟨11, 2, 0, 1506790, 285643, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_285643_1506790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285643 ⟨1506790, by decide⟩ :=
  accepted_of_selected 11 285643 ⟨1506790, by decide⟩ ⟨11, 2, 0, 1506790, 285643, 1093, 262144⟩
    (by decide) selected_cut_52018

theorem unmarked_context_10_71410_1506791 : frontier 11 ⟨1506791, by decide⟩
    (prefixCache 10 71410) (prefixPartial 10 71410) = false := by
  decide +kernel

theorem node_context_10_71410_1506791 : EJMOriginalGlobalDAGData.nodes 11 ⟨1506791, by decide⟩ =
    .split (coordinate 10) (![⟨1506714, by decide⟩,⟨1506767, by decide⟩,⟨1468743, by decide⟩,⟨1506790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71410_1506791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71410 ⟨1506791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71410
    ⟨1506791, by decide⟩ (by decide) (![⟨1506714, by decide⟩,⟨1506767, by decide⟩,⟨1468743, by decide⟩,⟨1506790, by decide⟩]) unmarked_context_10_71410_1506791 node_context_10_71410_1506791
  intro a
  fin_cases a
  · exact context_11_285640_1506714
  · exact context_11_285641_1506767
  · exact context_11_285642_1468743
  · exact context_11_285643_1506790

theorem selected_cut_52019 : selected 10 ⟨1503964, by decide⟩
    (prefixPartial 11 285644) = some ⟨11, 2, 0, 1503964, 285644, 5, 262144⟩ := by
  decide +kernel

theorem context_11_285644_1503964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285644 ⟨1503964, by decide⟩ :=
  accepted_of_selected 11 285644 ⟨1503964, by decide⟩ ⟨11, 2, 0, 1503964, 285644, 5, 262144⟩
    (by decide) selected_cut_52019

theorem selected_cut_52020 : selected 10 ⟨1506852, by decide⟩
    (prefixPartial 11 285645) = some ⟨11, 2, 0, 1506852, 285645, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_285645_1506852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285645 ⟨1506852, by decide⟩ :=
  accepted_of_selected 11 285645 ⟨1506852, by decide⟩ ⟨11, 2, 0, 1506852, 285645, 2433, 262144⟩
    (by decide) selected_cut_52020

theorem selected_cut_52021 : selected 10 ⟨1506905, by decide⟩
    (prefixPartial 11 285646) = some ⟨11, 2, 0, 1506905, 285646, 2205, 262144⟩ := by
  decide +kernel

theorem context_11_285646_1506905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285646 ⟨1506905, by decide⟩ :=
  accepted_of_selected 11 285646 ⟨1506905, by decide⟩ ⟨11, 2, 0, 1506905, 285646, 2205, 262144⟩
    (by decide) selected_cut_52021

theorem selected_cut_52022 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 285647) = some ⟨11, 1, 0, 1470044, 285647, 1, 262144⟩ := by
  decide +kernel

theorem context_11_285647_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 285647 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 285647 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 285647, 1, 262144⟩
    (by decide) selected_cut_52022

theorem unmarked_context_10_71411_1506906 : frontier 11 ⟨1506906, by decide⟩
    (prefixCache 10 71411) (prefixPartial 10 71411) = false := by
  decide +kernel

theorem node_context_10_71411_1506906 : EJMOriginalGlobalDAGData.nodes 11 ⟨1506906, by decide⟩ =
    .split (coordinate 10) (![⟨1503964, by decide⟩,⟨1506852, by decide⟩,⟨1506905, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_71411_1506906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71411 ⟨1506906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 71411
    ⟨1506906, by decide⟩ (by decide) (![⟨1503964, by decide⟩,⟨1506852, by decide⟩,⟨1506905, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_71411_1506906 node_context_10_71411_1506906
  intro a
  fin_cases a
  · exact context_11_285644_1503964
  · exact context_11_285645_1506852
  · exact context_11_285646_1506905
  · exact context_11_285647_1470044

theorem unmarked_context_9_17852_1506907 : frontier 12 ⟨1506907, by decide⟩
    (prefixCache 9 17852) (prefixPartial 9 17852) = false := by
  decide +kernel

theorem node_context_9_17852_1506907 : EJMOriginalGlobalDAGData.nodes 12 ⟨1506907, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1506629, by decide⟩,⟨1506791, by decide⟩,⟨1506906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17852_1506907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17852 ⟨1506907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17852
    ⟨1506907, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1506629, by decide⟩,⟨1506791, by decide⟩,⟨1506906, by decide⟩]) unmarked_context_9_17852_1506907 node_context_9_17852_1506907
  intro a
  fin_cases a
  · exact context_10_71408_1468246
  · exact context_10_71409_1506629
  · exact context_10_71410_1506791
  · exact context_10_71411_1506906

theorem selected_cut_52023 : selected 11 ⟨1506971, by decide⟩
    (prefixPartial 10 71412) = some ⟨10, 2, 0, 1506971, 71412, 2673, 1048576⟩ := by
  decide +kernel

theorem context_10_71412_1506971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71412 ⟨1506971, by decide⟩ :=
  accepted_of_selected 10 71412 ⟨1506971, by decide⟩ ⟨10, 2, 0, 1506971, 71412, 2673, 1048576⟩
    (by decide) selected_cut_52023

theorem selected_cut_52024 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 71413) = some ⟨10, 1, 0, 1468874, 71413, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71413_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71413 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 71413 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 71413, 1, 1048576⟩
    (by decide) selected_cut_52024

theorem selected_cut_52025 : selected 11 ⟨1507044, by decide⟩
    (prefixPartial 10 71414) = some ⟨10, 2, 0, 1507044, 71414, 3901, 1048576⟩ := by
  decide +kernel

theorem context_10_71414_1507044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71414 ⟨1507044, by decide⟩ :=
  accepted_of_selected 10 71414 ⟨1507044, by decide⟩ ⟨10, 2, 0, 1507044, 71414, 3901, 1048576⟩
    (by decide) selected_cut_52025

theorem selected_cut_52026 : selected 11 ⟨1507131, by decide⟩
    (prefixPartial 10 71415) = some ⟨10, 2, 0, 1507131, 71415, 3981, 1048576⟩ := by
  decide +kernel

theorem context_10_71415_1507131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71415 ⟨1507131, by decide⟩ :=
  accepted_of_selected 10 71415 ⟨1507131, by decide⟩ ⟨10, 2, 0, 1507131, 71415, 3981, 1048576⟩
    (by decide) selected_cut_52026

theorem unmarked_context_9_17853_1507132 : frontier 12 ⟨1507132, by decide⟩
    (prefixCache 9 17853) (prefixPartial 9 17853) = false := by
  decide +kernel

theorem node_context_9_17853_1507132 : EJMOriginalGlobalDAGData.nodes 12 ⟨1507132, by decide⟩ =
    .split (coordinate 9) (![⟨1506971, by decide⟩,⟨1468874, by decide⟩,⟨1507044, by decide⟩,⟨1507131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17853_1507132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17853 ⟨1507132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17853
    ⟨1507132, by decide⟩ (by decide) (![⟨1506971, by decide⟩,⟨1468874, by decide⟩,⟨1507044, by decide⟩,⟨1507131, by decide⟩]) unmarked_context_9_17853_1507132 node_context_9_17853_1507132
  intro a
  fin_cases a
  · exact context_10_71412_1506971
  · exact context_10_71413_1468874
  · exact context_10_71414_1507044
  · exact context_10_71415_1507131

theorem selected_cut_52027 : selected 11 ⟨1507197, by decide⟩
    (prefixPartial 10 71416) = some ⟨10, 2, 0, 1507197, 71416, 3237, 1048576⟩ := by
  decide +kernel

theorem context_10_71416_1507197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71416 ⟨1507197, by decide⟩ :=
  accepted_of_selected 10 71416 ⟨1507197, by decide⟩ ⟨10, 2, 0, 1507197, 71416, 3237, 1048576⟩
    (by decide) selected_cut_52027

theorem selected_cut_52028 : selected 11 ⟨1507268, by decide⟩
    (prefixPartial 10 71417) = some ⟨10, 2, 0, 1507268, 71417, 2905, 1048576⟩ := by
  decide +kernel

theorem context_10_71417_1507268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71417 ⟨1507268, by decide⟩ :=
  accepted_of_selected 10 71417 ⟨1507268, by decide⟩ ⟨10, 2, 0, 1507268, 71417, 2905, 1048576⟩
    (by decide) selected_cut_52028

theorem selected_cut_52029 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 71418) = some ⟨10, 1, 0, 1469103, 71418, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_71418_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71418 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 71418 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 71418, 1, 1048576⟩
    (by decide) selected_cut_52029

theorem selected_cut_52030 : selected 11 ⟨1507315, by decide⟩
    (prefixPartial 10 71419) = some ⟨10, 2, 0, 1507315, 71419, 2321, 1048576⟩ := by
  decide +kernel

theorem context_10_71419_1507315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 71419 ⟨1507315, by decide⟩ :=
  accepted_of_selected 10 71419 ⟨1507315, by decide⟩ ⟨10, 2, 0, 1507315, 71419, 2321, 1048576⟩
    (by decide) selected_cut_52030

theorem unmarked_context_9_17854_1507316 : frontier 12 ⟨1507316, by decide⟩
    (prefixCache 9 17854) (prefixPartial 9 17854) = false := by
  decide +kernel

theorem node_context_9_17854_1507316 : EJMOriginalGlobalDAGData.nodes 12 ⟨1507316, by decide⟩ =
    .split (coordinate 9) (![⟨1507197, by decide⟩,⟨1507268, by decide⟩,⟨1469103, by decide⟩,⟨1507315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17854_1507316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17854 ⟨1507316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17854
    ⟨1507316, by decide⟩ (by decide) (![⟨1507197, by decide⟩,⟨1507268, by decide⟩,⟨1469103, by decide⟩,⟨1507315, by decide⟩]) unmarked_context_9_17854_1507316 node_context_9_17854_1507316
  intro a
  fin_cases a
  · exact context_10_71416_1507197
  · exact context_10_71417_1507268
  · exact context_10_71418_1469103
  · exact context_10_71419_1507315

theorem selected_cut_52031 : selected 12 ⟨1507374, by decide⟩
    (prefixPartial 9 17855) = some ⟨9, 2, 0, 1507374, 17855, 1533, 4194304⟩ := by
  decide +kernel

theorem context_9_17855_1507374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17855 ⟨1507374, by decide⟩ :=
  accepted_of_selected 9 17855 ⟨1507374, by decide⟩ ⟨9, 2, 0, 1507374, 17855, 1533, 4194304⟩
    (by decide) selected_cut_52031

theorem unmarked_context_8_4463_1507375 : frontier 13 ⟨1507375, by decide⟩
    (prefixCache 8 4463) (prefixPartial 8 4463) = false := by
  decide +kernel

theorem node_context_8_4463_1507375 : EJMOriginalGlobalDAGData.nodes 13 ⟨1507375, by decide⟩ =
    .split (coordinate 8) (![⟨1506907, by decide⟩,⟨1507132, by decide⟩,⟨1507316, by decide⟩,⟨1507374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4463_1507375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4463 ⟨1507375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4463
    ⟨1507375, by decide⟩ (by decide) (![⟨1506907, by decide⟩,⟨1507132, by decide⟩,⟨1507316, by decide⟩,⟨1507374, by decide⟩]) unmarked_context_8_4463_1507375 node_context_8_4463_1507375
  intro a
  fin_cases a
  · exact context_9_17852_1506907
  · exact context_9_17853_1507132
  · exact context_9_17854_1507316
  · exact context_9_17855_1507374

theorem unmarked_context_7_1115_1507376 : frontier 14 ⟨1507376, by decide⟩
    (prefixCache 7 1115) (prefixPartial 7 1115) = false := by
  decide +kernel

theorem node_context_7_1115_1507376 : EJMOriginalGlobalDAGData.nodes 14 ⟨1507376, by decide⟩ =
    .split (coordinate 7) (![⟨1504563, by decide⟩,⟨1505357, by decide⟩,⟨1506406, by decide⟩,⟨1507375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1115_1507376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1115 ⟨1507376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1115
    ⟨1507376, by decide⟩ (by decide) (![⟨1504563, by decide⟩,⟨1505357, by decide⟩,⟨1506406, by decide⟩,⟨1507375, by decide⟩]) unmarked_context_7_1115_1507376 node_context_7_1115_1507376
  intro a
  fin_cases a
  · exact context_8_4460_1504563
  · exact context_8_4461_1505357
  · exact context_8_4462_1506406
  · exact context_8_4463_1507375

theorem unmarked_context_6_278_1507377 : frontier 15 ⟨1507377, by decide⟩
    (prefixCache 6 278) (prefixPartial 6 278) = false := by
  decide +kernel

theorem node_context_6_278_1507377 : EJMOriginalGlobalDAGData.nodes 15 ⟨1507377, by decide⟩ =
    .split (coordinate 6) (![⟨1497120, by decide⟩,⟨1500844, by decide⟩,⟨1503610, by decide⟩,⟨1507376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_278_1507377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 278 ⟨1507377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 278
    ⟨1507377, by decide⟩ (by decide) (![⟨1497120, by decide⟩,⟨1500844, by decide⟩,⟨1503610, by decide⟩,⟨1507376, by decide⟩]) unmarked_context_6_278_1507377 node_context_6_278_1507377
  intro a
  fin_cases a
  · exact context_7_1112_1497120
  · exact context_7_1113_1500844
  · exact context_7_1114_1503610
  · exact context_7_1115_1507376

theorem selected_cut_52032 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 279) = some ⟨6, 1, 0, 116314, 279, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_279_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 279 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 279 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 279, 1, 268435456⟩
    (by decide) selected_cut_52032

theorem unmarked_context_5_69_1507378 : frontier 16 ⟨1507378, by decide⟩
    (prefixCache 5 69) (prefixPartial 5 69) = false := by
  decide +kernel

theorem node_context_5_69_1507378 : EJMOriginalGlobalDAGData.nodes 16 ⟨1507378, by decide⟩ =
    .split (coordinate 5) (![⟨1492908, by decide⟩,⟨1475984, by decide⟩,⟨1507377, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_69_1507378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 69 ⟨1507378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 69
    ⟨1507378, by decide⟩ (by decide) (![⟨1492908, by decide⟩,⟨1475984, by decide⟩,⟨1507377, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_69_1507378 node_context_5_69_1507378
  intro a
  fin_cases a
  · exact context_6_276_1492908
  · exact context_6_277_1475984
  · exact context_6_278_1507377
  · exact context_6_279_116314

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
