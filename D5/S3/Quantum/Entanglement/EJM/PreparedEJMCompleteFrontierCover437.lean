/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover436
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_41954 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 336992) = some ⟨12, 1, 0, 985390, 336992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336992_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336992 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 336992 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 336992, 1, 65536⟩
    (by decide) selected_cut_41954

theorem selected_cut_41955 : selected 9 ⟨1147016, by decide⟩
    (prefixPartial 12 336993) = some ⟨12, 2, 0, 1147016, 336993, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_336993_1147016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336993 ⟨1147016, by decide⟩ :=
  accepted_of_selected 12 336993 ⟨1147016, by decide⟩ ⟨12, 2, 0, 1147016, 336993, 1477, 65536⟩
    (by decide) selected_cut_41955

theorem selected_cut_41956 : selected 9 ⟨1147055, by decide⟩
    (prefixPartial 12 336994) = some ⟨12, 2, 0, 1147055, 336994, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_336994_1147055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336994 ⟨1147055, by decide⟩ :=
  accepted_of_selected 12 336994 ⟨1147055, by decide⟩ ⟨12, 2, 0, 1147055, 336994, 1997, 65536⟩
    (by decide) selected_cut_41956

theorem selected_cut_41957 : selected 9 ⟨1147082, by decide⟩
    (prefixPartial 12 336995) = some ⟨12, 2, 0, 1147082, 336995, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_336995_1147082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336995 ⟨1147082, by decide⟩ :=
  accepted_of_selected 12 336995 ⟨1147082, by decide⟩ ⟨12, 2, 0, 1147082, 336995, 1829, 65536⟩
    (by decide) selected_cut_41957

theorem unmarked_context_11_84248_1147083 : frontier 10 ⟨1147083, by decide⟩
    (prefixCache 11 84248) (prefixPartial 11 84248) = false := by
  decide +kernel

theorem node_context_11_84248_1147083 : EJMOriginalGlobalDAGData.nodes 10 ⟨1147083, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1147016, by decide⟩,⟨1147055, by decide⟩,⟨1147082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84248_1147083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84248 ⟨1147083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84248
    ⟨1147083, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1147016, by decide⟩,⟨1147055, by decide⟩,⟨1147082, by decide⟩]) unmarked_context_11_84248_1147083 node_context_11_84248_1147083
  intro a
  fin_cases a
  · exact context_12_336992_985390
  · exact context_12_336993_1147016
  · exact context_12_336994_1147055
  · exact context_12_336995_1147082

theorem selected_cut_41958 : selected 9 ⟨1147112, by decide⟩
    (prefixPartial 12 336996) = some ⟨12, 2, 0, 1147112, 336996, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_336996_1147112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336996 ⟨1147112, by decide⟩ :=
  accepted_of_selected 12 336996 ⟨1147112, by decide⟩ ⟨12, 2, 0, 1147112, 336996, 1537, 65536⟩
    (by decide) selected_cut_41958

theorem selected_cut_41959 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 336997) = some ⟨12, 1, 0, 642794, 336997, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336997_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336997 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 336997 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 336997, 1, 65536⟩
    (by decide) selected_cut_41959

theorem selected_cut_41960 : selected 9 ⟨1147147, by decide⟩
    (prefixPartial 12 336998) = some ⟨12, 2, 0, 1147147, 336998, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_336998_1147147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336998 ⟨1147147, by decide⟩ :=
  accepted_of_selected 12 336998 ⟨1147147, by decide⟩ ⟨12, 2, 0, 1147147, 336998, 1765, 65536⟩
    (by decide) selected_cut_41960

theorem selected_cut_41961 : selected 9 ⟨1147177, by decide⟩
    (prefixPartial 12 336999) = some ⟨12, 2, 0, 1147177, 336999, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_336999_1147177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336999 ⟨1147177, by decide⟩ :=
  accepted_of_selected 12 336999 ⟨1147177, by decide⟩ ⟨12, 2, 0, 1147177, 336999, 1621, 65536⟩
    (by decide) selected_cut_41961

theorem unmarked_context_11_84249_1147178 : frontier 10 ⟨1147178, by decide⟩
    (prefixCache 11 84249) (prefixPartial 11 84249) = false := by
  decide +kernel

theorem node_context_11_84249_1147178 : EJMOriginalGlobalDAGData.nodes 10 ⟨1147178, by decide⟩ =
    .split (coordinate 11) (![⟨1147112, by decide⟩,⟨642794, by decide⟩,⟨1147147, by decide⟩,⟨1147177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84249_1147178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84249 ⟨1147178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84249
    ⟨1147178, by decide⟩ (by decide) (![⟨1147112, by decide⟩,⟨642794, by decide⟩,⟨1147147, by decide⟩,⟨1147177, by decide⟩]) unmarked_context_11_84249_1147178 node_context_11_84249_1147178
  intro a
  fin_cases a
  · exact context_12_336996_1147112
  · exact context_12_336997_642794
  · exact context_12_336998_1147147
  · exact context_12_336999_1147177

theorem selected_cut_41962 : selected 9 ⟨1147201, by decide⟩
    (prefixPartial 12 337000) = some ⟨12, 2, 0, 1147201, 337000, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_337000_1147201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337000 ⟨1147201, by decide⟩ :=
  accepted_of_selected 12 337000 ⟨1147201, by decide⟩ ⟨12, 2, 0, 1147201, 337000, 1537, 65536⟩
    (by decide) selected_cut_41962

theorem selected_cut_41963 : selected 9 ⟨1147220, by decide⟩
    (prefixPartial 12 337001) = some ⟨12, 2, 0, 1147220, 337001, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_337001_1147220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337001 ⟨1147220, by decide⟩ :=
  accepted_of_selected 12 337001 ⟨1147220, by decide⟩ ⟨12, 2, 0, 1147220, 337001, 1417, 65536⟩
    (by decide) selected_cut_41963

theorem selected_cut_41964 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 337002) = some ⟨12, 1, 0, 1113261, 337002, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337002_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337002 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 337002 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 337002, 1, 65536⟩
    (by decide) selected_cut_41964

theorem selected_cut_41965 : selected 9 ⟨1147256, by decide⟩
    (prefixPartial 12 337003) = some ⟨12, 2, 0, 1147256, 337003, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_337003_1147256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337003 ⟨1147256, by decide⟩ :=
  accepted_of_selected 12 337003 ⟨1147256, by decide⟩ ⟨12, 2, 0, 1147256, 337003, 1881, 65536⟩
    (by decide) selected_cut_41965

theorem unmarked_context_11_84250_1147257 : frontier 10 ⟨1147257, by decide⟩
    (prefixCache 11 84250) (prefixPartial 11 84250) = false := by
  decide +kernel

theorem node_context_11_84250_1147257 : EJMOriginalGlobalDAGData.nodes 10 ⟨1147257, by decide⟩ =
    .split (coordinate 11) (![⟨1147201, by decide⟩,⟨1147220, by decide⟩,⟨1113261, by decide⟩,⟨1147256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84250_1147257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84250 ⟨1147257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84250
    ⟨1147257, by decide⟩ (by decide) (![⟨1147201, by decide⟩,⟨1147220, by decide⟩,⟨1113261, by decide⟩,⟨1147256, by decide⟩]) unmarked_context_11_84250_1147257 node_context_11_84250_1147257
  intro a
  fin_cases a
  · exact context_12_337000_1147201
  · exact context_12_337001_1147220
  · exact context_12_337002_1113261
  · exact context_12_337003_1147256

theorem selected_cut_41966 : selected 9 ⟨1147282, by decide⟩
    (prefixPartial 12 337004) = some ⟨12, 2, 0, 1147282, 337004, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_337004_1147282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337004 ⟨1147282, by decide⟩ :=
  accepted_of_selected 12 337004 ⟨1147282, by decide⟩ ⟨12, 2, 0, 1147282, 337004, 1573, 65536⟩
    (by decide) selected_cut_41966

theorem selected_cut_41967 : selected 9 ⟨1147301, by decide⟩
    (prefixPartial 12 337005) = some ⟨12, 2, 0, 1147301, 337005, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_337005_1147301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337005 ⟨1147301, by decide⟩ :=
  accepted_of_selected 12 337005 ⟨1147301, by decide⟩ ⟨12, 2, 0, 1147301, 337005, 1473, 65536⟩
    (by decide) selected_cut_41967

theorem selected_cut_41968 : selected 9 ⟨1147346, by decide⟩
    (prefixPartial 12 337006) = some ⟨12, 2, 0, 1147346, 337006, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_337006_1147346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337006 ⟨1147346, by decide⟩ :=
  accepted_of_selected 12 337006 ⟨1147346, by decide⟩ ⟨12, 2, 0, 1147346, 337006, 1985, 65536⟩
    (by decide) selected_cut_41968

theorem selected_cut_41969 : selected 9 ⟨1147377, by decide⟩
    (prefixPartial 12 337007) = some ⟨12, 2, 0, 1147377, 337007, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_337007_1147377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337007 ⟨1147377, by decide⟩ :=
  accepted_of_selected 12 337007 ⟨1147377, by decide⟩ ⟨12, 2, 0, 1147377, 337007, 1837, 65536⟩
    (by decide) selected_cut_41969

theorem unmarked_context_11_84251_1147378 : frontier 10 ⟨1147378, by decide⟩
    (prefixCache 11 84251) (prefixPartial 11 84251) = false := by
  decide +kernel

theorem node_context_11_84251_1147378 : EJMOriginalGlobalDAGData.nodes 10 ⟨1147378, by decide⟩ =
    .split (coordinate 11) (![⟨1147282, by decide⟩,⟨1147301, by decide⟩,⟨1147346, by decide⟩,⟨1147377, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84251_1147378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84251 ⟨1147378, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84251
    ⟨1147378, by decide⟩ (by decide) (![⟨1147282, by decide⟩,⟨1147301, by decide⟩,⟨1147346, by decide⟩,⟨1147377, by decide⟩]) unmarked_context_11_84251_1147378 node_context_11_84251_1147378
  intro a
  fin_cases a
  · exact context_12_337004_1147282
  · exact context_12_337005_1147301
  · exact context_12_337006_1147346
  · exact context_12_337007_1147377

theorem unmarked_context_10_21062_1147379 : frontier 11 ⟨1147379, by decide⟩
    (prefixCache 10 21062) (prefixPartial 10 21062) = false := by
  decide +kernel

theorem node_context_10_21062_1147379 : EJMOriginalGlobalDAGData.nodes 11 ⟨1147379, by decide⟩ =
    .split (coordinate 10) (![⟨1147083, by decide⟩,⟨1147178, by decide⟩,⟨1147257, by decide⟩,⟨1147378, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21062_1147379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21062 ⟨1147379, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21062
    ⟨1147379, by decide⟩ (by decide) (![⟨1147083, by decide⟩,⟨1147178, by decide⟩,⟨1147257, by decide⟩,⟨1147378, by decide⟩]) unmarked_context_10_21062_1147379 node_context_10_21062_1147379
  intro a
  fin_cases a
  · exact context_11_84248_1147083
  · exact context_11_84249_1147178
  · exact context_11_84250_1147257
  · exact context_11_84251_1147378

theorem selected_cut_41970 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 337008) = some ⟨12, 1, 0, 985390, 337008, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337008_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337008 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 337008 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 337008, 1, 65536⟩
    (by decide) selected_cut_41970

theorem selected_cut_41971 : selected 9 ⟨1147401, by decide⟩
    (prefixPartial 12 337009) = some ⟨12, 2, 0, 1147401, 337009, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_337009_1147401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337009 ⟨1147401, by decide⟩ :=
  accepted_of_selected 12 337009 ⟨1147401, by decide⟩ ⟨12, 2, 0, 1147401, 337009, 1461, 65536⟩
    (by decide) selected_cut_41971

theorem selected_cut_41972 : selected 9 ⟨1147434, by decide⟩
    (prefixPartial 12 337010) = some ⟨12, 2, 0, 1147434, 337010, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_337010_1147434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337010 ⟨1147434, by decide⟩ :=
  accepted_of_selected 12 337010 ⟨1147434, by decide⟩ ⟨12, 2, 0, 1147434, 337010, 1877, 65536⟩
    (by decide) selected_cut_41972

theorem selected_cut_41973 : selected 9 ⟨1147468, by decide⟩
    (prefixPartial 12 337011) = some ⟨12, 2, 0, 1147468, 337011, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_337011_1147468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337011 ⟨1147468, by decide⟩ :=
  accepted_of_selected 12 337011 ⟨1147468, by decide⟩ ⟨12, 2, 0, 1147468, 337011, 1873, 65536⟩
    (by decide) selected_cut_41973

theorem unmarked_context_11_84252_1147469 : frontier 10 ⟨1147469, by decide⟩
    (prefixCache 11 84252) (prefixPartial 11 84252) = false := by
  decide +kernel

theorem node_context_11_84252_1147469 : EJMOriginalGlobalDAGData.nodes 10 ⟨1147469, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1147401, by decide⟩,⟨1147434, by decide⟩,⟨1147468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84252_1147469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84252 ⟨1147469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84252
    ⟨1147469, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1147401, by decide⟩,⟨1147434, by decide⟩,⟨1147468, by decide⟩]) unmarked_context_11_84252_1147469 node_context_11_84252_1147469
  intro a
  fin_cases a
  · exact context_12_337008_985390
  · exact context_12_337009_1147401
  · exact context_12_337010_1147434
  · exact context_12_337011_1147468

theorem selected_cut_41974 : selected 9 ⟨1147498, by decide⟩
    (prefixPartial 12 337012) = some ⟨12, 2, 0, 1147498, 337012, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_337012_1147498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337012 ⟨1147498, by decide⟩ :=
  accepted_of_selected 12 337012 ⟨1147498, by decide⟩ ⟨12, 2, 0, 1147498, 337012, 1373, 65536⟩
    (by decide) selected_cut_41974

theorem selected_cut_41975 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 337013) = some ⟨12, 1, 0, 642794, 337013, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337013_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337013 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 337013 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 337013, 1, 65536⟩
    (by decide) selected_cut_41975

theorem selected_cut_41976 : selected 9 ⟨1147528, by decide⟩
    (prefixPartial 12 337014) = some ⟨12, 2, 0, 1147528, 337014, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_337014_1147528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337014 ⟨1147528, by decide⟩ :=
  accepted_of_selected 12 337014 ⟨1147528, by decide⟩ ⟨12, 2, 0, 1147528, 337014, 1525, 65536⟩
    (by decide) selected_cut_41976

theorem selected_cut_41977 : selected 9 ⟨1147560, by decide⟩
    (prefixPartial 12 337015) = some ⟨12, 2, 0, 1147560, 337015, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_337015_1147560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337015 ⟨1147560, by decide⟩ :=
  accepted_of_selected 12 337015 ⟨1147560, by decide⟩ ⟨12, 2, 0, 1147560, 337015, 1641, 65536⟩
    (by decide) selected_cut_41977

theorem unmarked_context_11_84253_1147561 : frontier 10 ⟨1147561, by decide⟩
    (prefixCache 11 84253) (prefixPartial 11 84253) = false := by
  decide +kernel

theorem node_context_11_84253_1147561 : EJMOriginalGlobalDAGData.nodes 10 ⟨1147561, by decide⟩ =
    .split (coordinate 11) (![⟨1147498, by decide⟩,⟨642794, by decide⟩,⟨1147528, by decide⟩,⟨1147560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84253_1147561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84253 ⟨1147561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84253
    ⟨1147561, by decide⟩ (by decide) (![⟨1147498, by decide⟩,⟨642794, by decide⟩,⟨1147528, by decide⟩,⟨1147560, by decide⟩]) unmarked_context_11_84253_1147561 node_context_11_84253_1147561
  intro a
  fin_cases a
  · exact context_12_337012_1147498
  · exact context_12_337013_642794
  · exact context_12_337014_1147528
  · exact context_12_337015_1147560

theorem selected_cut_41978 : selected 9 ⟨1147592, by decide⟩
    (prefixPartial 12 337016) = some ⟨12, 2, 0, 1147592, 337016, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_337016_1147592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337016 ⟨1147592, by decide⟩ :=
  accepted_of_selected 12 337016 ⟨1147592, by decide⟩ ⟨12, 2, 0, 1147592, 337016, 1493, 65536⟩
    (by decide) selected_cut_41978

theorem selected_cut_41979 : selected 9 ⟨1147612, by decide⟩
    (prefixPartial 12 337017) = some ⟨12, 2, 0, 1147612, 337017, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_337017_1147612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337017 ⟨1147612, by decide⟩ :=
  accepted_of_selected 12 337017 ⟨1147612, by decide⟩ ⟨12, 2, 0, 1147612, 337017, 1389, 65536⟩
    (by decide) selected_cut_41979

theorem selected_cut_41980 : selected 9 ⟨1147643, by decide⟩
    (prefixPartial 12 337018) = some ⟨12, 2, 0, 1147643, 337018, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_337018_1147643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337018 ⟨1147643, by decide⟩ :=
  accepted_of_selected 12 337018 ⟨1147643, by decide⟩ ⟨12, 2, 0, 1147643, 337018, 1693, 65536⟩
    (by decide) selected_cut_41980

theorem selected_cut_41981 : selected 9 ⟨1147676, by decide⟩
    (prefixPartial 12 337019) = some ⟨12, 2, 0, 1147676, 337019, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_337019_1147676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337019 ⟨1147676, by decide⟩ :=
  accepted_of_selected 12 337019 ⟨1147676, by decide⟩ ⟨12, 2, 0, 1147676, 337019, 1869, 65536⟩
    (by decide) selected_cut_41981

theorem unmarked_context_11_84254_1147677 : frontier 10 ⟨1147677, by decide⟩
    (prefixCache 11 84254) (prefixPartial 11 84254) = false := by
  decide +kernel

theorem node_context_11_84254_1147677 : EJMOriginalGlobalDAGData.nodes 10 ⟨1147677, by decide⟩ =
    .split (coordinate 11) (![⟨1147592, by decide⟩,⟨1147612, by decide⟩,⟨1147643, by decide⟩,⟨1147676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84254_1147677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84254 ⟨1147677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84254
    ⟨1147677, by decide⟩ (by decide) (![⟨1147592, by decide⟩,⟨1147612, by decide⟩,⟨1147643, by decide⟩,⟨1147676, by decide⟩]) unmarked_context_11_84254_1147677 node_context_11_84254_1147677
  intro a
  fin_cases a
  · exact context_12_337016_1147592
  · exact context_12_337017_1147612
  · exact context_12_337018_1147643
  · exact context_12_337019_1147676

theorem selected_cut_41982 : selected 9 ⟨1147698, by decide⟩
    (prefixPartial 12 337020) = some ⟨12, 2, 0, 1147698, 337020, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_337020_1147698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337020 ⟨1147698, by decide⟩ :=
  accepted_of_selected 12 337020 ⟨1147698, by decide⟩ ⟨12, 2, 0, 1147698, 337020, 1333, 65536⟩
    (by decide) selected_cut_41982

theorem selected_cut_41983 : selected 9 ⟨1147717, by decide⟩
    (prefixPartial 12 337021) = some ⟨12, 2, 0, 1147717, 337021, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_337021_1147717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337021 ⟨1147717, by decide⟩ :=
  accepted_of_selected 12 337021 ⟨1147717, by decide⟩ ⟨12, 2, 0, 1147717, 337021, 1257, 65536⟩
    (by decide) selected_cut_41983

theorem selected_cut_41984 : selected 9 ⟨1147755, by decide⟩
    (prefixPartial 12 337022) = some ⟨12, 2, 0, 1147755, 337022, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_337022_1147755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337022 ⟨1147755, by decide⟩ :=
  accepted_of_selected 12 337022 ⟨1147755, by decide⟩ ⟨12, 2, 0, 1147755, 337022, 1637, 65536⟩
    (by decide) selected_cut_41984

theorem selected_cut_41985 : selected 9 ⟨1116246, by decide⟩
    (prefixPartial 12 337023) = some ⟨12, 1, 0, 1116246, 337023, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337023_1116246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337023 ⟨1116246, by decide⟩ :=
  accepted_of_selected 12 337023 ⟨1116246, by decide⟩ ⟨12, 1, 0, 1116246, 337023, 1, 65536⟩
    (by decide) selected_cut_41985

theorem unmarked_context_11_84255_1147756 : frontier 10 ⟨1147756, by decide⟩
    (prefixCache 11 84255) (prefixPartial 11 84255) = false := by
  decide +kernel

theorem node_context_11_84255_1147756 : EJMOriginalGlobalDAGData.nodes 10 ⟨1147756, by decide⟩ =
    .split (coordinate 11) (![⟨1147698, by decide⟩,⟨1147717, by decide⟩,⟨1147755, by decide⟩,⟨1116246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84255_1147756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84255 ⟨1147756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84255
    ⟨1147756, by decide⟩ (by decide) (![⟨1147698, by decide⟩,⟨1147717, by decide⟩,⟨1147755, by decide⟩,⟨1116246, by decide⟩]) unmarked_context_11_84255_1147756 node_context_11_84255_1147756
  intro a
  fin_cases a
  · exact context_12_337020_1147698
  · exact context_12_337021_1147717
  · exact context_12_337022_1147755
  · exact context_12_337023_1116246

theorem unmarked_context_10_21063_1147757 : frontier 11 ⟨1147757, by decide⟩
    (prefixCache 10 21063) (prefixPartial 10 21063) = false := by
  decide +kernel

theorem node_context_10_21063_1147757 : EJMOriginalGlobalDAGData.nodes 11 ⟨1147757, by decide⟩ =
    .split (coordinate 10) (![⟨1147469, by decide⟩,⟨1147561, by decide⟩,⟨1147677, by decide⟩,⟨1147756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21063_1147757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21063 ⟨1147757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21063
    ⟨1147757, by decide⟩ (by decide) (![⟨1147469, by decide⟩,⟨1147561, by decide⟩,⟨1147677, by decide⟩,⟨1147756, by decide⟩]) unmarked_context_10_21063_1147757 node_context_10_21063_1147757
  intro a
  fin_cases a
  · exact context_11_84252_1147469
  · exact context_11_84253_1147561
  · exact context_11_84254_1147677
  · exact context_11_84255_1147756

theorem unmarked_context_9_5265_1147758 : frontier 12 ⟨1147758, by decide⟩
    (prefixCache 9 5265) (prefixPartial 9 5265) = false := by
  decide +kernel

theorem node_context_9_5265_1147758 : EJMOriginalGlobalDAGData.nodes 12 ⟨1147758, by decide⟩ =
    .split (coordinate 9) (![⟨1146992, by decide⟩,⟨893098, by decide⟩,⟨1147379, by decide⟩,⟨1147757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5265_1147758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5265 ⟨1147758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5265
    ⟨1147758, by decide⟩ (by decide) (![⟨1146992, by decide⟩,⟨893098, by decide⟩,⟨1147379, by decide⟩,⟨1147757, by decide⟩]) unmarked_context_9_5265_1147758 node_context_9_5265_1147758
  intro a
  fin_cases a
  · exact context_10_21060_1146992
  · exact context_10_21061_893098
  · exact context_10_21062_1147379
  · exact context_10_21063_1147757

theorem selected_cut_41986 : selected 10 ⟨1147821, by decide⟩
    (prefixPartial 11 84256) = some ⟨11, 2, 0, 1147821, 84256, 2929, 262144⟩ := by
  decide +kernel

theorem context_11_84256_1147821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84256 ⟨1147821, by decide⟩ :=
  accepted_of_selected 11 84256 ⟨1147821, by decide⟩ ⟨11, 2, 0, 1147821, 84256, 2929, 262144⟩
    (by decide) selected_cut_41986

theorem selected_cut_41987 : selected 10 ⟨1147904, by decide⟩
    (prefixPartial 11 84257) = some ⟨11, 2, 0, 1147904, 84257, 4065, 262144⟩ := by
  decide +kernel

theorem context_11_84257_1147904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84257 ⟨1147904, by decide⟩ :=
  accepted_of_selected 11 84257 ⟨1147904, by decide⟩ ⟨11, 2, 0, 1147904, 84257, 4065, 262144⟩
    (by decide) selected_cut_41987

theorem selected_cut_41988 : selected 10 ⟨1147971, by decide⟩
    (prefixPartial 11 84258) = some ⟨11, 2, 0, 1147971, 84258, 3917, 262144⟩ := by
  decide +kernel

theorem context_11_84258_1147971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84258 ⟨1147971, by decide⟩ :=
  accepted_of_selected 11 84258 ⟨1147971, by decide⟩ ⟨11, 2, 0, 1147971, 84258, 3917, 262144⟩
    (by decide) selected_cut_41988

theorem selected_cut_41989 : selected 9 ⟨1147984, by decide⟩
    (prefixPartial 12 337036) = some ⟨12, 2, 0, 1147984, 337036, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_337036_1147984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337036 ⟨1147984, by decide⟩ :=
  accepted_of_selected 12 337036 ⟨1147984, by decide⟩ ⟨12, 2, 0, 1147984, 337036, 1077, 65536⟩
    (by decide) selected_cut_41989

theorem selected_cut_41990 : selected 9 ⟨1147999, by decide⟩
    (prefixPartial 12 337037) = some ⟨12, 2, 0, 1147999, 337037, 1145, 65536⟩ := by
  decide +kernel

theorem context_12_337037_1147999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337037 ⟨1147999, by decide⟩ :=
  accepted_of_selected 12 337037 ⟨1147999, by decide⟩ ⟨12, 2, 0, 1147999, 337037, 1145, 65536⟩
    (by decide) selected_cut_41990

theorem selected_cut_41991 : selected 9 ⟨1148018, by decide⟩
    (prefixPartial 12 337038) = some ⟨12, 2, 0, 1148018, 337038, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_337038_1148018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337038 ⟨1148018, by decide⟩ :=
  accepted_of_selected 12 337038 ⟨1148018, by decide⟩ ⟨12, 2, 0, 1148018, 337038, 1193, 65536⟩
    (by decide) selected_cut_41991

theorem selected_cut_41992 : selected 9 ⟨1148030, by decide⟩
    (prefixPartial 12 337039) = some ⟨12, 2, 0, 1148030, 337039, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_337039_1148030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337039 ⟨1148030, by decide⟩ :=
  accepted_of_selected 12 337039 ⟨1148030, by decide⟩ ⟨12, 2, 0, 1148030, 337039, 1189, 65536⟩
    (by decide) selected_cut_41992

theorem unmarked_context_11_84259_1148031 : frontier 10 ⟨1148031, by decide⟩
    (prefixCache 11 84259) (prefixPartial 11 84259) = false := by
  decide +kernel

theorem node_context_11_84259_1148031 : EJMOriginalGlobalDAGData.nodes 10 ⟨1148031, by decide⟩ =
    .split (coordinate 11) (![⟨1147984, by decide⟩,⟨1147999, by decide⟩,⟨1148018, by decide⟩,⟨1148030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84259_1148031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84259 ⟨1148031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84259
    ⟨1148031, by decide⟩ (by decide) (![⟨1147984, by decide⟩,⟨1147999, by decide⟩,⟨1148018, by decide⟩,⟨1148030, by decide⟩]) unmarked_context_11_84259_1148031 node_context_11_84259_1148031
  intro a
  fin_cases a
  · exact context_12_337036_1147984
  · exact context_12_337037_1147999
  · exact context_12_337038_1148018
  · exact context_12_337039_1148030

theorem unmarked_context_10_21064_1148032 : frontier 11 ⟨1148032, by decide⟩
    (prefixCache 10 21064) (prefixPartial 10 21064) = false := by
  decide +kernel

theorem node_context_10_21064_1148032 : EJMOriginalGlobalDAGData.nodes 11 ⟨1148032, by decide⟩ =
    .split (coordinate 10) (![⟨1147821, by decide⟩,⟨1147904, by decide⟩,⟨1147971, by decide⟩,⟨1148031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21064_1148032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21064 ⟨1148032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21064
    ⟨1148032, by decide⟩ (by decide) (![⟨1147821, by decide⟩,⟨1147904, by decide⟩,⟨1147971, by decide⟩,⟨1148031, by decide⟩]) unmarked_context_10_21064_1148032 node_context_10_21064_1148032
  intro a
  fin_cases a
  · exact context_11_84256_1147821
  · exact context_11_84257_1147904
  · exact context_11_84258_1147971
  · exact context_11_84259_1148031

theorem selected_cut_41993 : selected 10 ⟨1148064, by decide⟩
    (prefixPartial 11 84260) = some ⟨11, 2, 0, 1148064, 84260, 2781, 262144⟩ := by
  decide +kernel

theorem context_11_84260_1148064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84260 ⟨1148064, by decide⟩ :=
  accepted_of_selected 11 84260 ⟨1148064, by decide⟩ ⟨11, 2, 0, 1148064, 84260, 2781, 262144⟩
    (by decide) selected_cut_41993

theorem selected_cut_41994 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 84261) = some ⟨11, 1, 0, 892405, 84261, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84261_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84261 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 84261 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 84261, 1, 262144⟩
    (by decide) selected_cut_41994

theorem selected_cut_41995 : selected 10 ⟨1148116, by decide⟩
    (prefixPartial 11 84262) = some ⟨11, 2, 0, 1148116, 84262, 3137, 262144⟩ := by
  decide +kernel

theorem context_11_84262_1148116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84262 ⟨1148116, by decide⟩ :=
  accepted_of_selected 11 84262 ⟨1148116, by decide⟩ ⟨11, 2, 0, 1148116, 84262, 3137, 262144⟩
    (by decide) selected_cut_41995

theorem selected_cut_41996 : selected 10 ⟨1148161, by decide⟩
    (prefixPartial 11 84263) = some ⟨11, 2, 0, 1148161, 84263, 3525, 262144⟩ := by
  decide +kernel

theorem context_11_84263_1148161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84263 ⟨1148161, by decide⟩ :=
  accepted_of_selected 11 84263 ⟨1148161, by decide⟩ ⟨11, 2, 0, 1148161, 84263, 3525, 262144⟩
    (by decide) selected_cut_41996

theorem unmarked_context_10_21065_1148162 : frontier 11 ⟨1148162, by decide⟩
    (prefixCache 10 21065) (prefixPartial 10 21065) = false := by
  decide +kernel

theorem node_context_10_21065_1148162 : EJMOriginalGlobalDAGData.nodes 11 ⟨1148162, by decide⟩ =
    .split (coordinate 10) (![⟨1148064, by decide⟩,⟨892405, by decide⟩,⟨1148116, by decide⟩,⟨1148161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21065_1148162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21065 ⟨1148162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21065
    ⟨1148162, by decide⟩ (by decide) (![⟨1148064, by decide⟩,⟨892405, by decide⟩,⟨1148116, by decide⟩,⟨1148161, by decide⟩]) unmarked_context_10_21065_1148162 node_context_10_21065_1148162
  intro a
  fin_cases a
  · exact context_11_84260_1148064
  · exact context_11_84261_892405
  · exact context_11_84262_1148116
  · exact context_11_84263_1148161

theorem selected_cut_41997 : selected 10 ⟨1148180, by decide⟩
    (prefixPartial 11 84264) = some ⟨11, 2, 0, 1148180, 84264, 1581, 262144⟩ := by
  decide +kernel

theorem context_11_84264_1148180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84264 ⟨1148180, by decide⟩ :=
  accepted_of_selected 11 84264 ⟨1148180, by decide⟩ ⟨11, 2, 0, 1148180, 84264, 1581, 262144⟩
    (by decide) selected_cut_41997

theorem selected_cut_41998 : selected 10 ⟨1148227, by decide⟩
    (prefixPartial 11 84265) = some ⟨11, 2, 0, 1148227, 84265, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_84265_1148227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84265 ⟨1148227, by decide⟩ :=
  accepted_of_selected 11 84265 ⟨1148227, by decide⟩ ⟨11, 2, 0, 1148227, 84265, 2545, 262144⟩
    (by decide) selected_cut_41998

theorem selected_cut_41999 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84266) = some ⟨11, 1, 0, 1109453, 84266, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84266_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84266 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84266 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84266, 1, 262144⟩
    (by decide) selected_cut_41999

theorem selected_cut_42000 : selected 10 ⟨1148261, by decide⟩
    (prefixPartial 11 84267) = some ⟨11, 2, 0, 1148261, 84267, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_84267_1148261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84267 ⟨1148261, by decide⟩ :=
  accepted_of_selected 11 84267 ⟨1148261, by decide⟩ ⟨11, 2, 0, 1148261, 84267, 2329, 262144⟩
    (by decide) selected_cut_42000

theorem unmarked_context_10_21066_1148262 : frontier 11 ⟨1148262, by decide⟩
    (prefixCache 10 21066) (prefixPartial 10 21066) = false := by
  decide +kernel

theorem node_context_10_21066_1148262 : EJMOriginalGlobalDAGData.nodes 11 ⟨1148262, by decide⟩ =
    .split (coordinate 10) (![⟨1148180, by decide⟩,⟨1148227, by decide⟩,⟨1109453, by decide⟩,⟨1148261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21066_1148262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21066 ⟨1148262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21066
    ⟨1148262, by decide⟩ (by decide) (![⟨1148180, by decide⟩,⟨1148227, by decide⟩,⟨1109453, by decide⟩,⟨1148261, by decide⟩]) unmarked_context_10_21066_1148262 node_context_10_21066_1148262
  intro a
  fin_cases a
  · exact context_11_84264_1148180
  · exact context_11_84265_1148227
  · exact context_11_84266_1109453
  · exact context_11_84267_1148261

theorem selected_cut_42001 : selected 10 ⟨1148291, by decide⟩
    (prefixPartial 11 84268) = some ⟨11, 2, 0, 1148291, 84268, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_84268_1148291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84268 ⟨1148291, by decide⟩ :=
  accepted_of_selected 11 84268 ⟨1148291, by decide⟩ ⟨11, 2, 0, 1148291, 84268, 2125, 262144⟩
    (by decide) selected_cut_42001

theorem selected_cut_42002 : selected 10 ⟨1148336, by decide⟩
    (prefixPartial 11 84269) = some ⟨11, 2, 0, 1148336, 84269, 2737, 262144⟩ := by
  decide +kernel

theorem context_11_84269_1148336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84269 ⟨1148336, by decide⟩ :=
  accepted_of_selected 11 84269 ⟨1148336, by decide⟩ ⟨11, 2, 0, 1148336, 84269, 2737, 262144⟩
    (by decide) selected_cut_42002

theorem selected_cut_42003 : selected 10 ⟨1148378, by decide⟩
    (prefixPartial 11 84270) = some ⟨11, 2, 0, 1148378, 84270, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_84270_1148378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84270 ⟨1148378, by decide⟩ :=
  accepted_of_selected 11 84270 ⟨1148378, by decide⟩ ⟨11, 2, 0, 1148378, 84270, 2113, 262144⟩
    (by decide) selected_cut_42003

theorem selected_cut_42004 : selected 10 ⟨1148403, by decide⟩
    (prefixPartial 11 84271) = some ⟨11, 2, 0, 1148403, 84271, 1569, 262144⟩ := by
  decide +kernel

theorem context_11_84271_1148403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84271 ⟨1148403, by decide⟩ :=
  accepted_of_selected 11 84271 ⟨1148403, by decide⟩ ⟨11, 2, 0, 1148403, 84271, 1569, 262144⟩
    (by decide) selected_cut_42004

theorem unmarked_context_10_21067_1148404 : frontier 11 ⟨1148404, by decide⟩
    (prefixCache 10 21067) (prefixPartial 10 21067) = false := by
  decide +kernel

theorem node_context_10_21067_1148404 : EJMOriginalGlobalDAGData.nodes 11 ⟨1148404, by decide⟩ =
    .split (coordinate 10) (![⟨1148291, by decide⟩,⟨1148336, by decide⟩,⟨1148378, by decide⟩,⟨1148403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21067_1148404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21067 ⟨1148404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21067
    ⟨1148404, by decide⟩ (by decide) (![⟨1148291, by decide⟩,⟨1148336, by decide⟩,⟨1148378, by decide⟩,⟨1148403, by decide⟩]) unmarked_context_10_21067_1148404 node_context_10_21067_1148404
  intro a
  fin_cases a
  · exact context_11_84268_1148291
  · exact context_11_84269_1148336
  · exact context_11_84270_1148378
  · exact context_11_84271_1148403

theorem unmarked_context_9_5266_1148405 : frontier 12 ⟨1148405, by decide⟩
    (prefixCache 9 5266) (prefixPartial 9 5266) = false := by
  decide +kernel

theorem node_context_9_5266_1148405 : EJMOriginalGlobalDAGData.nodes 12 ⟨1148405, by decide⟩ =
    .split (coordinate 9) (![⟨1148032, by decide⟩,⟨1148162, by decide⟩,⟨1148262, by decide⟩,⟨1148404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5266_1148405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5266 ⟨1148405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5266
    ⟨1148405, by decide⟩ (by decide) (![⟨1148032, by decide⟩,⟨1148162, by decide⟩,⟨1148262, by decide⟩,⟨1148404, by decide⟩]) unmarked_context_9_5266_1148405 node_context_9_5266_1148405
  intro a
  fin_cases a
  · exact context_10_21064_1148032
  · exact context_10_21065_1148162
  · exact context_10_21066_1148262
  · exact context_10_21067_1148404

theorem selected_cut_42005 : selected 10 ⟨1148422, by decide⟩
    (prefixPartial 11 84272) = some ⟨11, 2, 0, 1148422, 84272, 1017, 262144⟩ := by
  decide +kernel

theorem context_11_84272_1148422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84272 ⟨1148422, by decide⟩ :=
  accepted_of_selected 11 84272 ⟨1148422, by decide⟩ ⟨11, 2, 0, 1148422, 84272, 1017, 262144⟩
    (by decide) selected_cut_42005

theorem selected_cut_42006 : selected 10 ⟨1148443, by decide⟩
    (prefixPartial 11 84273) = some ⟨11, 2, 0, 1148443, 84273, 1337, 262144⟩ := by
  decide +kernel

theorem context_11_84273_1148443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84273 ⟨1148443, by decide⟩ :=
  accepted_of_selected 11 84273 ⟨1148443, by decide⟩ ⟨11, 2, 0, 1148443, 84273, 1337, 262144⟩
    (by decide) selected_cut_42006

theorem selected_cut_42007 : selected 10 ⟨1148460, by decide⟩
    (prefixPartial 11 84274) = some ⟨11, 2, 0, 1148460, 84274, 1597, 262144⟩ := by
  decide +kernel

theorem context_11_84274_1148460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84274 ⟨1148460, by decide⟩ :=
  accepted_of_selected 11 84274 ⟨1148460, by decide⟩ ⟨11, 2, 0, 1148460, 84274, 1597, 262144⟩
    (by decide) selected_cut_42007

theorem selected_cut_42008 : selected 10 ⟨1148481, by decide⟩
    (prefixPartial 11 84275) = some ⟨11, 2, 0, 1148481, 84275, 1173, 262144⟩ := by
  decide +kernel

theorem context_11_84275_1148481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84275 ⟨1148481, by decide⟩ :=
  accepted_of_selected 11 84275 ⟨1148481, by decide⟩ ⟨11, 2, 0, 1148481, 84275, 1173, 262144⟩
    (by decide) selected_cut_42008

theorem unmarked_context_10_21068_1148482 : frontier 11 ⟨1148482, by decide⟩
    (prefixCache 10 21068) (prefixPartial 10 21068) = false := by
  decide +kernel

theorem node_context_10_21068_1148482 : EJMOriginalGlobalDAGData.nodes 11 ⟨1148482, by decide⟩ =
    .split (coordinate 10) (![⟨1148422, by decide⟩,⟨1148443, by decide⟩,⟨1148460, by decide⟩,⟨1148481, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21068_1148482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21068 ⟨1148482, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21068
    ⟨1148482, by decide⟩ (by decide) (![⟨1148422, by decide⟩,⟨1148443, by decide⟩,⟨1148460, by decide⟩,⟨1148481, by decide⟩]) unmarked_context_10_21068_1148482 node_context_10_21068_1148482
  intro a
  fin_cases a
  · exact context_11_84272_1148422
  · exact context_11_84273_1148443
  · exact context_11_84274_1148460
  · exact context_11_84275_1148481

theorem selected_cut_42009 : selected 11 ⟨1148518, by decide⟩
    (prefixPartial 10 21069) = some ⟨10, 2, 0, 1148518, 21069, 2725, 1048576⟩ := by
  decide +kernel

theorem context_10_21069_1148518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21069 ⟨1148518, by decide⟩ :=
  accepted_of_selected 10 21069 ⟨1148518, by decide⟩ ⟨10, 2, 0, 1148518, 21069, 2725, 1048576⟩
    (by decide) selected_cut_42009

theorem selected_cut_42010 : selected 11 ⟨1148553, by decide⟩
    (prefixPartial 10 21070) = some ⟨10, 2, 0, 1148553, 21070, 2149, 1048576⟩ := by
  decide +kernel

theorem context_10_21070_1148553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21070 ⟨1148553, by decide⟩ :=
  accepted_of_selected 10 21070 ⟨1148553, by decide⟩ ⟨10, 2, 0, 1148553, 21070, 2149, 1048576⟩
    (by decide) selected_cut_42010

theorem selected_cut_42011 : selected 11 ⟨1148563, by decide⟩
    (prefixPartial 10 21071) = some ⟨10, 2, 0, 1148563, 21071, 457, 1048576⟩ := by
  decide +kernel

theorem context_10_21071_1148563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21071 ⟨1148563, by decide⟩ :=
  accepted_of_selected 10 21071 ⟨1148563, by decide⟩ ⟨10, 2, 0, 1148563, 21071, 457, 1048576⟩
    (by decide) selected_cut_42011

theorem unmarked_context_9_5267_1148564 : frontier 12 ⟨1148564, by decide⟩
    (prefixCache 9 5267) (prefixPartial 9 5267) = false := by
  decide +kernel

theorem node_context_9_5267_1148564 : EJMOriginalGlobalDAGData.nodes 12 ⟨1148564, by decide⟩ =
    .split (coordinate 9) (![⟨1148482, by decide⟩,⟨1148518, by decide⟩,⟨1148553, by decide⟩,⟨1148563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5267_1148564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5267 ⟨1148564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5267
    ⟨1148564, by decide⟩ (by decide) (![⟨1148482, by decide⟩,⟨1148518, by decide⟩,⟨1148553, by decide⟩,⟨1148563, by decide⟩]) unmarked_context_9_5267_1148564 node_context_9_5267_1148564
  intro a
  fin_cases a
  · exact context_10_21068_1148482
  · exact context_10_21069_1148518
  · exact context_10_21070_1148553
  · exact context_10_21071_1148563

theorem unmarked_context_8_1316_1148565 : frontier 13 ⟨1148565, by decide⟩
    (prefixCache 8 1316) (prefixPartial 8 1316) = false := by
  decide +kernel

theorem node_context_8_1316_1148565 : EJMOriginalGlobalDAGData.nodes 13 ⟨1148565, by decide⟩ =
    .split (coordinate 8) (![⟨1146576, by decide⟩,⟨1147758, by decide⟩,⟨1148405, by decide⟩,⟨1148564, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1316_1148565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1316 ⟨1148565, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1316
    ⟨1148565, by decide⟩ (by decide) (![⟨1146576, by decide⟩,⟨1147758, by decide⟩,⟨1148405, by decide⟩,⟨1148564, by decide⟩]) unmarked_context_8_1316_1148565 node_context_8_1316_1148565
  intro a
  fin_cases a
  · exact context_9_5264_1146576
  · exact context_9_5265_1147758
  · exact context_9_5266_1148405
  · exact context_9_5267_1148564

theorem selected_cut_42012 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84288) = some ⟨11, 1, 0, 434745, 84288, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84288_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84288 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84288 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84288, 1, 262144⟩
    (by decide) selected_cut_42012

theorem selected_cut_42013 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337156) = some ⟨12, 1, 0, 448748, 337156, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337156_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337156 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337156 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337156, 1, 65536⟩
    (by decide) selected_cut_42013

theorem selected_cut_42014 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 337157) = some ⟨12, 1, 0, 34034, 337157, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337157_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337157 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 337157 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 337157, 1, 65536⟩
    (by decide) selected_cut_42014

theorem selected_cut_42015 : selected 9 ⟨1148599, by decide⟩
    (prefixPartial 12 337158) = some ⟨12, 2, 0, 1148599, 337158, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_337158_1148599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337158 ⟨1148599, by decide⟩ :=
  accepted_of_selected 12 337158 ⟨1148599, by decide⟩ ⟨12, 2, 0, 1148599, 337158, 2437, 65536⟩
    (by decide) selected_cut_42015

theorem selected_cut_42016 : selected 9 ⟨1148643, by decide⟩
    (prefixPartial 12 337159) = some ⟨12, 2, 0, 1148643, 337159, 2657, 65536⟩ := by
  decide +kernel

theorem context_12_337159_1148643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337159 ⟨1148643, by decide⟩ :=
  accepted_of_selected 12 337159 ⟨1148643, by decide⟩ ⟨12, 2, 0, 1148643, 337159, 2657, 65536⟩
    (by decide) selected_cut_42016

theorem unmarked_context_11_84289_1148644 : frontier 10 ⟨1148644, by decide⟩
    (prefixCache 11 84289) (prefixPartial 11 84289) = false := by
  decide +kernel

theorem node_context_11_84289_1148644 : EJMOriginalGlobalDAGData.nodes 10 ⟨1148644, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1148599, by decide⟩,⟨1148643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84289_1148644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84289 ⟨1148644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84289
    ⟨1148644, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1148599, by decide⟩,⟨1148643, by decide⟩]) unmarked_context_11_84289_1148644 node_context_11_84289_1148644
  intro a
  fin_cases a
  · exact context_12_337156_448748
  · exact context_12_337157_34034
  · exact context_12_337158_1148599
  · exact context_12_337159_1148643

theorem selected_cut_42017 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337160) = some ⟨12, 1, 0, 448748, 337160, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337160_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337160 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337160 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337160, 1, 65536⟩
    (by decide) selected_cut_42017

theorem selected_cut_42018 : selected 9 ⟨1148700, by decide⟩
    (prefixPartial 12 337161) = some ⟨12, 2, 0, 1148700, 337161, 2673, 65536⟩ := by
  decide +kernel

theorem context_12_337161_1148700 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337161 ⟨1148700, by decide⟩ :=
  accepted_of_selected 12 337161 ⟨1148700, by decide⟩ ⟨12, 2, 0, 1148700, 337161, 2673, 65536⟩
    (by decide) selected_cut_42018

theorem selected_cut_42019 : selected 9 ⟨1148745, by decide⟩
    (prefixPartial 12 337162) = some ⟨12, 2, 0, 1148745, 337162, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_337162_1148745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337162 ⟨1148745, by decide⟩ :=
  accepted_of_selected 12 337162 ⟨1148745, by decide⟩ ⟨12, 2, 0, 1148745, 337162, 2821, 65536⟩
    (by decide) selected_cut_42019

theorem selected_cut_42020 : selected 9 ⟨1148795, by decide⟩
    (prefixPartial 12 337163) = some ⟨12, 2, 0, 1148795, 337163, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_337163_1148795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337163 ⟨1148795, by decide⟩ :=
  accepted_of_selected 12 337163 ⟨1148795, by decide⟩ ⟨12, 2, 0, 1148795, 337163, 3005, 65536⟩
    (by decide) selected_cut_42020

theorem unmarked_context_11_84290_1148796 : frontier 10 ⟨1148796, by decide⟩
    (prefixCache 11 84290) (prefixPartial 11 84290) = false := by
  decide +kernel

theorem node_context_11_84290_1148796 : EJMOriginalGlobalDAGData.nodes 10 ⟨1148796, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1148700, by decide⟩,⟨1148745, by decide⟩,⟨1148795, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84290_1148796 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84290 ⟨1148796, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84290
    ⟨1148796, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1148700, by decide⟩,⟨1148745, by decide⟩,⟨1148795, by decide⟩]) unmarked_context_11_84290_1148796 node_context_11_84290_1148796
  intro a
  fin_cases a
  · exact context_12_337160_448748
  · exact context_12_337161_1148700
  · exact context_12_337162_1148745
  · exact context_12_337163_1148795

theorem selected_cut_42021 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 337164) = some ⟨12, 1, 0, 448748, 337164, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337164_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337164 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 337164 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 337164, 1, 65536⟩
    (by decide) selected_cut_42021

theorem selected_cut_42022 : selected 9 ⟨1148826, by decide⟩
    (prefixPartial 12 337165) = some ⟨12, 2, 0, 1148826, 337165, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_337165_1148826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337165 ⟨1148826, by decide⟩ :=
  accepted_of_selected 12 337165 ⟨1148826, by decide⟩ ⟨12, 2, 0, 1148826, 337165, 1305, 65536⟩
    (by decide) selected_cut_42022

theorem selected_cut_42023 : selected 9 ⟨1148861, by decide⟩
    (prefixPartial 12 337166) = some ⟨12, 2, 0, 1148861, 337166, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_337166_1148861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337166 ⟨1148861, by decide⟩ :=
  accepted_of_selected 12 337166 ⟨1148861, by decide⟩ ⟨12, 2, 0, 1148861, 337166, 2565, 65536⟩
    (by decide) selected_cut_42023

theorem selected_cut_42024 : selected 9 ⟨1148904, by decide⟩
    (prefixPartial 12 337167) = some ⟨12, 2, 0, 1148904, 337167, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_337167_1148904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337167 ⟨1148904, by decide⟩ :=
  accepted_of_selected 12 337167 ⟨1148904, by decide⟩ ⟨12, 2, 0, 1148904, 337167, 2897, 65536⟩
    (by decide) selected_cut_42024

theorem unmarked_context_11_84291_1148905 : frontier 10 ⟨1148905, by decide⟩
    (prefixCache 11 84291) (prefixPartial 11 84291) = false := by
  decide +kernel

theorem node_context_11_84291_1148905 : EJMOriginalGlobalDAGData.nodes 10 ⟨1148905, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1148826, by decide⟩,⟨1148861, by decide⟩,⟨1148904, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84291_1148905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84291 ⟨1148905, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84291
    ⟨1148905, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1148826, by decide⟩,⟨1148861, by decide⟩,⟨1148904, by decide⟩]) unmarked_context_11_84291_1148905 node_context_11_84291_1148905
  intro a
  fin_cases a
  · exact context_12_337164_448748
  · exact context_12_337165_1148826
  · exact context_12_337166_1148861
  · exact context_12_337167_1148904

theorem unmarked_context_10_21072_1148906 : frontier 11 ⟨1148906, by decide⟩
    (prefixCache 10 21072) (prefixPartial 10 21072) = false := by
  decide +kernel

theorem node_context_10_21072_1148906 : EJMOriginalGlobalDAGData.nodes 11 ⟨1148906, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1148644, by decide⟩,⟨1148796, by decide⟩,⟨1148905, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21072_1148906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21072 ⟨1148906, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21072
    ⟨1148906, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1148644, by decide⟩,⟨1148796, by decide⟩,⟨1148905, by decide⟩]) unmarked_context_10_21072_1148906 node_context_10_21072_1148906
  intro a
  fin_cases a
  · exact context_11_84288_434745
  · exact context_11_84289_1148644
  · exact context_11_84290_1148796
  · exact context_11_84291_1148905

theorem selected_cut_42025 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337168) = some ⟨12, 1, 0, 1108174, 337168, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337168_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337168 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337168 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337168, 1, 65536⟩
    (by decide) selected_cut_42025

theorem selected_cut_42026 : selected 9 ⟨1148949, by decide⟩
    (prefixPartial 12 337169) = some ⟨12, 2, 0, 1148949, 337169, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_337169_1148949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337169 ⟨1148949, by decide⟩ :=
  accepted_of_selected 12 337169 ⟨1148949, by decide⟩ ⟨12, 2, 0, 1148949, 337169, 2201, 65536⟩
    (by decide) selected_cut_42026

theorem selected_cut_42027 : selected 9 ⟨1148996, by decide⟩
    (prefixPartial 12 337170) = some ⟨12, 2, 0, 1148996, 337170, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_337170_1148996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337170 ⟨1148996, by decide⟩ :=
  accepted_of_selected 12 337170 ⟨1148996, by decide⟩ ⟨12, 2, 0, 1148996, 337170, 2629, 65536⟩
    (by decide) selected_cut_42027

theorem selected_cut_42028 : selected 9 ⟨1149042, by decide⟩
    (prefixPartial 12 337171) = some ⟨12, 2, 0, 1149042, 337171, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_337171_1149042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337171 ⟨1149042, by decide⟩ :=
  accepted_of_selected 12 337171 ⟨1149042, by decide⟩ ⟨12, 2, 0, 1149042, 337171, 2721, 65536⟩
    (by decide) selected_cut_42028

theorem unmarked_context_11_84292_1149043 : frontier 10 ⟨1149043, by decide⟩
    (prefixCache 11 84292) (prefixPartial 11 84292) = false := by
  decide +kernel

theorem node_context_11_84292_1149043 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149043, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1148949, by decide⟩,⟨1148996, by decide⟩,⟨1149042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84292_1149043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84292 ⟨1149043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84292
    ⟨1149043, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1148949, by decide⟩,⟨1148996, by decide⟩,⟨1149042, by decide⟩]) unmarked_context_11_84292_1149043 node_context_11_84292_1149043
  intro a
  fin_cases a
  · exact context_12_337168_1108174
  · exact context_12_337169_1148949
  · exact context_12_337170_1148996
  · exact context_12_337171_1149042

theorem selected_cut_42029 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 84293) = some ⟨11, 1, 0, 892405, 84293, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84293_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84293 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 84293 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 84293, 1, 262144⟩
    (by decide) selected_cut_42029

theorem selected_cut_42030 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337176) = some ⟨12, 1, 0, 1108174, 337176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337176_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337176 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337176 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337176, 1, 65536⟩
    (by decide) selected_cut_42030

theorem selected_cut_42031 : selected 9 ⟨1149078, by decide⟩
    (prefixPartial 12 337177) = some ⟨12, 2, 0, 1149078, 337177, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_337177_1149078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337177 ⟨1149078, by decide⟩ :=
  accepted_of_selected 12 337177 ⟨1149078, by decide⟩ ⟨12, 2, 0, 1149078, 337177, 2065, 65536⟩
    (by decide) selected_cut_42031

theorem selected_cut_42032 : selected 9 ⟨1149120, by decide⟩
    (prefixPartial 12 337178) = some ⟨12, 2, 0, 1149120, 337178, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_337178_1149120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337178 ⟨1149120, by decide⟩ :=
  accepted_of_selected 12 337178 ⟨1149120, by decide⟩ ⟨12, 2, 0, 1149120, 337178, 2453, 65536⟩
    (by decide) selected_cut_42032

theorem selected_cut_42033 : selected 9 ⟨1149160, by decide⟩
    (prefixPartial 12 337179) = some ⟨12, 2, 0, 1149160, 337179, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_337179_1149160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337179 ⟨1149160, by decide⟩ :=
  accepted_of_selected 12 337179 ⟨1149160, by decide⟩ ⟨12, 2, 0, 1149160, 337179, 2453, 65536⟩
    (by decide) selected_cut_42033

theorem unmarked_context_11_84294_1149161 : frontier 10 ⟨1149161, by decide⟩
    (prefixCache 11 84294) (prefixPartial 11 84294) = false := by
  decide +kernel

theorem node_context_11_84294_1149161 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149161, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1149078, by decide⟩,⟨1149120, by decide⟩,⟨1149160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84294_1149161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84294 ⟨1149161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84294
    ⟨1149161, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1149078, by decide⟩,⟨1149120, by decide⟩,⟨1149160, by decide⟩]) unmarked_context_11_84294_1149161 node_context_11_84294_1149161
  intro a
  fin_cases a
  · exact context_12_337176_1108174
  · exact context_12_337177_1149078
  · exact context_12_337178_1149120
  · exact context_12_337179_1149160

theorem selected_cut_42034 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337180) = some ⟨12, 1, 0, 1108174, 337180, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337180_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337180 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337180 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337180, 1, 65536⟩
    (by decide) selected_cut_42034

theorem selected_cut_42035 : selected 9 ⟨1149192, by decide⟩
    (prefixPartial 12 337181) = some ⟨12, 2, 0, 1149192, 337181, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_337181_1149192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337181 ⟨1149192, by decide⟩ :=
  accepted_of_selected 12 337181 ⟨1149192, by decide⟩ ⟨12, 2, 0, 1149192, 337181, 1973, 65536⟩
    (by decide) selected_cut_42035

theorem selected_cut_42036 : selected 9 ⟨1149226, by decide⟩
    (prefixPartial 12 337182) = some ⟨12, 2, 0, 1149226, 337182, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_337182_1149226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337182 ⟨1149226, by decide⟩ :=
  accepted_of_selected 12 337182 ⟨1149226, by decide⟩ ⟨12, 2, 0, 1149226, 337182, 2289, 65536⟩
    (by decide) selected_cut_42036

theorem selected_cut_42037 : selected 9 ⟨1149261, by decide⟩
    (prefixPartial 12 337183) = some ⟨12, 2, 0, 1149261, 337183, 2525, 65536⟩ := by
  decide +kernel

theorem context_12_337183_1149261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337183 ⟨1149261, by decide⟩ :=
  accepted_of_selected 12 337183 ⟨1149261, by decide⟩ ⟨12, 2, 0, 1149261, 337183, 2525, 65536⟩
    (by decide) selected_cut_42037

theorem unmarked_context_11_84295_1149262 : frontier 10 ⟨1149262, by decide⟩
    (prefixCache 11 84295) (prefixPartial 11 84295) = false := by
  decide +kernel

theorem node_context_11_84295_1149262 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149262, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1149192, by decide⟩,⟨1149226, by decide⟩,⟨1149261, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84295_1149262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84295 ⟨1149262, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84295
    ⟨1149262, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1149192, by decide⟩,⟨1149226, by decide⟩,⟨1149261, by decide⟩]) unmarked_context_11_84295_1149262 node_context_11_84295_1149262
  intro a
  fin_cases a
  · exact context_12_337180_1108174
  · exact context_12_337181_1149192
  · exact context_12_337182_1149226
  · exact context_12_337183_1149261

theorem unmarked_context_10_21073_1149263 : frontier 11 ⟨1149263, by decide⟩
    (prefixCache 10 21073) (prefixPartial 10 21073) = false := by
  decide +kernel

theorem node_context_10_21073_1149263 : EJMOriginalGlobalDAGData.nodes 11 ⟨1149263, by decide⟩ =
    .split (coordinate 10) (![⟨1149043, by decide⟩,⟨892405, by decide⟩,⟨1149161, by decide⟩,⟨1149262, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21073_1149263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21073 ⟨1149263, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21073
    ⟨1149263, by decide⟩ (by decide) (![⟨1149043, by decide⟩,⟨892405, by decide⟩,⟨1149161, by decide⟩,⟨1149262, by decide⟩]) unmarked_context_10_21073_1149263 node_context_10_21073_1149263
  intro a
  fin_cases a
  · exact context_11_84292_1149043
  · exact context_11_84293_892405
  · exact context_11_84294_1149161
  · exact context_11_84295_1149262

theorem selected_cut_42038 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337184) = some ⟨12, 1, 0, 1108174, 337184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337184_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337184 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337184 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337184, 1, 65536⟩
    (by decide) selected_cut_42038

theorem selected_cut_42039 : selected 9 ⟨1149310, by decide⟩
    (prefixPartial 12 337185) = some ⟨12, 2, 0, 1149310, 337185, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_337185_1149310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337185 ⟨1149310, by decide⟩ :=
  accepted_of_selected 12 337185 ⟨1149310, by decide⟩ ⟨12, 2, 0, 1149310, 337185, 2437, 65536⟩
    (by decide) selected_cut_42039

theorem selected_cut_42040 : selected 9 ⟨1149352, by decide⟩
    (prefixPartial 12 337186) = some ⟨12, 2, 0, 1149352, 337186, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_337186_1149352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337186 ⟨1149352, by decide⟩ :=
  accepted_of_selected 12 337186 ⟨1149352, by decide⟩ ⟨12, 2, 0, 1149352, 337186, 2501, 65536⟩
    (by decide) selected_cut_42040

theorem selected_cut_42041 : selected 9 ⟨1149410, by decide⟩
    (prefixPartial 12 337187) = some ⟨12, 2, 0, 1149410, 337187, 2869, 65536⟩ := by
  decide +kernel

theorem context_12_337187_1149410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337187 ⟨1149410, by decide⟩ :=
  accepted_of_selected 12 337187 ⟨1149410, by decide⟩ ⟨12, 2, 0, 1149410, 337187, 2869, 65536⟩
    (by decide) selected_cut_42041

theorem unmarked_context_11_84296_1149411 : frontier 10 ⟨1149411, by decide⟩
    (prefixCache 11 84296) (prefixPartial 11 84296) = false := by
  decide +kernel

theorem node_context_11_84296_1149411 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149411, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1149310, by decide⟩,⟨1149352, by decide⟩,⟨1149410, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84296_1149411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84296 ⟨1149411, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84296
    ⟨1149411, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1149310, by decide⟩,⟨1149352, by decide⟩,⟨1149410, by decide⟩]) unmarked_context_11_84296_1149411 node_context_11_84296_1149411
  intro a
  fin_cases a
  · exact context_12_337184_1108174
  · exact context_12_337185_1149310
  · exact context_12_337186_1149352
  · exact context_12_337187_1149410

theorem selected_cut_42042 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337188) = some ⟨12, 1, 0, 1108174, 337188, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337188_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337188 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337188 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337188, 1, 65536⟩
    (by decide) selected_cut_42042

theorem selected_cut_42043 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 337189) = some ⟨12, 1, 0, 891951, 337189, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337189_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337189 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 337189 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 337189, 1, 65536⟩
    (by decide) selected_cut_42043

theorem selected_cut_42044 : selected 9 ⟨1149444, by decide⟩
    (prefixPartial 12 337190) = some ⟨12, 2, 0, 1149444, 337190, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_337190_1149444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337190 ⟨1149444, by decide⟩ :=
  accepted_of_selected 12 337190 ⟨1149444, by decide⟩ ⟨12, 2, 0, 1149444, 337190, 2241, 65536⟩
    (by decide) selected_cut_42044

theorem selected_cut_42045 : selected 9 ⟨1149490, by decide⟩
    (prefixPartial 12 337191) = some ⟨12, 2, 0, 1149490, 337191, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_337191_1149490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337191 ⟨1149490, by decide⟩ :=
  accepted_of_selected 12 337191 ⟨1149490, by decide⟩ ⟨12, 2, 0, 1149490, 337191, 2437, 65536⟩
    (by decide) selected_cut_42045

theorem unmarked_context_11_84297_1149491 : frontier 10 ⟨1149491, by decide⟩
    (prefixCache 11 84297) (prefixPartial 11 84297) = false := by
  decide +kernel

theorem node_context_11_84297_1149491 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149491, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1149444, by decide⟩,⟨1149490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84297_1149491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84297 ⟨1149491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84297
    ⟨1149491, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1149444, by decide⟩,⟨1149490, by decide⟩]) unmarked_context_11_84297_1149491 node_context_11_84297_1149491
  intro a
  fin_cases a
  · exact context_12_337188_1108174
  · exact context_12_337189_891951
  · exact context_12_337190_1149444
  · exact context_12_337191_1149490

theorem selected_cut_42046 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337192) = some ⟨12, 1, 0, 1108174, 337192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337192_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337192 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337192 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337192, 1, 65536⟩
    (by decide) selected_cut_42046

theorem selected_cut_42047 : selected 9 ⟨1149518, by decide⟩
    (prefixPartial 12 337193) = some ⟨12, 2, 0, 1149518, 337193, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_337193_1149518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337193 ⟨1149518, by decide⟩ :=
  accepted_of_selected 12 337193 ⟨1149518, by decide⟩ ⟨12, 2, 0, 1149518, 337193, 2077, 65536⟩
    (by decide) selected_cut_42047

theorem selected_cut_42048 : selected 9 ⟨1113261, by decide⟩
    (prefixPartial 12 337194) = some ⟨12, 1, 0, 1113261, 337194, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337194_1113261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337194 ⟨1113261, by decide⟩ :=
  accepted_of_selected 12 337194 ⟨1113261, by decide⟩ ⟨12, 1, 0, 1113261, 337194, 1, 65536⟩
    (by decide) selected_cut_42048

theorem selected_cut_42049 : selected 9 ⟨1149560, by decide⟩
    (prefixPartial 12 337195) = some ⟨12, 2, 0, 1149560, 337195, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_337195_1149560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337195 ⟨1149560, by decide⟩ :=
  accepted_of_selected 12 337195 ⟨1149560, by decide⟩ ⟨12, 2, 0, 1149560, 337195, 2385, 65536⟩
    (by decide) selected_cut_42049

theorem unmarked_context_11_84298_1149561 : frontier 10 ⟨1149561, by decide⟩
    (prefixCache 11 84298) (prefixPartial 11 84298) = false := by
  decide +kernel

theorem node_context_11_84298_1149561 : EJMOriginalGlobalDAGData.nodes 10 ⟨1149561, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1149518, by decide⟩,⟨1113261, by decide⟩,⟨1149560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84298_1149561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84298 ⟨1149561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84298
    ⟨1149561, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1149518, by decide⟩,⟨1113261, by decide⟩,⟨1149560, by decide⟩]) unmarked_context_11_84298_1149561 node_context_11_84298_1149561
  intro a
  fin_cases a
  · exact context_12_337192_1108174
  · exact context_12_337193_1149518
  · exact context_12_337194_1113261
  · exact context_12_337195_1149560

theorem selected_cut_42050 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 337196) = some ⟨12, 1, 0, 1108174, 337196, 1, 65536⟩ := by
  decide +kernel

theorem context_12_337196_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 337196 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 337196 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 337196, 1, 65536⟩
    (by decide) selected_cut_42050

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
