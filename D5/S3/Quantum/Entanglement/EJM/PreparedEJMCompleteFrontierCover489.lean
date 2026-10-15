/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover488
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_92997_1311701 : frontier 10 ⟨1311701, by decide⟩
    (prefixCache 11 92997) (prefixPartial 11 92997) = false := by
  decide +kernel

theorem node_context_11_92997_1311701 : EJMOriginalGlobalDAGData.nodes 10 ⟨1311701, by decide⟩ =
    .split (coordinate 11) (![⟨1311657, by decide⟩,⟨1172003, by decide⟩,⟨1311700, by decide⟩,⟨692794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92997_1311701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92997 ⟨1311701, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92997
    ⟨1311701, by decide⟩ (by decide) (![⟨1311657, by decide⟩,⟨1172003, by decide⟩,⟨1311700, by decide⟩,⟨692794, by decide⟩]) unmarked_context_11_92997_1311701 node_context_11_92997_1311701
  intro a
  fin_cases a
  · exact context_12_371988_1311657
  · exact context_12_371989_1172003
  · exact context_12_371990_1311700
  · exact context_12_371991_692794

theorem selected_cut_46948 : selected 9 ⟨1055595, by decide⟩
    (prefixPartial 12 371992) = some ⟨12, 1, 0, 1055595, 371992, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371992_1055595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371992 ⟨1055595, by decide⟩ :=
  accepted_of_selected 12 371992 ⟨1055595, by decide⟩ ⟨12, 1, 0, 1055595, 371992, 1, 65536⟩
    (by decide) selected_cut_46948

theorem selected_cut_46949 : selected 9 ⟨1311760, by decide⟩
    (prefixPartial 12 371993) = some ⟨12, 2, 0, 1311760, 371993, 2893, 65536⟩ := by
  decide +kernel

theorem context_12_371993_1311760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371993 ⟨1311760, by decide⟩ :=
  accepted_of_selected 12 371993 ⟨1311760, by decide⟩ ⟨12, 2, 0, 1311760, 371993, 2893, 65536⟩
    (by decide) selected_cut_46949

theorem selected_cut_46950 : selected 9 ⟨1311813, by decide⟩
    (prefixPartial 12 371994) = some ⟨12, 2, 0, 1311813, 371994, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_371994_1311813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371994 ⟨1311813, by decide⟩ :=
  accepted_of_selected 12 371994 ⟨1311813, by decide⟩ ⟨12, 2, 0, 1311813, 371994, 2453, 65536⟩
    (by decide) selected_cut_46950

theorem selected_cut_46951 : selected 9 ⟨1311861, by decide⟩
    (prefixPartial 12 371995) = some ⟨12, 2, 0, 1311861, 371995, 2797, 65536⟩ := by
  decide +kernel

theorem context_12_371995_1311861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371995 ⟨1311861, by decide⟩ :=
  accepted_of_selected 12 371995 ⟨1311861, by decide⟩ ⟨12, 2, 0, 1311861, 371995, 2797, 65536⟩
    (by decide) selected_cut_46951

theorem unmarked_context_11_92998_1311862 : frontier 10 ⟨1311862, by decide⟩
    (prefixCache 11 92998) (prefixPartial 11 92998) = false := by
  decide +kernel

theorem node_context_11_92998_1311862 : EJMOriginalGlobalDAGData.nodes 10 ⟨1311862, by decide⟩ =
    .split (coordinate 11) (![⟨1055595, by decide⟩,⟨1311760, by decide⟩,⟨1311813, by decide⟩,⟨1311861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92998_1311862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92998 ⟨1311862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92998
    ⟨1311862, by decide⟩ (by decide) (![⟨1055595, by decide⟩,⟨1311760, by decide⟩,⟨1311813, by decide⟩,⟨1311861, by decide⟩]) unmarked_context_11_92998_1311862 node_context_11_92998_1311862
  intro a
  fin_cases a
  · exact context_12_371992_1055595
  · exact context_12_371993_1311760
  · exact context_12_371994_1311813
  · exact context_12_371995_1311861

theorem selected_cut_46952 : selected 9 ⟨1311903, by decide⟩
    (prefixPartial 12 371996) = some ⟨12, 2, 0, 1311903, 371996, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_371996_1311903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371996 ⟨1311903, by decide⟩ :=
  accepted_of_selected 12 371996 ⟨1311903, by decide⟩ ⟨12, 2, 0, 1311903, 371996, 2281, 65536⟩
    (by decide) selected_cut_46952

theorem selected_cut_46953 : selected 9 ⟨1311943, by decide⟩
    (prefixPartial 12 371997) = some ⟨12, 2, 0, 1311943, 371997, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_371997_1311943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371997 ⟨1311943, by decide⟩ :=
  accepted_of_selected 12 371997 ⟨1311943, by decide⟩ ⟨12, 2, 0, 1311943, 371997, 2557, 65536⟩
    (by decide) selected_cut_46953

theorem selected_cut_46954 : selected 9 ⟨1311975, by decide⟩
    (prefixPartial 12 371998) = some ⟨12, 2, 0, 1311975, 371998, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_371998_1311975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371998 ⟨1311975, by decide⟩ :=
  accepted_of_selected 12 371998 ⟨1311975, by decide⟩ ⟨12, 2, 0, 1311975, 371998, 2161, 65536⟩
    (by decide) selected_cut_46954

theorem selected_cut_46955 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 371999) = some ⟨12, 1, 0, 757807, 371999, 1, 65536⟩ := by
  decide +kernel

theorem context_12_371999_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 371999 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 371999 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 371999, 1, 65536⟩
    (by decide) selected_cut_46955

theorem unmarked_context_11_92999_1311976 : frontier 10 ⟨1311976, by decide⟩
    (prefixCache 11 92999) (prefixPartial 11 92999) = false := by
  decide +kernel

theorem node_context_11_92999_1311976 : EJMOriginalGlobalDAGData.nodes 10 ⟨1311976, by decide⟩ =
    .split (coordinate 11) (![⟨1311903, by decide⟩,⟨1311943, by decide⟩,⟨1311975, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_92999_1311976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 92999 ⟨1311976, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 92999
    ⟨1311976, by decide⟩ (by decide) (![⟨1311903, by decide⟩,⟨1311943, by decide⟩,⟨1311975, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_92999_1311976 node_context_11_92999_1311976
  intro a
  fin_cases a
  · exact context_12_371996_1311903
  · exact context_12_371997_1311943
  · exact context_12_371998_1311975
  · exact context_12_371999_757807

theorem unmarked_context_10_23249_1311977 : frontier 11 ⟨1311977, by decide⟩
    (prefixCache 10 23249) (prefixPartial 10 23249) = false := by
  decide +kernel

theorem node_context_10_23249_1311977 : EJMOriginalGlobalDAGData.nodes 11 ⟨1311977, by decide⟩ =
    .split (coordinate 10) (![⟨1311602, by decide⟩,⟨1311701, by decide⟩,⟨1311862, by decide⟩,⟨1311976, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23249_1311977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23249 ⟨1311977, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23249
    ⟨1311977, by decide⟩ (by decide) (![⟨1311602, by decide⟩,⟨1311701, by decide⟩,⟨1311862, by decide⟩,⟨1311976, by decide⟩]) unmarked_context_10_23249_1311977 node_context_10_23249_1311977
  intro a
  fin_cases a
  · exact context_11_92996_1311602
  · exact context_11_92997_1311701
  · exact context_11_92998_1311862
  · exact context_11_92999_1311976

theorem selected_cut_46956 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 372000) = some ⟨12, 1, 0, 435790, 372000, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372000_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372000 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 372000 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 372000, 1, 65536⟩
    (by decide) selected_cut_46956

theorem selected_cut_46957 : selected 9 ⟨1312023, by decide⟩
    (prefixPartial 12 372001) = some ⟨12, 2, 0, 1312023, 372001, 2805, 65536⟩ := by
  decide +kernel

theorem context_12_372001_1312023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372001 ⟨1312023, by decide⟩ :=
  accepted_of_selected 12 372001 ⟨1312023, by decide⟩ ⟨12, 2, 0, 1312023, 372001, 2805, 65536⟩
    (by decide) selected_cut_46957

theorem selected_cut_46958 : selected 9 ⟨1312064, by decide⟩
    (prefixPartial 12 372002) = some ⟨12, 2, 0, 1312064, 372002, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_372002_1312064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372002 ⟨1312064, by decide⟩ :=
  accepted_of_selected 12 372002 ⟨1312064, by decide⟩ ⟨12, 2, 0, 1312064, 372002, 2357, 65536⟩
    (by decide) selected_cut_46958

theorem selected_cut_46959 : selected 9 ⟨1312109, by decide⟩
    (prefixPartial 12 372003) = some ⟨12, 2, 0, 1312109, 372003, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_372003_1312109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372003 ⟨1312109, by decide⟩ :=
  accepted_of_selected 12 372003 ⟨1312109, by decide⟩ ⟨12, 2, 0, 1312109, 372003, 2593, 65536⟩
    (by decide) selected_cut_46959

theorem unmarked_context_11_93000_1312110 : frontier 10 ⟨1312110, by decide⟩
    (prefixCache 11 93000) (prefixPartial 11 93000) = false := by
  decide +kernel

theorem node_context_11_93000_1312110 : EJMOriginalGlobalDAGData.nodes 10 ⟨1312110, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1312023, by decide⟩,⟨1312064, by decide⟩,⟨1312109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93000_1312110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93000 ⟨1312110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93000
    ⟨1312110, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1312023, by decide⟩,⟨1312064, by decide⟩,⟨1312109, by decide⟩]) unmarked_context_11_93000_1312110 node_context_11_93000_1312110
  intro a
  fin_cases a
  · exact context_12_372000_435790
  · exact context_12_372001_1312023
  · exact context_12_372002_1312064
  · exact context_12_372003_1312109

theorem selected_cut_46960 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 372004) = some ⟨12, 1, 0, 450498, 372004, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372004_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372004 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 372004 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 372004, 1, 65536⟩
    (by decide) selected_cut_46960

theorem selected_cut_46961 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 372005) = some ⟨12, 1, 0, 891951, 372005, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372005_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372005 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 372005 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 372005, 1, 65536⟩
    (by decide) selected_cut_46961

theorem selected_cut_46962 : selected 9 ⟨1312169, by decide⟩
    (prefixPartial 12 372006) = some ⟨12, 2, 0, 1312169, 372006, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_372006_1312169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372006 ⟨1312169, by decide⟩ :=
  accepted_of_selected 12 372006 ⟨1312169, by decide⟩ ⟨12, 2, 0, 1312169, 372006, 2761, 65536⟩
    (by decide) selected_cut_46962

theorem selected_cut_46963 : selected 9 ⟨1312240, by decide⟩
    (prefixPartial 12 372007) = some ⟨12, 2, 0, 1312240, 372007, 3025, 65536⟩ := by
  decide +kernel

theorem context_12_372007_1312240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372007 ⟨1312240, by decide⟩ :=
  accepted_of_selected 12 372007 ⟨1312240, by decide⟩ ⟨12, 2, 0, 1312240, 372007, 3025, 65536⟩
    (by decide) selected_cut_46963

theorem unmarked_context_11_93001_1312241 : frontier 10 ⟨1312241, by decide⟩
    (prefixCache 11 93001) (prefixPartial 11 93001) = false := by
  decide +kernel

theorem node_context_11_93001_1312241 : EJMOriginalGlobalDAGData.nodes 10 ⟨1312241, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨891951, by decide⟩,⟨1312169, by decide⟩,⟨1312240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93001_1312241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93001 ⟨1312241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93001
    ⟨1312241, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨891951, by decide⟩,⟨1312169, by decide⟩,⟨1312240, by decide⟩]) unmarked_context_11_93001_1312241 node_context_11_93001_1312241
  intro a
  fin_cases a
  · exact context_12_372004_450498
  · exact context_12_372005_891951
  · exact context_12_372006_1312169
  · exact context_12_372007_1312240

theorem selected_cut_46964 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 372008) = some ⟨12, 1, 0, 435790, 372008, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372008_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372008 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 372008 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 372008, 1, 65536⟩
    (by decide) selected_cut_46964

theorem selected_cut_46965 : selected 9 ⟨1312291, by decide⟩
    (prefixPartial 12 372009) = some ⟨12, 2, 0, 1312291, 372009, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_372009_1312291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372009 ⟨1312291, by decide⟩ :=
  accepted_of_selected 12 372009 ⟨1312291, by decide⟩ ⟨12, 2, 0, 1312291, 372009, 2629, 65536⟩
    (by decide) selected_cut_46965

theorem selected_cut_46966 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 372010) = some ⟨12, 1, 0, 1172910, 372010, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372010_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372010 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 372010 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 372010, 1, 65536⟩
    (by decide) selected_cut_46966

theorem selected_cut_46967 : selected 9 ⟨1312329, by decide⟩
    (prefixPartial 12 372011) = some ⟨12, 2, 0, 1312329, 372011, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_372011_1312329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372011 ⟨1312329, by decide⟩ :=
  accepted_of_selected 12 372011 ⟨1312329, by decide⟩ ⟨12, 2, 0, 1312329, 372011, 2453, 65536⟩
    (by decide) selected_cut_46967

theorem unmarked_context_11_93002_1312330 : frontier 10 ⟨1312330, by decide⟩
    (prefixCache 11 93002) (prefixPartial 11 93002) = false := by
  decide +kernel

theorem node_context_11_93002_1312330 : EJMOriginalGlobalDAGData.nodes 10 ⟨1312330, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1312291, by decide⟩,⟨1172910, by decide⟩,⟨1312329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93002_1312330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93002 ⟨1312330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93002
    ⟨1312330, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1312291, by decide⟩,⟨1172910, by decide⟩,⟨1312329, by decide⟩]) unmarked_context_11_93002_1312330 node_context_11_93002_1312330
  intro a
  fin_cases a
  · exact context_12_372008_435790
  · exact context_12_372009_1312291
  · exact context_12_372010_1172910
  · exact context_12_372011_1312329

theorem selected_cut_46968 : selected 9 ⟨1312378, by decide⟩
    (prefixPartial 12 372012) = some ⟨12, 2, 0, 1312378, 372012, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_372012_1312378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372012 ⟨1312378, by decide⟩ :=
  accepted_of_selected 12 372012 ⟨1312378, by decide⟩ ⟨12, 2, 0, 1312378, 372012, 2325, 65536⟩
    (by decide) selected_cut_46968

theorem selected_cut_46969 : selected 9 ⟨1312417, by decide⟩
    (prefixPartial 12 372013) = some ⟨12, 2, 0, 1312417, 372013, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_372013_1312417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372013 ⟨1312417, by decide⟩ :=
  accepted_of_selected 12 372013 ⟨1312417, by decide⟩ ⟨12, 2, 0, 1312417, 372013, 2481, 65536⟩
    (by decide) selected_cut_46969

theorem selected_cut_46970 : selected 9 ⟨1312448, by decide⟩
    (prefixPartial 12 372014) = some ⟨12, 2, 0, 1312448, 372014, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_372014_1312448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372014 ⟨1312448, by decide⟩ :=
  accepted_of_selected 12 372014 ⟨1312448, by decide⟩ ⟨12, 2, 0, 1312448, 372014, 2077, 65536⟩
    (by decide) selected_cut_46970

theorem selected_cut_46971 : selected 9 ⟨1312510, by decide⟩
    (prefixPartial 12 372015) = some ⟨12, 2, 0, 1312510, 372015, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_372015_1312510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372015 ⟨1312510, by decide⟩ :=
  accepted_of_selected 12 372015 ⟨1312510, by decide⟩ ⟨12, 2, 0, 1312510, 372015, 2737, 65536⟩
    (by decide) selected_cut_46971

theorem unmarked_context_11_93003_1312511 : frontier 10 ⟨1312511, by decide⟩
    (prefixCache 11 93003) (prefixPartial 11 93003) = false := by
  decide +kernel

theorem node_context_11_93003_1312511 : EJMOriginalGlobalDAGData.nodes 10 ⟨1312511, by decide⟩ =
    .split (coordinate 11) (![⟨1312378, by decide⟩,⟨1312417, by decide⟩,⟨1312448, by decide⟩,⟨1312510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93003_1312511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93003 ⟨1312511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93003
    ⟨1312511, by decide⟩ (by decide) (![⟨1312378, by decide⟩,⟨1312417, by decide⟩,⟨1312448, by decide⟩,⟨1312510, by decide⟩]) unmarked_context_11_93003_1312511 node_context_11_93003_1312511
  intro a
  fin_cases a
  · exact context_12_372012_1312378
  · exact context_12_372013_1312417
  · exact context_12_372014_1312448
  · exact context_12_372015_1312510

theorem unmarked_context_10_23250_1312512 : frontier 11 ⟨1312512, by decide⟩
    (prefixCache 10 23250) (prefixPartial 10 23250) = false := by
  decide +kernel

theorem node_context_10_23250_1312512 : EJMOriginalGlobalDAGData.nodes 11 ⟨1312512, by decide⟩ =
    .split (coordinate 10) (![⟨1312110, by decide⟩,⟨1312241, by decide⟩,⟨1312330, by decide⟩,⟨1312511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23250_1312512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23250 ⟨1312512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23250
    ⟨1312512, by decide⟩ (by decide) (![⟨1312110, by decide⟩,⟨1312241, by decide⟩,⟨1312330, by decide⟩,⟨1312511, by decide⟩]) unmarked_context_10_23250_1312512 node_context_10_23250_1312512
  intro a
  fin_cases a
  · exact context_11_93000_1312110
  · exact context_11_93001_1312241
  · exact context_11_93002_1312330
  · exact context_11_93003_1312511

theorem selected_cut_46972 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 372016) = some ⟨12, 1, 0, 1255011, 372016, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372016_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372016 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 372016 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 372016, 1, 65536⟩
    (by decide) selected_cut_46972

theorem selected_cut_46973 : selected 9 ⟨1312540, by decide⟩
    (prefixPartial 12 372017) = some ⟨12, 2, 0, 1312540, 372017, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_372017_1312540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372017 ⟨1312540, by decide⟩ :=
  accepted_of_selected 12 372017 ⟨1312540, by decide⟩ ⟨12, 2, 0, 1312540, 372017, 2041, 65536⟩
    (by decide) selected_cut_46973

theorem selected_cut_46974 : selected 9 ⟨1312568, by decide⟩
    (prefixPartial 12 372018) = some ⟨12, 2, 0, 1312568, 372018, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_372018_1312568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372018 ⟨1312568, by decide⟩ :=
  accepted_of_selected 12 372018 ⟨1312568, by decide⟩ ⟨12, 2, 0, 1312568, 372018, 1749, 65536⟩
    (by decide) selected_cut_46974

theorem selected_cut_46975 : selected 9 ⟨1312597, by decide⟩
    (prefixPartial 12 372019) = some ⟨12, 2, 0, 1312597, 372019, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_372019_1312597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372019 ⟨1312597, by decide⟩ :=
  accepted_of_selected 12 372019 ⟨1312597, by decide⟩ ⟨12, 2, 0, 1312597, 372019, 2081, 65536⟩
    (by decide) selected_cut_46975

theorem unmarked_context_11_93004_1312598 : frontier 10 ⟨1312598, by decide⟩
    (prefixCache 11 93004) (prefixPartial 11 93004) = false := by
  decide +kernel

theorem node_context_11_93004_1312598 : EJMOriginalGlobalDAGData.nodes 10 ⟨1312598, by decide⟩ =
    .split (coordinate 11) (![⟨1255011, by decide⟩,⟨1312540, by decide⟩,⟨1312568, by decide⟩,⟨1312597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93004_1312598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93004 ⟨1312598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93004
    ⟨1312598, by decide⟩ (by decide) (![⟨1255011, by decide⟩,⟨1312540, by decide⟩,⟨1312568, by decide⟩,⟨1312597, by decide⟩]) unmarked_context_11_93004_1312598 node_context_11_93004_1312598
  intro a
  fin_cases a
  · exact context_12_372016_1255011
  · exact context_12_372017_1312540
  · exact context_12_372018_1312568
  · exact context_12_372019_1312597

theorem selected_cut_46976 : selected 9 ⟨1312636, by decide⟩
    (prefixPartial 12 372020) = some ⟨12, 2, 0, 1312636, 372020, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_372020_1312636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372020 ⟨1312636, by decide⟩ :=
  accepted_of_selected 12 372020 ⟨1312636, by decide⟩ ⟨12, 2, 0, 1312636, 372020, 2197, 65536⟩
    (by decide) selected_cut_46976

theorem selected_cut_46977 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 372021) = some ⟨12, 1, 0, 891951, 372021, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372021_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372021 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 372021 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 372021, 1, 65536⟩
    (by decide) selected_cut_46977

theorem selected_cut_46978 : selected 9 ⟨1312665, by decide⟩
    (prefixPartial 12 372022) = some ⟨12, 2, 0, 1312665, 372022, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_372022_1312665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372022 ⟨1312665, by decide⟩ :=
  accepted_of_selected 12 372022 ⟨1312665, by decide⟩ ⟨12, 2, 0, 1312665, 372022, 1789, 65536⟩
    (by decide) selected_cut_46978

theorem selected_cut_46979 : selected 9 ⟨1312702, by decide⟩
    (prefixPartial 12 372023) = some ⟨12, 2, 0, 1312702, 372023, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_372023_1312702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372023 ⟨1312702, by decide⟩ :=
  accepted_of_selected 12 372023 ⟨1312702, by decide⟩ ⟨12, 2, 0, 1312702, 372023, 2125, 65536⟩
    (by decide) selected_cut_46979

theorem unmarked_context_11_93005_1312703 : frontier 10 ⟨1312703, by decide⟩
    (prefixCache 11 93005) (prefixPartial 11 93005) = false := by
  decide +kernel

theorem node_context_11_93005_1312703 : EJMOriginalGlobalDAGData.nodes 10 ⟨1312703, by decide⟩ =
    .split (coordinate 11) (![⟨1312636, by decide⟩,⟨891951, by decide⟩,⟨1312665, by decide⟩,⟨1312702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93005_1312703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93005 ⟨1312703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93005
    ⟨1312703, by decide⟩ (by decide) (![⟨1312636, by decide⟩,⟨891951, by decide⟩,⟨1312665, by decide⟩,⟨1312702, by decide⟩]) unmarked_context_11_93005_1312703 node_context_11_93005_1312703
  intro a
  fin_cases a
  · exact context_12_372020_1312636
  · exact context_12_372021_891951
  · exact context_12_372022_1312665
  · exact context_12_372023_1312702

theorem selected_cut_46980 : selected 9 ⟨1312731, by decide⟩
    (prefixPartial 12 372024) = some ⟨12, 2, 0, 1312731, 372024, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_372024_1312731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372024 ⟨1312731, by decide⟩ :=
  accepted_of_selected 12 372024 ⟨1312731, by decide⟩ ⟨12, 2, 0, 1312731, 372024, 1669, 65536⟩
    (by decide) selected_cut_46980

theorem selected_cut_46981 : selected 9 ⟨1312757, by decide⟩
    (prefixPartial 12 372025) = some ⟨12, 2, 0, 1312757, 372025, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_372025_1312757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372025 ⟨1312757, by decide⟩ :=
  accepted_of_selected 12 372025 ⟨1312757, by decide⟩ ⟨12, 2, 0, 1312757, 372025, 1857, 65536⟩
    (by decide) selected_cut_46981

theorem selected_cut_46982 : selected 9 ⟨1312788, by decide⟩
    (prefixPartial 12 372026) = some ⟨12, 2, 0, 1312788, 372026, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_372026_1312788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372026 ⟨1312788, by decide⟩ :=
  accepted_of_selected 12 372026 ⟨1312788, by decide⟩ ⟨12, 2, 0, 1312788, 372026, 1597, 65536⟩
    (by decide) selected_cut_46982

theorem selected_cut_46983 : selected 9 ⟨1312818, by decide⟩
    (prefixPartial 12 372027) = some ⟨12, 2, 0, 1312818, 372027, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_372027_1312818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372027 ⟨1312818, by decide⟩ :=
  accepted_of_selected 12 372027 ⟨1312818, by decide⟩ ⟨12, 2, 0, 1312818, 372027, 1877, 65536⟩
    (by decide) selected_cut_46983

theorem unmarked_context_11_93006_1312819 : frontier 10 ⟨1312819, by decide⟩
    (prefixCache 11 93006) (prefixPartial 11 93006) = false := by
  decide +kernel

theorem node_context_11_93006_1312819 : EJMOriginalGlobalDAGData.nodes 10 ⟨1312819, by decide⟩ =
    .split (coordinate 11) (![⟨1312731, by decide⟩,⟨1312757, by decide⟩,⟨1312788, by decide⟩,⟨1312818, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93006_1312819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93006 ⟨1312819, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93006
    ⟨1312819, by decide⟩ (by decide) (![⟨1312731, by decide⟩,⟨1312757, by decide⟩,⟨1312788, by decide⟩,⟨1312818, by decide⟩]) unmarked_context_11_93006_1312819 node_context_11_93006_1312819
  intro a
  fin_cases a
  · exact context_12_372024_1312731
  · exact context_12_372025_1312757
  · exact context_12_372026_1312788
  · exact context_12_372027_1312818

theorem selected_cut_46984 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 93007) = some ⟨11, 1, 0, 977886, 93007, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93007_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93007 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 93007 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 93007, 1, 262144⟩
    (by decide) selected_cut_46984

theorem unmarked_context_10_23251_1312820 : frontier 11 ⟨1312820, by decide⟩
    (prefixCache 10 23251) (prefixPartial 10 23251) = false := by
  decide +kernel

theorem node_context_10_23251_1312820 : EJMOriginalGlobalDAGData.nodes 11 ⟨1312820, by decide⟩ =
    .split (coordinate 10) (![⟨1312598, by decide⟩,⟨1312703, by decide⟩,⟨1312819, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23251_1312820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23251 ⟨1312820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23251
    ⟨1312820, by decide⟩ (by decide) (![⟨1312598, by decide⟩,⟨1312703, by decide⟩,⟨1312819, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23251_1312820 node_context_10_23251_1312820
  intro a
  fin_cases a
  · exact context_11_93004_1312598
  · exact context_11_93005_1312703
  · exact context_11_93006_1312819
  · exact context_11_93007_977886

theorem unmarked_context_9_5812_1312821 : frontier 12 ⟨1312821, by decide⟩
    (prefixCache 9 5812) (prefixPartial 9 5812) = false := by
  decide +kernel

theorem node_context_9_5812_1312821 : EJMOriginalGlobalDAGData.nodes 12 ⟨1312821, by decide⟩ =
    .split (coordinate 9) (![⟨1311446, by decide⟩,⟨1311977, by decide⟩,⟨1312512, by decide⟩,⟨1312820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5812_1312821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5812 ⟨1312821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5812
    ⟨1312821, by decide⟩ (by decide) (![⟨1311446, by decide⟩,⟨1311977, by decide⟩,⟨1312512, by decide⟩,⟨1312820, by decide⟩]) unmarked_context_9_5812_1312821 node_context_9_5812_1312821
  intro a
  fin_cases a
  · exact context_10_23248_1311446
  · exact context_10_23249_1311977
  · exact context_10_23250_1312512
  · exact context_10_23251_1312820

theorem selected_cut_46985 : selected 10 ⟨1312877, by decide⟩
    (prefixPartial 11 93008) = some ⟨11, 2, 0, 1312877, 93008, 2985, 262144⟩ := by
  decide +kernel

theorem context_11_93008_1312877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93008 ⟨1312877, by decide⟩ :=
  accepted_of_selected 11 93008 ⟨1312877, by decide⟩ ⟨11, 2, 0, 1312877, 93008, 2985, 262144⟩
    (by decide) selected_cut_46985

theorem selected_cut_46986 : selected 9 ⟨1312913, by decide⟩
    (prefixPartial 12 372036) = some ⟨12, 2, 0, 1312913, 372036, 1733, 65536⟩ := by
  decide +kernel

theorem context_12_372036_1312913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372036 ⟨1312913, by decide⟩ :=
  accepted_of_selected 12 372036 ⟨1312913, by decide⟩ ⟨12, 2, 0, 1312913, 372036, 1733, 65536⟩
    (by decide) selected_cut_46986

theorem selected_cut_46987 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 372037) = some ⟨12, 1, 0, 891951, 372037, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372037_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372037 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 372037 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 372037, 1, 65536⟩
    (by decide) selected_cut_46987

theorem selected_cut_46988 : selected 9 ⟨1312944, by decide⟩
    (prefixPartial 12 372038) = some ⟨12, 2, 0, 1312944, 372038, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_372038_1312944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372038 ⟨1312944, by decide⟩ :=
  accepted_of_selected 12 372038 ⟨1312944, by decide⟩ ⟨12, 2, 0, 1312944, 372038, 1545, 65536⟩
    (by decide) selected_cut_46988

theorem selected_cut_46989 : selected 9 ⟨1312972, by decide⟩
    (prefixPartial 12 372039) = some ⟨12, 2, 0, 1312972, 372039, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_372039_1312972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372039 ⟨1312972, by decide⟩ :=
  accepted_of_selected 12 372039 ⟨1312972, by decide⟩ ⟨12, 2, 0, 1312972, 372039, 1585, 65536⟩
    (by decide) selected_cut_46989

theorem unmarked_context_11_93009_1312973 : frontier 10 ⟨1312973, by decide⟩
    (prefixCache 11 93009) (prefixPartial 11 93009) = false := by
  decide +kernel

theorem node_context_11_93009_1312973 : EJMOriginalGlobalDAGData.nodes 10 ⟨1312973, by decide⟩ =
    .split (coordinate 11) (![⟨1312913, by decide⟩,⟨891951, by decide⟩,⟨1312944, by decide⟩,⟨1312972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93009_1312973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93009 ⟨1312973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93009
    ⟨1312973, by decide⟩ (by decide) (![⟨1312913, by decide⟩,⟨891951, by decide⟩,⟨1312944, by decide⟩,⟨1312972, by decide⟩]) unmarked_context_11_93009_1312973 node_context_11_93009_1312973
  intro a
  fin_cases a
  · exact context_12_372036_1312913
  · exact context_12_372037_891951
  · exact context_12_372038_1312944
  · exact context_12_372039_1312972

theorem selected_cut_46990 : selected 10 ⟨1313031, by decide⟩
    (prefixPartial 11 93010) = some ⟨11, 2, 0, 1313031, 93010, 3009, 262144⟩ := by
  decide +kernel

theorem context_11_93010_1313031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93010 ⟨1313031, by decide⟩ :=
  accepted_of_selected 11 93010 ⟨1313031, by decide⟩ ⟨11, 2, 0, 1313031, 93010, 3009, 262144⟩
    (by decide) selected_cut_46990

theorem selected_cut_46991 : selected 9 ⟨1313050, by decide⟩
    (prefixPartial 12 372044) = some ⟨12, 2, 0, 1313050, 372044, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_372044_1313050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372044 ⟨1313050, by decide⟩ :=
  accepted_of_selected 12 372044 ⟨1313050, by decide⟩ ⟨12, 2, 0, 1313050, 372044, 1321, 65536⟩
    (by decide) selected_cut_46991

theorem selected_cut_46992 : selected 9 ⟨1313072, by decide⟩
    (prefixPartial 12 372045) = some ⟨12, 2, 0, 1313072, 372045, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_372045_1313072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372045 ⟨1313072, by decide⟩ :=
  accepted_of_selected 12 372045 ⟨1313072, by decide⟩ ⟨12, 2, 0, 1313072, 372045, 1289, 65536⟩
    (by decide) selected_cut_46992

theorem selected_cut_46993 : selected 9 ⟨1313089, by decide⟩
    (prefixPartial 12 372046) = some ⟨12, 2, 0, 1313089, 372046, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_372046_1313089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372046 ⟨1313089, by decide⟩ :=
  accepted_of_selected 12 372046 ⟨1313089, by decide⟩ ⟨12, 2, 0, 1313089, 372046, 1253, 65536⟩
    (by decide) selected_cut_46993

theorem selected_cut_46994 : selected 9 ⟨1313115, by decide⟩
    (prefixPartial 12 372047) = some ⟨12, 2, 0, 1313115, 372047, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_372047_1313115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372047 ⟨1313115, by decide⟩ :=
  accepted_of_selected 12 372047 ⟨1313115, by decide⟩ ⟨12, 2, 0, 1313115, 372047, 1437, 65536⟩
    (by decide) selected_cut_46994

theorem unmarked_context_11_93011_1313116 : frontier 10 ⟨1313116, by decide⟩
    (prefixCache 11 93011) (prefixPartial 11 93011) = false := by
  decide +kernel

theorem node_context_11_93011_1313116 : EJMOriginalGlobalDAGData.nodes 10 ⟨1313116, by decide⟩ =
    .split (coordinate 11) (![⟨1313050, by decide⟩,⟨1313072, by decide⟩,⟨1313089, by decide⟩,⟨1313115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93011_1313116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93011 ⟨1313116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93011
    ⟨1313116, by decide⟩ (by decide) (![⟨1313050, by decide⟩,⟨1313072, by decide⟩,⟨1313089, by decide⟩,⟨1313115, by decide⟩]) unmarked_context_11_93011_1313116 node_context_11_93011_1313116
  intro a
  fin_cases a
  · exact context_12_372044_1313050
  · exact context_12_372045_1313072
  · exact context_12_372046_1313089
  · exact context_12_372047_1313115

theorem unmarked_context_10_23252_1313117 : frontier 11 ⟨1313117, by decide⟩
    (prefixCache 10 23252) (prefixPartial 10 23252) = false := by
  decide +kernel

theorem node_context_10_23252_1313117 : EJMOriginalGlobalDAGData.nodes 11 ⟨1313117, by decide⟩ =
    .split (coordinate 10) (![⟨1312877, by decide⟩,⟨1312973, by decide⟩,⟨1313031, by decide⟩,⟨1313116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23252_1313117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23252 ⟨1313117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23252
    ⟨1313117, by decide⟩ (by decide) (![⟨1312877, by decide⟩,⟨1312973, by decide⟩,⟨1313031, by decide⟩,⟨1313116, by decide⟩]) unmarked_context_10_23252_1313117 node_context_10_23252_1313117
  intro a
  fin_cases a
  · exact context_11_93008_1312877
  · exact context_11_93009_1312973
  · exact context_11_93010_1313031
  · exact context_11_93011_1313116

theorem selected_cut_46995 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23253) = some ⟨10, 1, 0, 893098, 23253, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23253_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23253 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23253 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23253, 1, 1048576⟩
    (by decide) selected_cut_46995

theorem selected_cut_46996 : selected 10 ⟨1313196, by decide⟩
    (prefixPartial 11 93016) = some ⟨11, 2, 0, 1313196, 93016, 3245, 262144⟩ := by
  decide +kernel

theorem context_11_93016_1313196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93016 ⟨1313196, by decide⟩ :=
  accepted_of_selected 11 93016 ⟨1313196, by decide⟩ ⟨11, 2, 0, 1313196, 93016, 3245, 262144⟩
    (by decide) selected_cut_46996

theorem selected_cut_46997 : selected 9 ⟨1313227, by decide⟩
    (prefixPartial 12 372068) = some ⟨12, 2, 0, 1313227, 372068, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_372068_1313227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372068 ⟨1313227, by decide⟩ :=
  accepted_of_selected 12 372068 ⟨1313227, by decide⟩ ⟨12, 2, 0, 1313227, 372068, 1529, 65536⟩
    (by decide) selected_cut_46997

theorem selected_cut_46998 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 372069) = some ⟨12, 1, 0, 1256866, 372069, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372069_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372069 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 372069 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 372069, 1, 65536⟩
    (by decide) selected_cut_46998

theorem selected_cut_46999 : selected 9 ⟨1313249, by decide⟩
    (prefixPartial 12 372070) = some ⟨12, 2, 0, 1313249, 372070, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_372070_1313249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372070 ⟨1313249, by decide⟩ :=
  accepted_of_selected 12 372070 ⟨1313249, by decide⟩ ⟨12, 2, 0, 1313249, 372070, 1269, 65536⟩
    (by decide) selected_cut_46999

theorem selected_cut_47000 : selected 9 ⟨1313278, by decide⟩
    (prefixPartial 12 372071) = some ⟨12, 2, 0, 1313278, 372071, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_372071_1313278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372071 ⟨1313278, by decide⟩ :=
  accepted_of_selected 12 372071 ⟨1313278, by decide⟩ ⟨12, 2, 0, 1313278, 372071, 1309, 65536⟩
    (by decide) selected_cut_47000

theorem unmarked_context_11_93017_1313279 : frontier 10 ⟨1313279, by decide⟩
    (prefixCache 11 93017) (prefixPartial 11 93017) = false := by
  decide +kernel

theorem node_context_11_93017_1313279 : EJMOriginalGlobalDAGData.nodes 10 ⟨1313279, by decide⟩ =
    .split (coordinate 11) (![⟨1313227, by decide⟩,⟨1256866, by decide⟩,⟨1313249, by decide⟩,⟨1313278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93017_1313279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93017 ⟨1313279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93017
    ⟨1313279, by decide⟩ (by decide) (![⟨1313227, by decide⟩,⟨1256866, by decide⟩,⟨1313249, by decide⟩,⟨1313278, by decide⟩]) unmarked_context_11_93017_1313279 node_context_11_93017_1313279
  intro a
  fin_cases a
  · exact context_12_372068_1313227
  · exact context_12_372069_1256866
  · exact context_12_372070_1313249
  · exact context_12_372071_1313278

theorem selected_cut_47001 : selected 10 ⟨1313298, by decide⟩
    (prefixPartial 11 93018) = some ⟨11, 2, 0, 1313298, 93018, 1141, 262144⟩ := by
  decide +kernel

theorem context_11_93018_1313298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93018 ⟨1313298, by decide⟩ :=
  accepted_of_selected 11 93018 ⟨1313298, by decide⟩ ⟨11, 2, 0, 1313298, 93018, 1141, 262144⟩
    (by decide) selected_cut_47001

theorem selected_cut_47002 : selected 10 ⟨1313328, by decide⟩
    (prefixPartial 11 93019) = some ⟨11, 2, 0, 1313328, 93019, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_93019_1313328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93019 ⟨1313328, by decide⟩ :=
  accepted_of_selected 11 93019 ⟨1313328, by decide⟩ ⟨11, 2, 0, 1313328, 93019, 2329, 262144⟩
    (by decide) selected_cut_47002

theorem unmarked_context_10_23254_1313329 : frontier 11 ⟨1313329, by decide⟩
    (prefixCache 10 23254) (prefixPartial 10 23254) = false := by
  decide +kernel

theorem node_context_10_23254_1313329 : EJMOriginalGlobalDAGData.nodes 11 ⟨1313329, by decide⟩ =
    .split (coordinate 10) (![⟨1313196, by decide⟩,⟨1313279, by decide⟩,⟨1313298, by decide⟩,⟨1313328, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23254_1313329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23254 ⟨1313329, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23254
    ⟨1313329, by decide⟩ (by decide) (![⟨1313196, by decide⟩,⟨1313279, by decide⟩,⟨1313298, by decide⟩,⟨1313328, by decide⟩]) unmarked_context_10_23254_1313329 node_context_10_23254_1313329
  intro a
  fin_cases a
  · exact context_11_93016_1313196
  · exact context_11_93017_1313279
  · exact context_11_93018_1313298
  · exact context_11_93019_1313328

theorem selected_cut_47003 : selected 9 ⟨1313349, by decide⟩
    (prefixPartial 12 372080) = some ⟨12, 2, 0, 1313349, 372080, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_372080_1313349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372080 ⟨1313349, by decide⟩ :=
  accepted_of_selected 12 372080 ⟨1313349, by decide⟩ ⟨12, 2, 0, 1313349, 372080, 1161, 65536⟩
    (by decide) selected_cut_47003

theorem selected_cut_47004 : selected 9 ⟨1313366, by decide⟩
    (prefixPartial 12 372081) = some ⟨12, 2, 0, 1313366, 372081, 1025, 65536⟩ := by
  decide +kernel

theorem context_12_372081_1313366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372081 ⟨1313366, by decide⟩ :=
  accepted_of_selected 12 372081 ⟨1313366, by decide⟩ ⟨12, 2, 0, 1313366, 372081, 1025, 65536⟩
    (by decide) selected_cut_47004

theorem selected_cut_47005 : selected 9 ⟨1313381, by decide⟩
    (prefixPartial 12 372082) = some ⟨12, 2, 0, 1313381, 372082, 953, 65536⟩ := by
  decide +kernel

theorem context_12_372082_1313381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372082 ⟨1313381, by decide⟩ :=
  accepted_of_selected 12 372082 ⟨1313381, by decide⟩ ⟨12, 2, 0, 1313381, 372082, 953, 65536⟩
    (by decide) selected_cut_47005

theorem selected_cut_47006 : selected 9 ⟨1313397, by decide⟩
    (prefixPartial 12 372083) = some ⟨12, 2, 0, 1313397, 372083, 1069, 65536⟩ := by
  decide +kernel

theorem context_12_372083_1313397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372083 ⟨1313397, by decide⟩ :=
  accepted_of_selected 12 372083 ⟨1313397, by decide⟩ ⟨12, 2, 0, 1313397, 372083, 1069, 65536⟩
    (by decide) selected_cut_47006

theorem unmarked_context_11_93020_1313398 : frontier 10 ⟨1313398, by decide⟩
    (prefixCache 11 93020) (prefixPartial 11 93020) = false := by
  decide +kernel

theorem node_context_11_93020_1313398 : EJMOriginalGlobalDAGData.nodes 10 ⟨1313398, by decide⟩ =
    .split (coordinate 11) (![⟨1313349, by decide⟩,⟨1313366, by decide⟩,⟨1313381, by decide⟩,⟨1313397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93020_1313398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93020 ⟨1313398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93020
    ⟨1313398, by decide⟩ (by decide) (![⟨1313349, by decide⟩,⟨1313366, by decide⟩,⟨1313381, by decide⟩,⟨1313397, by decide⟩]) unmarked_context_11_93020_1313398 node_context_11_93020_1313398
  intro a
  fin_cases a
  · exact context_12_372080_1313349
  · exact context_12_372081_1313366
  · exact context_12_372082_1313381
  · exact context_12_372083_1313397

theorem selected_cut_47007 : selected 10 ⟨1313463, by decide⟩
    (prefixPartial 11 93021) = some ⟨11, 2, 0, 1313463, 93021, 2937, 262144⟩ := by
  decide +kernel

theorem context_11_93021_1313463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93021 ⟨1313463, by decide⟩ :=
  accepted_of_selected 11 93021 ⟨1313463, by decide⟩ ⟨11, 2, 0, 1313463, 93021, 2937, 262144⟩
    (by decide) selected_cut_47007

theorem selected_cut_47008 : selected 10 ⟨1313495, by decide⟩
    (prefixPartial 11 93022) = some ⟨11, 2, 0, 1313495, 93022, 1793, 262144⟩ := by
  decide +kernel

theorem context_11_93022_1313495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93022 ⟨1313495, by decide⟩ :=
  accepted_of_selected 11 93022 ⟨1313495, by decide⟩ ⟨11, 2, 0, 1313495, 93022, 1793, 262144⟩
    (by decide) selected_cut_47008

theorem selected_cut_47009 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 93023) = some ⟨11, 1, 0, 977886, 93023, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93023_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93023 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 93023 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 93023, 1, 262144⟩
    (by decide) selected_cut_47009

theorem unmarked_context_10_23255_1313496 : frontier 11 ⟨1313496, by decide⟩
    (prefixCache 10 23255) (prefixPartial 10 23255) = false := by
  decide +kernel

theorem node_context_10_23255_1313496 : EJMOriginalGlobalDAGData.nodes 11 ⟨1313496, by decide⟩ =
    .split (coordinate 10) (![⟨1313398, by decide⟩,⟨1313463, by decide⟩,⟨1313495, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23255_1313496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23255 ⟨1313496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23255
    ⟨1313496, by decide⟩ (by decide) (![⟨1313398, by decide⟩,⟨1313463, by decide⟩,⟨1313495, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23255_1313496 node_context_10_23255_1313496
  intro a
  fin_cases a
  · exact context_11_93020_1313398
  · exact context_11_93021_1313463
  · exact context_11_93022_1313495
  · exact context_11_93023_977886

theorem unmarked_context_9_5813_1313497 : frontier 12 ⟨1313497, by decide⟩
    (prefixCache 9 5813) (prefixPartial 9 5813) = false := by
  decide +kernel

theorem node_context_9_5813_1313497 : EJMOriginalGlobalDAGData.nodes 12 ⟨1313497, by decide⟩ =
    .split (coordinate 9) (![⟨1313117, by decide⟩,⟨893098, by decide⟩,⟨1313329, by decide⟩,⟨1313496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5813_1313497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5813 ⟨1313497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5813
    ⟨1313497, by decide⟩ (by decide) (![⟨1313117, by decide⟩,⟨893098, by decide⟩,⟨1313329, by decide⟩,⟨1313496, by decide⟩]) unmarked_context_9_5813_1313497 node_context_9_5813_1313497
  intro a
  fin_cases a
  · exact context_10_23252_1313117
  · exact context_10_23253_893098
  · exact context_10_23254_1313329
  · exact context_10_23255_1313496

theorem selected_cut_47010 : selected 10 ⟨1313541, by decide⟩
    (prefixPartial 11 93024) = some ⟨11, 2, 0, 1313541, 93024, 2341, 262144⟩ := by
  decide +kernel

theorem context_11_93024_1313541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93024 ⟨1313541, by decide⟩ :=
  accepted_of_selected 11 93024 ⟨1313541, by decide⟩ ⟨11, 2, 0, 1313541, 93024, 2341, 262144⟩
    (by decide) selected_cut_47010

theorem selected_cut_47011 : selected 10 ⟨1313601, by decide⟩
    (prefixPartial 11 93025) = some ⟨11, 2, 0, 1313601, 93025, 2605, 262144⟩ := by
  decide +kernel

theorem context_11_93025_1313601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93025 ⟨1313601, by decide⟩ :=
  accepted_of_selected 11 93025 ⟨1313601, by decide⟩ ⟨11, 2, 0, 1313601, 93025, 2605, 262144⟩
    (by decide) selected_cut_47011

theorem selected_cut_47012 : selected 10 ⟨1313662, by decide⟩
    (prefixPartial 11 93026) = some ⟨11, 2, 0, 1313662, 93026, 3305, 262144⟩ := by
  decide +kernel

theorem context_11_93026_1313662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93026 ⟨1313662, by decide⟩ :=
  accepted_of_selected 11 93026 ⟨1313662, by decide⟩ ⟨11, 2, 0, 1313662, 93026, 3305, 262144⟩
    (by decide) selected_cut_47012

theorem selected_cut_47013 : selected 10 ⟨1313737, by decide⟩
    (prefixPartial 11 93027) = some ⟨11, 2, 0, 1313737, 93027, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_93027_1313737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93027 ⟨1313737, by decide⟩ :=
  accepted_of_selected 11 93027 ⟨1313737, by decide⟩ ⟨11, 2, 0, 1313737, 93027, 3169, 262144⟩
    (by decide) selected_cut_47013

theorem unmarked_context_10_23256_1313738 : frontier 11 ⟨1313738, by decide⟩
    (prefixCache 10 23256) (prefixPartial 10 23256) = false := by
  decide +kernel

theorem node_context_10_23256_1313738 : EJMOriginalGlobalDAGData.nodes 11 ⟨1313738, by decide⟩ =
    .split (coordinate 10) (![⟨1313541, by decide⟩,⟨1313601, by decide⟩,⟨1313662, by decide⟩,⟨1313737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23256_1313738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23256 ⟨1313738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23256
    ⟨1313738, by decide⟩ (by decide) (![⟨1313541, by decide⟩,⟨1313601, by decide⟩,⟨1313662, by decide⟩,⟨1313737, by decide⟩]) unmarked_context_10_23256_1313738 node_context_10_23256_1313738
  intro a
  fin_cases a
  · exact context_11_93024_1313541
  · exact context_11_93025_1313601
  · exact context_11_93026_1313662
  · exact context_11_93027_1313737

theorem selected_cut_47014 : selected 10 ⟨1313781, by decide⟩
    (prefixPartial 11 93028) = some ⟨11, 2, 0, 1313781, 93028, 2649, 262144⟩ := by
  decide +kernel

theorem context_11_93028_1313781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93028 ⟨1313781, by decide⟩ :=
  accepted_of_selected 11 93028 ⟨1313781, by decide⟩ ⟨11, 2, 0, 1313781, 93028, 2649, 262144⟩
    (by decide) selected_cut_47014

theorem selected_cut_47015 : selected 10 ⟨1313793, by decide⟩
    (prefixPartial 11 93029) = some ⟨11, 2, 0, 1313793, 93029, 897, 262144⟩ := by
  decide +kernel

theorem context_11_93029_1313793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93029 ⟨1313793, by decide⟩ :=
  accepted_of_selected 11 93029 ⟨1313793, by decide⟩ ⟨11, 2, 0, 1313793, 93029, 897, 262144⟩
    (by decide) selected_cut_47015

theorem selected_cut_47016 : selected 10 ⟨1313825, by decide⟩
    (prefixPartial 11 93030) = some ⟨11, 2, 0, 1313825, 93030, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_93030_1313825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93030 ⟨1313825, by decide⟩ :=
  accepted_of_selected 11 93030 ⟨1313825, by decide⟩ ⟨11, 2, 0, 1313825, 93030, 2125, 262144⟩
    (by decide) selected_cut_47016

theorem selected_cut_47017 : selected 10 ⟨1313849, by decide⟩
    (prefixPartial 11 93031) = some ⟨11, 2, 0, 1313849, 93031, 1349, 262144⟩ := by
  decide +kernel

theorem context_11_93031_1313849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93031 ⟨1313849, by decide⟩ :=
  accepted_of_selected 11 93031 ⟨1313849, by decide⟩ ⟨11, 2, 0, 1313849, 93031, 1349, 262144⟩
    (by decide) selected_cut_47017

theorem unmarked_context_10_23257_1313850 : frontier 11 ⟨1313850, by decide⟩
    (prefixCache 10 23257) (prefixPartial 10 23257) = false := by
  decide +kernel

theorem node_context_10_23257_1313850 : EJMOriginalGlobalDAGData.nodes 11 ⟨1313850, by decide⟩ =
    .split (coordinate 10) (![⟨1313781, by decide⟩,⟨1313793, by decide⟩,⟨1313825, by decide⟩,⟨1313849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23257_1313850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23257 ⟨1313850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23257
    ⟨1313850, by decide⟩ (by decide) (![⟨1313781, by decide⟩,⟨1313793, by decide⟩,⟨1313825, by decide⟩,⟨1313849, by decide⟩]) unmarked_context_10_23257_1313850 node_context_10_23257_1313850
  intro a
  fin_cases a
  · exact context_11_93028_1313781
  · exact context_11_93029_1313793
  · exact context_11_93030_1313825
  · exact context_11_93031_1313849

theorem selected_cut_47018 : selected 11 ⟨1313939, by decide⟩
    (prefixPartial 10 23258) = some ⟨10, 2, 0, 1313939, 23258, 3709, 1048576⟩ := by
  decide +kernel

theorem context_10_23258_1313939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23258 ⟨1313939, by decide⟩ :=
  accepted_of_selected 10 23258 ⟨1313939, by decide⟩ ⟨10, 2, 0, 1313939, 23258, 3709, 1048576⟩
    (by decide) selected_cut_47018

theorem selected_cut_47019 : selected 11 ⟨1314003, by decide⟩
    (prefixPartial 10 23259) = some ⟨10, 2, 0, 1314003, 23259, 3433, 1048576⟩ := by
  decide +kernel

theorem context_10_23259_1314003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23259 ⟨1314003, by decide⟩ :=
  accepted_of_selected 10 23259 ⟨1314003, by decide⟩ ⟨10, 2, 0, 1314003, 23259, 3433, 1048576⟩
    (by decide) selected_cut_47019

theorem unmarked_context_9_5814_1314004 : frontier 12 ⟨1314004, by decide⟩
    (prefixCache 9 5814) (prefixPartial 9 5814) = false := by
  decide +kernel

theorem node_context_9_5814_1314004 : EJMOriginalGlobalDAGData.nodes 12 ⟨1314004, by decide⟩ =
    .split (coordinate 9) (![⟨1313738, by decide⟩,⟨1313850, by decide⟩,⟨1313939, by decide⟩,⟨1314003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5814_1314004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5814 ⟨1314004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5814
    ⟨1314004, by decide⟩ (by decide) (![⟨1313738, by decide⟩,⟨1313850, by decide⟩,⟨1313939, by decide⟩,⟨1314003, by decide⟩]) unmarked_context_9_5814_1314004 node_context_9_5814_1314004
  intro a
  fin_cases a
  · exact context_10_23256_1313738
  · exact context_10_23257_1313850
  · exact context_10_23258_1313939
  · exact context_10_23259_1314003

theorem selected_cut_47020 : selected 11 ⟨1314072, by decide⟩
    (prefixPartial 10 23260) = some ⟨10, 2, 0, 1314072, 23260, 3873, 1048576⟩ := by
  decide +kernel

theorem context_10_23260_1314072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23260 ⟨1314072, by decide⟩ :=
  accepted_of_selected 10 23260 ⟨1314072, by decide⟩ ⟨10, 2, 0, 1314072, 23260, 3873, 1048576⟩
    (by decide) selected_cut_47020

theorem selected_cut_47021 : selected 11 ⟨1314114, by decide⟩
    (prefixPartial 10 23261) = some ⟨10, 2, 0, 1314114, 23261, 1693, 1048576⟩ := by
  decide +kernel

theorem context_10_23261_1314114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23261 ⟨1314114, by decide⟩ :=
  accepted_of_selected 10 23261 ⟨1314114, by decide⟩ ⟨10, 2, 0, 1314114, 23261, 1693, 1048576⟩
    (by decide) selected_cut_47021

theorem selected_cut_47022 : selected 11 ⟨1314153, by decide⟩
    (prefixPartial 10 23262) = some ⟨10, 2, 0, 1314153, 23262, 1337, 1048576⟩ := by
  decide +kernel

theorem context_10_23262_1314153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23262 ⟨1314153, by decide⟩ :=
  accepted_of_selected 10 23262 ⟨1314153, by decide⟩ ⟨10, 2, 0, 1314153, 23262, 1337, 1048576⟩
    (by decide) selected_cut_47022

theorem selected_cut_47023 : selected 11 ⟨1314161, by decide⟩
    (prefixPartial 10 23263) = some ⟨10, 2, 0, 1314161, 23263, 189, 1048576⟩ := by
  decide +kernel

theorem context_10_23263_1314161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23263 ⟨1314161, by decide⟩ :=
  accepted_of_selected 10 23263 ⟨1314161, by decide⟩ ⟨10, 2, 0, 1314161, 23263, 189, 1048576⟩
    (by decide) selected_cut_47023

theorem unmarked_context_9_5815_1314162 : frontier 12 ⟨1314162, by decide⟩
    (prefixCache 9 5815) (prefixPartial 9 5815) = false := by
  decide +kernel

theorem node_context_9_5815_1314162 : EJMOriginalGlobalDAGData.nodes 12 ⟨1314162, by decide⟩ =
    .split (coordinate 9) (![⟨1314072, by decide⟩,⟨1314114, by decide⟩,⟨1314153, by decide⟩,⟨1314161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5815_1314162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5815 ⟨1314162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5815
    ⟨1314162, by decide⟩ (by decide) (![⟨1314072, by decide⟩,⟨1314114, by decide⟩,⟨1314153, by decide⟩,⟨1314161, by decide⟩]) unmarked_context_9_5815_1314162 node_context_9_5815_1314162
  intro a
  fin_cases a
  · exact context_10_23260_1314072
  · exact context_10_23261_1314114
  · exact context_10_23262_1314153
  · exact context_10_23263_1314161

theorem unmarked_context_8_1453_1314163 : frontier 13 ⟨1314163, by decide⟩
    (prefixCache 8 1453) (prefixPartial 8 1453) = false := by
  decide +kernel

theorem node_context_8_1453_1314163 : EJMOriginalGlobalDAGData.nodes 13 ⟨1314163, by decide⟩ =
    .split (coordinate 8) (![⟨1312821, by decide⟩,⟨1313497, by decide⟩,⟨1314004, by decide⟩,⟨1314162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1453_1314163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1453 ⟨1314163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1453
    ⟨1314163, by decide⟩ (by decide) (![⟨1312821, by decide⟩,⟨1313497, by decide⟩,⟨1314004, by decide⟩,⟨1314162, by decide⟩]) unmarked_context_8_1453_1314163 node_context_8_1453_1314163
  intro a
  fin_cases a
  · exact context_9_5812_1312821
  · exact context_9_5813_1313497
  · exact context_9_5814_1314004
  · exact context_9_5815_1314162

theorem selected_cut_47024 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 93056) = some ⟨11, 1, 0, 434745, 93056, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93056_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93056 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 93056 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 93056, 1, 262144⟩
    (by decide) selected_cut_47024

theorem selected_cut_47025 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 372228) = some ⟨12, 1, 0, 448748, 372228, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372228_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372228 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 372228 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 372228, 1, 65536⟩
    (by decide) selected_cut_47025

theorem selected_cut_47026 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 372229) = some ⟨12, 1, 0, 34034, 372229, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372229_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372229 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 372229 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 372229, 1, 65536⟩
    (by decide) selected_cut_47026

theorem selected_cut_47027 : selected 9 ⟨1314222, by decide⟩
    (prefixPartial 12 372230) = some ⟨12, 2, 0, 1314222, 372230, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_372230_1314222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372230 ⟨1314222, by decide⟩ :=
  accepted_of_selected 12 372230 ⟨1314222, by decide⟩ ⟨12, 2, 0, 1314222, 372230, 3465, 65536⟩
    (by decide) selected_cut_47027

theorem selected_cut_47028 : selected 8 ⟨1314252, by decide⟩
    (prefixPartial 13 1488924) = some ⟨13, 2, 0, 1314252, 1488924, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_1488924_1314252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1488924 ⟨1314252, by decide⟩ :=
  accepted_of_selected 13 1488924 ⟨1314252, by decide⟩ ⟨13, 2, 0, 1314252, 1488924, 1913, 16384⟩
    (by decide) selected_cut_47028

theorem selected_cut_47029 : selected 8 ⟨1314271, by decide⟩
    (prefixPartial 13 1488925) = some ⟨13, 2, 0, 1314271, 1488925, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_1488925_1314271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1488925 ⟨1314271, by decide⟩ :=
  accepted_of_selected 13 1488925 ⟨1314271, by decide⟩ ⟨13, 2, 0, 1314271, 1488925, 1157, 16384⟩
    (by decide) selected_cut_47029

theorem selected_cut_47030 : selected 8 ⟨1314293, by decide⟩
    (prefixPartial 13 1488926) = some ⟨13, 2, 0, 1314293, 1488926, 853, 16384⟩ := by
  decide +kernel

theorem context_13_1488926_1314293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1488926 ⟨1314293, by decide⟩ :=
  accepted_of_selected 13 1488926 ⟨1314293, by decide⟩ ⟨13, 2, 0, 1314293, 1488926, 853, 16384⟩
    (by decide) selected_cut_47030

theorem selected_cut_47031 : selected 8 ⟨1314300, by decide⟩
    (prefixPartial 13 1488927) = some ⟨13, 2, 0, 1314300, 1488927, 489, 16384⟩ := by
  decide +kernel

theorem context_13_1488927_1314300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1488927 ⟨1314300, by decide⟩ :=
  accepted_of_selected 13 1488927 ⟨1314300, by decide⟩ ⟨13, 2, 0, 1314300, 1488927, 489, 16384⟩
    (by decide) selected_cut_47031

theorem unmarked_context_12_372231_1314301 : frontier 9 ⟨1314301, by decide⟩
    (prefixCache 12 372231) (prefixPartial 12 372231) = false := by
  decide +kernel

theorem node_context_12_372231_1314301 : EJMOriginalGlobalDAGData.nodes 9 ⟨1314301, by decide⟩ =
    .split (coordinate 12) (![⟨1314252, by decide⟩,⟨1314271, by decide⟩,⟨1314293, by decide⟩,⟨1314300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_372231_1314301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372231 ⟨1314301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 372231
    ⟨1314301, by decide⟩ (by decide) (![⟨1314252, by decide⟩,⟨1314271, by decide⟩,⟨1314293, by decide⟩,⟨1314300, by decide⟩]) unmarked_context_12_372231_1314301 node_context_12_372231_1314301
  intro a
  fin_cases a
  · exact context_13_1488924_1314252
  · exact context_13_1488925_1314271
  · exact context_13_1488926_1314293
  · exact context_13_1488927_1314300

theorem unmarked_context_11_93057_1314302 : frontier 10 ⟨1314302, by decide⟩
    (prefixCache 11 93057) (prefixPartial 11 93057) = false := by
  decide +kernel

theorem node_context_11_93057_1314302 : EJMOriginalGlobalDAGData.nodes 10 ⟨1314302, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1314222, by decide⟩,⟨1314301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93057_1314302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93057 ⟨1314302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93057
    ⟨1314302, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1314222, by decide⟩,⟨1314301, by decide⟩]) unmarked_context_11_93057_1314302 node_context_11_93057_1314302
  intro a
  fin_cases a
  · exact context_12_372228_448748
  · exact context_12_372229_34034
  · exact context_12_372230_1314222
  · exact context_12_372231_1314301

theorem selected_cut_47032 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 372232) = some ⟨12, 1, 0, 448748, 372232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372232_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372232 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 372232 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 372232, 1, 65536⟩
    (by decide) selected_cut_47032

theorem selected_cut_47033 : selected 9 ⟨1314377, by decide⟩
    (prefixPartial 12 372233) = some ⟨12, 2, 0, 1314377, 372233, 3553, 65536⟩ := by
  decide +kernel

theorem context_12_372233_1314377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372233 ⟨1314377, by decide⟩ :=
  accepted_of_selected 12 372233 ⟨1314377, by decide⟩ ⟨12, 2, 0, 1314377, 372233, 3553, 65536⟩
    (by decide) selected_cut_47033

theorem selected_cut_47034 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 372234) = some ⟨12, 1, 0, 893903, 372234, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372234_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372234 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 372234 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 372234, 1, 65536⟩
    (by decide) selected_cut_47034

theorem selected_cut_47035 : selected 9 ⟨1314444, by decide⟩
    (prefixPartial 12 372235) = some ⟨12, 2, 0, 1314444, 372235, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_372235_1314444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372235 ⟨1314444, by decide⟩ :=
  accepted_of_selected 12 372235 ⟨1314444, by decide⟩ ⟨12, 2, 0, 1314444, 372235, 3689, 65536⟩
    (by decide) selected_cut_47035

theorem unmarked_context_11_93058_1314445 : frontier 10 ⟨1314445, by decide⟩
    (prefixCache 11 93058) (prefixPartial 11 93058) = false := by
  decide +kernel

theorem node_context_11_93058_1314445 : EJMOriginalGlobalDAGData.nodes 10 ⟨1314445, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1314377, by decide⟩,⟨893903, by decide⟩,⟨1314444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93058_1314445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93058 ⟨1314445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93058
    ⟨1314445, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1314377, by decide⟩,⟨893903, by decide⟩,⟨1314444, by decide⟩]) unmarked_context_11_93058_1314445 node_context_11_93058_1314445
  intro a
  fin_cases a
  · exact context_12_372232_448748
  · exact context_12_372233_1314377
  · exact context_12_372234_893903
  · exact context_12_372235_1314444

theorem selected_cut_47036 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 372236) = some ⟨12, 1, 0, 448748, 372236, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372236_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372236 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 372236 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 372236, 1, 65536⟩
    (by decide) selected_cut_47036

theorem selected_cut_47037 : selected 9 ⟨1314502, by decide⟩
    (prefixPartial 12 372237) = some ⟨12, 2, 0, 1314502, 372237, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_372237_1314502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372237 ⟨1314502, by decide⟩ :=
  accepted_of_selected 12 372237 ⟨1314502, by decide⟩ ⟨12, 2, 0, 1314502, 372237, 3429, 65536⟩
    (by decide) selected_cut_47037

theorem selected_cut_47038 : selected 9 ⟨1314557, by decide⟩
    (prefixPartial 12 372238) = some ⟨12, 2, 0, 1314557, 372238, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_372238_1314557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372238 ⟨1314557, by decide⟩ :=
  accepted_of_selected 12 372238 ⟨1314557, by decide⟩ ⟨12, 2, 0, 1314557, 372238, 2925, 65536⟩
    (by decide) selected_cut_47038

theorem selected_cut_47039 : selected 9 ⟨1314609, by decide⟩
    (prefixPartial 12 372239) = some ⟨12, 2, 0, 1314609, 372239, 3313, 65536⟩ := by
  decide +kernel

theorem context_12_372239_1314609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372239 ⟨1314609, by decide⟩ :=
  accepted_of_selected 12 372239 ⟨1314609, by decide⟩ ⟨12, 2, 0, 1314609, 372239, 3313, 65536⟩
    (by decide) selected_cut_47039

theorem unmarked_context_11_93059_1314610 : frontier 10 ⟨1314610, by decide⟩
    (prefixCache 11 93059) (prefixPartial 11 93059) = false := by
  decide +kernel

theorem node_context_11_93059_1314610 : EJMOriginalGlobalDAGData.nodes 10 ⟨1314610, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1314502, by decide⟩,⟨1314557, by decide⟩,⟨1314609, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93059_1314610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93059 ⟨1314610, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93059
    ⟨1314610, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1314502, by decide⟩,⟨1314557, by decide⟩,⟨1314609, by decide⟩]) unmarked_context_11_93059_1314610 node_context_11_93059_1314610
  intro a
  fin_cases a
  · exact context_12_372236_448748
  · exact context_12_372237_1314502
  · exact context_12_372238_1314557
  · exact context_12_372239_1314609

theorem unmarked_context_10_23264_1314611 : frontier 11 ⟨1314611, by decide⟩
    (prefixCache 10 23264) (prefixPartial 10 23264) = false := by
  decide +kernel

theorem node_context_10_23264_1314611 : EJMOriginalGlobalDAGData.nodes 11 ⟨1314611, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1314302, by decide⟩,⟨1314445, by decide⟩,⟨1314610, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23264_1314611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23264 ⟨1314611, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23264
    ⟨1314611, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1314302, by decide⟩,⟨1314445, by decide⟩,⟨1314610, by decide⟩]) unmarked_context_10_23264_1314611 node_context_10_23264_1314611
  intro a
  fin_cases a
  · exact context_11_93056_434745
  · exact context_11_93057_1314302
  · exact context_11_93058_1314445
  · exact context_11_93059_1314610

theorem selected_cut_47040 : selected 9 ⟨1255011, by decide⟩
    (prefixPartial 12 372240) = some ⟨12, 1, 0, 1255011, 372240, 1, 65536⟩ := by
  decide +kernel

theorem context_12_372240_1255011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372240 ⟨1255011, by decide⟩ :=
  accepted_of_selected 12 372240 ⟨1255011, by decide⟩ ⟨12, 1, 0, 1255011, 372240, 1, 65536⟩
    (by decide) selected_cut_47040

theorem selected_cut_47041 : selected 9 ⟨1314660, by decide⟩
    (prefixPartial 12 372241) = some ⟨12, 2, 0, 1314660, 372241, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_372241_1314660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372241 ⟨1314660, by decide⟩ :=
  accepted_of_selected 12 372241 ⟨1314660, by decide⟩ ⟨12, 2, 0, 1314660, 372241, 3365, 65536⟩
    (by decide) selected_cut_47041

theorem selected_cut_47042 : selected 9 ⟨1314715, by decide⟩
    (prefixPartial 12 372242) = some ⟨12, 2, 0, 1314715, 372242, 3017, 65536⟩ := by
  decide +kernel

theorem context_12_372242_1314715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372242 ⟨1314715, by decide⟩ :=
  accepted_of_selected 12 372242 ⟨1314715, by decide⟩ ⟨12, 2, 0, 1314715, 372242, 3017, 65536⟩
    (by decide) selected_cut_47042

theorem selected_cut_47043 : selected 9 ⟨1314777, by decide⟩
    (prefixPartial 12 372243) = some ⟨12, 2, 0, 1314777, 372243, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_372243_1314777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 372243 ⟨1314777, by decide⟩ :=
  accepted_of_selected 12 372243 ⟨1314777, by decide⟩ ⟨12, 2, 0, 1314777, 372243, 3721, 65536⟩
    (by decide) selected_cut_47043

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
