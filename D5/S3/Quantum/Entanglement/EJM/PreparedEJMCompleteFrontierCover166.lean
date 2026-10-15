/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover165
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_27987_406758 : frontier 9 ⟨406758, by decide⟩
    (prefixCache 12 27987) (prefixPartial 12 27987) = false := by
  decide +kernel

theorem node_context_12_27987_406758 : EJMOriginalGlobalDAGData.nodes 9 ⟨406758, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406710, by decide⟩,⟨406748, by decide⟩,⟨406757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27987_406758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27987 ⟨406758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27987
    ⟨406758, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406710, by decide⟩,⟨406748, by decide⟩,⟨406757, by decide⟩]) unmarked_context_12_27987_406758 node_context_12_27987_406758
  intro a
  fin_cases a
  · exact context_13_111948_3444
  · exact context_13_111949_406710
  · exact context_13_111950_406748
  · exact context_13_111951_406757

theorem unmarked_context_11_6996_406759 : frontier 10 ⟨406759, by decide⟩
    (prefixCache 11 6996) (prefixPartial 11 6996) = false := by
  decide +kernel

theorem node_context_11_6996_406759 : EJMOriginalGlobalDAGData.nodes 10 ⟨406759, by decide⟩ =
    .split (coordinate 11) (![⟨406626, by decide⟩,⟨170504, by decide⟩,⟨406680, by decide⟩,⟨406758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6996_406759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6996 ⟨406759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6996
    ⟨406759, by decide⟩ (by decide) (![⟨406626, by decide⟩,⟨170504, by decide⟩,⟨406680, by decide⟩,⟨406758, by decide⟩]) unmarked_context_11_6996_406759 node_context_11_6996_406759
  intro a
  fin_cases a
  · exact context_12_27984_406626
  · exact context_12_27985_170504
  · exact context_12_27986_406680
  · exact context_12_27987_406758

theorem selected_cut_15940 : selected 9 ⟨406803, by decide⟩
    (prefixPartial 12 27988) = some ⟨12, 2, 0, 406803, 27988, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_27988_406803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27988 ⟨406803, by decide⟩ :=
  accepted_of_selected 12 27988 ⟨406803, by decide⟩ ⟨12, 2, 0, 406803, 27988, 3633, 65536⟩
    (by decide) selected_cut_15940

theorem selected_cut_15941 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 27989) = some ⟨12, 1, 0, 170504, 27989, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27989_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27989 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 27989 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 27989, 1, 65536⟩
    (by decide) selected_cut_15941

theorem selected_cut_15942 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111960) = some ⟨13, 1, 0, 3444, 111960, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111960_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111960 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111960 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111960, 1, 16384⟩
    (by decide) selected_cut_15942

theorem selected_cut_15943 : selected 8 ⟨406818, by decide⟩
    (prefixPartial 13 111961) = some ⟨13, 2, 0, 406818, 111961, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_111961_406818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111961 ⟨406818, by decide⟩ :=
  accepted_of_selected 13 111961 ⟨406818, by decide⟩ ⟨13, 2, 0, 406818, 111961, 1541, 16384⟩
    (by decide) selected_cut_15943

theorem selected_cut_15944 : selected 8 ⟨406840, by decide⟩
    (prefixPartial 13 111962) = some ⟨13, 2, 0, 406840, 111962, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_111962_406840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111962 ⟨406840, by decide⟩ :=
  accepted_of_selected 13 111962 ⟨406840, by decide⟩ ⟨13, 2, 0, 406840, 111962, 1997, 16384⟩
    (by decide) selected_cut_15944

theorem selected_cut_15945 : selected 8 ⟨406846, by decide⟩
    (prefixPartial 13 111963) = some ⟨13, 2, 0, 406846, 111963, 781, 16384⟩ := by
  decide +kernel

theorem context_13_111963_406846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111963 ⟨406846, by decide⟩ :=
  accepted_of_selected 13 111963 ⟨406846, by decide⟩ ⟨13, 2, 0, 406846, 111963, 781, 16384⟩
    (by decide) selected_cut_15945

theorem unmarked_context_12_27990_406847 : frontier 9 ⟨406847, by decide⟩
    (prefixCache 12 27990) (prefixPartial 12 27990) = false := by
  decide +kernel

theorem node_context_12_27990_406847 : EJMOriginalGlobalDAGData.nodes 9 ⟨406847, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406818, by decide⟩,⟨406840, by decide⟩,⟨406846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27990_406847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27990 ⟨406847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27990
    ⟨406847, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406818, by decide⟩,⟨406840, by decide⟩,⟨406846, by decide⟩]) unmarked_context_12_27990_406847 node_context_12_27990_406847
  intro a
  fin_cases a
  · exact context_13_111960_3444
  · exact context_13_111961_406818
  · exact context_13_111962_406840
  · exact context_13_111963_406846

theorem selected_cut_15946 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111964) = some ⟨13, 1, 0, 3444, 111964, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111964_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111964 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111964 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111964, 1, 16384⟩
    (by decide) selected_cut_15946

theorem selected_cut_15947 : selected 8 ⟨406865, by decide⟩
    (prefixPartial 13 111965) = some ⟨13, 2, 0, 406865, 111965, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_111965_406865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111965 ⟨406865, by decide⟩ :=
  accepted_of_selected 13 111965 ⟨406865, by decide⟩ ⟨13, 2, 0, 406865, 111965, 1649, 16384⟩
    (by decide) selected_cut_15947

theorem selected_cut_15948 : selected 8 ⟨406880, by decide⟩
    (prefixPartial 13 111966) = some ⟨13, 2, 0, 406880, 111966, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_111966_406880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111966 ⟨406880, by decide⟩ :=
  accepted_of_selected 13 111966 ⟨406880, by decide⟩ ⟨13, 2, 0, 406880, 111966, 1973, 16384⟩
    (by decide) selected_cut_15948

theorem selected_cut_15949 : selected 8 ⟨406887, by decide⟩
    (prefixPartial 13 111967) = some ⟨13, 2, 0, 406887, 111967, 901, 16384⟩ := by
  decide +kernel

theorem context_13_111967_406887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111967 ⟨406887, by decide⟩ :=
  accepted_of_selected 13 111967 ⟨406887, by decide⟩ ⟨13, 2, 0, 406887, 111967, 901, 16384⟩
    (by decide) selected_cut_15949

theorem unmarked_context_12_27991_406888 : frontier 9 ⟨406888, by decide⟩
    (prefixCache 12 27991) (prefixPartial 12 27991) = false := by
  decide +kernel

theorem node_context_12_27991_406888 : EJMOriginalGlobalDAGData.nodes 9 ⟨406888, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406865, by decide⟩,⟨406880, by decide⟩,⟨406887, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27991_406888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27991 ⟨406888, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27991
    ⟨406888, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406865, by decide⟩,⟨406880, by decide⟩,⟨406887, by decide⟩]) unmarked_context_12_27991_406888 node_context_12_27991_406888
  intro a
  fin_cases a
  · exact context_13_111964_3444
  · exact context_13_111965_406865
  · exact context_13_111966_406880
  · exact context_13_111967_406887

theorem unmarked_context_11_6997_406889 : frontier 10 ⟨406889, by decide⟩
    (prefixCache 11 6997) (prefixPartial 11 6997) = false := by
  decide +kernel

theorem node_context_11_6997_406889 : EJMOriginalGlobalDAGData.nodes 10 ⟨406889, by decide⟩ =
    .split (coordinate 11) (![⟨406803, by decide⟩,⟨170504, by decide⟩,⟨406847, by decide⟩,⟨406888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6997_406889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6997 ⟨406889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6997
    ⟨406889, by decide⟩ (by decide) (![⟨406803, by decide⟩,⟨170504, by decide⟩,⟨406847, by decide⟩,⟨406888, by decide⟩]) unmarked_context_11_6997_406889 node_context_11_6997_406889
  intro a
  fin_cases a
  · exact context_12_27988_406803
  · exact context_12_27989_170504
  · exact context_12_27990_406847
  · exact context_12_27991_406888

theorem selected_cut_15950 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111968) = some ⟨13, 1, 0, 3444, 111968, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111968_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111968 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111968 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111968, 1, 16384⟩
    (by decide) selected_cut_15950

theorem selected_cut_15951 : selected 8 ⟨406909, by decide⟩
    (prefixPartial 13 111969) = some ⟨13, 2, 0, 406909, 111969, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_111969_406909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111969 ⟨406909, by decide⟩ :=
  accepted_of_selected 13 111969 ⟨406909, by decide⟩ ⟨13, 2, 0, 406909, 111969, 1533, 16384⟩
    (by decide) selected_cut_15951

theorem selected_cut_15952 : selected 8 ⟨406933, by decide⟩
    (prefixPartial 13 111970) = some ⟨13, 2, 0, 406933, 111970, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_111970_406933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111970 ⟨406933, by decide⟩ :=
  accepted_of_selected 13 111970 ⟨406933, by decide⟩ ⟨13, 2, 0, 406933, 111970, 1837, 16384⟩
    (by decide) selected_cut_15952

theorem selected_cut_15953 : selected 8 ⟨406940, by decide⟩
    (prefixPartial 13 111971) = some ⟨13, 2, 0, 406940, 111971, 729, 16384⟩ := by
  decide +kernel

theorem context_13_111971_406940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111971 ⟨406940, by decide⟩ :=
  accepted_of_selected 13 111971 ⟨406940, by decide⟩ ⟨13, 2, 0, 406940, 111971, 729, 16384⟩
    (by decide) selected_cut_15953

theorem unmarked_context_12_27992_406941 : frontier 9 ⟨406941, by decide⟩
    (prefixCache 12 27992) (prefixPartial 12 27992) = false := by
  decide +kernel

theorem node_context_12_27992_406941 : EJMOriginalGlobalDAGData.nodes 9 ⟨406941, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406909, by decide⟩,⟨406933, by decide⟩,⟨406940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27992_406941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27992 ⟨406941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27992
    ⟨406941, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406909, by decide⟩,⟨406933, by decide⟩,⟨406940, by decide⟩]) unmarked_context_12_27992_406941 node_context_12_27992_406941
  intro a
  fin_cases a
  · exact context_13_111968_3444
  · exact context_13_111969_406909
  · exact context_13_111970_406933
  · exact context_13_111971_406940

theorem selected_cut_15954 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 27993) = some ⟨12, 1, 0, 126371, 27993, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27993_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27993 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 27993 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 27993, 1, 65536⟩
    (by decide) selected_cut_15954

theorem selected_cut_15955 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111976) = some ⟨13, 1, 0, 3444, 111976, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111976_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111976 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111976 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111976, 1, 16384⟩
    (by decide) selected_cut_15955

theorem selected_cut_15956 : selected 8 ⟨406957, by decide⟩
    (prefixPartial 13 111977) = some ⟨13, 2, 0, 406957, 111977, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_111977_406957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111977 ⟨406957, by decide⟩ :=
  accepted_of_selected 13 111977 ⟨406957, by decide⟩ ⟨13, 2, 0, 406957, 111977, 1549, 16384⟩
    (by decide) selected_cut_15956

theorem selected_cut_15957 : selected 8 ⟨406983, by decide⟩
    (prefixPartial 13 111978) = some ⟨13, 2, 0, 406983, 111978, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_111978_406983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111978 ⟨406983, by decide⟩ :=
  accepted_of_selected 13 111978 ⟨406983, by decide⟩ ⟨13, 2, 0, 406983, 111978, 2033, 16384⟩
    (by decide) selected_cut_15957

theorem selected_cut_15958 : selected 8 ⟨406992, by decide⟩
    (prefixPartial 13 111979) = some ⟨13, 2, 0, 406992, 111979, 885, 16384⟩ := by
  decide +kernel

theorem context_13_111979_406992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111979 ⟨406992, by decide⟩ :=
  accepted_of_selected 13 111979 ⟨406992, by decide⟩ ⟨13, 2, 0, 406992, 111979, 885, 16384⟩
    (by decide) selected_cut_15958

theorem unmarked_context_12_27994_406993 : frontier 9 ⟨406993, by decide⟩
    (prefixCache 12 27994) (prefixPartial 12 27994) = false := by
  decide +kernel

theorem node_context_12_27994_406993 : EJMOriginalGlobalDAGData.nodes 9 ⟨406993, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨406957, by decide⟩,⟨406983, by decide⟩,⟨406992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27994_406993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27994 ⟨406993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27994
    ⟨406993, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨406957, by decide⟩,⟨406983, by decide⟩,⟨406992, by decide⟩]) unmarked_context_12_27994_406993 node_context_12_27994_406993
  intro a
  fin_cases a
  · exact context_13_111976_3444
  · exact context_13_111977_406957
  · exact context_13_111978_406983
  · exact context_13_111979_406992

theorem selected_cut_15959 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111980) = some ⟨13, 1, 0, 3444, 111980, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111980_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111980 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111980 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111980, 1, 16384⟩
    (by decide) selected_cut_15959

theorem selected_cut_15960 : selected 8 ⟨407014, by decide⟩
    (prefixPartial 13 111981) = some ⟨13, 2, 0, 407014, 111981, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_111981_407014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111981 ⟨407014, by decide⟩ :=
  accepted_of_selected 13 111981 ⟨407014, by decide⟩ ⟨13, 2, 0, 407014, 111981, 1649, 16384⟩
    (by decide) selected_cut_15960

theorem selected_cut_15961 : selected 8 ⟨407045, by decide⟩
    (prefixPartial 13 111982) = some ⟨13, 2, 0, 407045, 111982, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_111982_407045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111982 ⟨407045, by decide⟩ :=
  accepted_of_selected 13 111982 ⟨407045, by decide⟩ ⟨13, 2, 0, 407045, 111982, 2049, 16384⟩
    (by decide) selected_cut_15961

theorem selected_cut_15962 : selected 8 ⟨407052, by decide⟩
    (prefixPartial 13 111983) = some ⟨13, 2, 0, 407052, 111983, 997, 16384⟩ := by
  decide +kernel

theorem context_13_111983_407052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111983 ⟨407052, by decide⟩ :=
  accepted_of_selected 13 111983 ⟨407052, by decide⟩ ⟨13, 2, 0, 407052, 111983, 997, 16384⟩
    (by decide) selected_cut_15962

theorem unmarked_context_12_27995_407053 : frontier 9 ⟨407053, by decide⟩
    (prefixCache 12 27995) (prefixPartial 12 27995) = false := by
  decide +kernel

theorem node_context_12_27995_407053 : EJMOriginalGlobalDAGData.nodes 9 ⟨407053, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407014, by decide⟩,⟨407045, by decide⟩,⟨407052, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27995_407053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27995 ⟨407053, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27995
    ⟨407053, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407014, by decide⟩,⟨407045, by decide⟩,⟨407052, by decide⟩]) unmarked_context_12_27995_407053 node_context_12_27995_407053
  intro a
  fin_cases a
  · exact context_13_111980_3444
  · exact context_13_111981_407014
  · exact context_13_111982_407045
  · exact context_13_111983_407052

theorem unmarked_context_11_6998_407054 : frontier 10 ⟨407054, by decide⟩
    (prefixCache 11 6998) (prefixPartial 11 6998) = false := by
  decide +kernel

theorem node_context_11_6998_407054 : EJMOriginalGlobalDAGData.nodes 10 ⟨407054, by decide⟩ =
    .split (coordinate 11) (![⟨406941, by decide⟩,⟨126371, by decide⟩,⟨406993, by decide⟩,⟨407053, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6998_407054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6998 ⟨407054, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6998
    ⟨407054, by decide⟩ (by decide) (![⟨406941, by decide⟩,⟨126371, by decide⟩,⟨406993, by decide⟩,⟨407053, by decide⟩]) unmarked_context_11_6998_407054 node_context_11_6998_407054
  intro a
  fin_cases a
  · exact context_12_27992_406941
  · exact context_12_27993_126371
  · exact context_12_27994_406993
  · exact context_12_27995_407053

theorem selected_cut_15963 : selected 9 ⟨407091, by decide⟩
    (prefixPartial 12 27996) = some ⟨12, 2, 0, 407091, 27996, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_27996_407091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27996 ⟨407091, by decide⟩ :=
  accepted_of_selected 12 27996 ⟨407091, by decide⟩ ⟨12, 2, 0, 407091, 27996, 3893, 65536⟩
    (by decide) selected_cut_15963

theorem selected_cut_15964 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 27997) = some ⟨12, 1, 0, 320864, 27997, 1, 65536⟩ := by
  decide +kernel

theorem context_12_27997_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27997 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 27997 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 27997, 1, 65536⟩
    (by decide) selected_cut_15964

theorem selected_cut_15965 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111992) = some ⟨13, 1, 0, 3444, 111992, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111992_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111992 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111992 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111992, 1, 16384⟩
    (by decide) selected_cut_15965

theorem selected_cut_15966 : selected 8 ⟨407104, by decide⟩
    (prefixPartial 13 111993) = some ⟨13, 2, 0, 407104, 111993, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_111993_407104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111993 ⟨407104, by decide⟩ :=
  accepted_of_selected 13 111993 ⟨407104, by decide⟩ ⟨13, 2, 0, 407104, 111993, 1441, 16384⟩
    (by decide) selected_cut_15966

theorem selected_cut_15967 : selected 8 ⟨407127, by decide⟩
    (prefixPartial 13 111994) = some ⟨13, 2, 0, 407127, 111994, 1945, 16384⟩ := by
  decide +kernel

theorem context_13_111994_407127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111994 ⟨407127, by decide⟩ :=
  accepted_of_selected 13 111994 ⟨407127, by decide⟩ ⟨13, 2, 0, 407127, 111994, 1945, 16384⟩
    (by decide) selected_cut_15967

theorem selected_cut_15968 : selected 8 ⟨407136, by decide⟩
    (prefixPartial 13 111995) = some ⟨13, 2, 0, 407136, 111995, 925, 16384⟩ := by
  decide +kernel

theorem context_13_111995_407136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111995 ⟨407136, by decide⟩ :=
  accepted_of_selected 13 111995 ⟨407136, by decide⟩ ⟨13, 2, 0, 407136, 111995, 925, 16384⟩
    (by decide) selected_cut_15968

theorem unmarked_context_12_27998_407137 : frontier 9 ⟨407137, by decide⟩
    (prefixCache 12 27998) (prefixPartial 12 27998) = false := by
  decide +kernel

theorem node_context_12_27998_407137 : EJMOriginalGlobalDAGData.nodes 9 ⟨407137, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407104, by decide⟩,⟨407127, by decide⟩,⟨407136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27998_407137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27998 ⟨407137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27998
    ⟨407137, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407104, by decide⟩,⟨407127, by decide⟩,⟨407136, by decide⟩]) unmarked_context_12_27998_407137 node_context_12_27998_407137
  intro a
  fin_cases a
  · exact context_13_111992_3444
  · exact context_13_111993_407104
  · exact context_13_111994_407127
  · exact context_13_111995_407136

theorem selected_cut_15969 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 111996) = some ⟨13, 1, 0, 3444, 111996, 1, 16384⟩ := by
  decide +kernel

theorem context_13_111996_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111996 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 111996 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 111996, 1, 16384⟩
    (by decide) selected_cut_15969

theorem selected_cut_15970 : selected 8 ⟨407151, by decide⟩
    (prefixPartial 13 111997) = some ⟨13, 2, 0, 407151, 111997, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_111997_407151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111997 ⟨407151, by decide⟩ :=
  accepted_of_selected 13 111997 ⟨407151, by decide⟩ ⟨13, 2, 0, 407151, 111997, 1457, 16384⟩
    (by decide) selected_cut_15970

theorem selected_cut_15971 : selected 8 ⟨407169, by decide⟩
    (prefixPartial 13 111998) = some ⟨13, 2, 0, 407169, 111998, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_111998_407169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111998 ⟨407169, by decide⟩ :=
  accepted_of_selected 13 111998 ⟨407169, by decide⟩ ⟨13, 2, 0, 407169, 111998, 1941, 16384⟩
    (by decide) selected_cut_15971

theorem selected_cut_15972 : selected 8 ⟨407177, by decide⟩
    (prefixPartial 13 111999) = some ⟨13, 2, 0, 407177, 111999, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_111999_407177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 111999 ⟨407177, by decide⟩ :=
  accepted_of_selected 13 111999 ⟨407177, by decide⟩ ⟨13, 2, 0, 407177, 111999, 1053, 16384⟩
    (by decide) selected_cut_15972

theorem unmarked_context_12_27999_407178 : frontier 9 ⟨407178, by decide⟩
    (prefixCache 12 27999) (prefixPartial 12 27999) = false := by
  decide +kernel

theorem node_context_12_27999_407178 : EJMOriginalGlobalDAGData.nodes 9 ⟨407178, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407151, by decide⟩,⟨407169, by decide⟩,⟨407177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27999_407178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27999 ⟨407178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27999
    ⟨407178, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407151, by decide⟩,⟨407169, by decide⟩,⟨407177, by decide⟩]) unmarked_context_12_27999_407178 node_context_12_27999_407178
  intro a
  fin_cases a
  · exact context_13_111996_3444
  · exact context_13_111997_407151
  · exact context_13_111998_407169
  · exact context_13_111999_407177

theorem unmarked_context_11_6999_407179 : frontier 10 ⟨407179, by decide⟩
    (prefixCache 11 6999) (prefixPartial 11 6999) = false := by
  decide +kernel

theorem node_context_11_6999_407179 : EJMOriginalGlobalDAGData.nodes 10 ⟨407179, by decide⟩ =
    .split (coordinate 11) (![⟨407091, by decide⟩,⟨320864, by decide⟩,⟨407137, by decide⟩,⟨407178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6999_407179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6999 ⟨407179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6999
    ⟨407179, by decide⟩ (by decide) (![⟨407091, by decide⟩,⟨320864, by decide⟩,⟨407137, by decide⟩,⟨407178, by decide⟩]) unmarked_context_11_6999_407179 node_context_11_6999_407179
  intro a
  fin_cases a
  · exact context_12_27996_407091
  · exact context_12_27997_320864
  · exact context_12_27998_407137
  · exact context_12_27999_407178

theorem unmarked_context_10_1749_407180 : frontier 11 ⟨407180, by decide⟩
    (prefixCache 10 1749) (prefixPartial 10 1749) = false := by
  decide +kernel

theorem node_context_10_1749_407180 : EJMOriginalGlobalDAGData.nodes 11 ⟨407180, by decide⟩ =
    .split (coordinate 10) (![⟨406759, by decide⟩,⟨406889, by decide⟩,⟨407054, by decide⟩,⟨407179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1749_407180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1749 ⟨407180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1749
    ⟨407180, by decide⟩ (by decide) (![⟨406759, by decide⟩,⟨406889, by decide⟩,⟨407054, by decide⟩,⟨407179, by decide⟩]) unmarked_context_10_1749_407180 node_context_10_1749_407180
  intro a
  fin_cases a
  · exact context_11_6996_406759
  · exact context_11_6997_406889
  · exact context_11_6998_407054
  · exact context_11_6999_407179

theorem selected_cut_15973 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112000) = some ⟨13, 1, 0, 3444, 112000, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112000_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112000 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112000 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112000, 1, 16384⟩
    (by decide) selected_cut_15973

theorem selected_cut_15974 : selected 8 ⟨407204, by decide⟩
    (prefixPartial 13 112001) = some ⟨13, 2, 0, 407204, 112001, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_112001_407204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112001 ⟨407204, by decide⟩ :=
  accepted_of_selected 13 112001 ⟨407204, by decide⟩ ⟨13, 2, 0, 407204, 112001, 1717, 16384⟩
    (by decide) selected_cut_15974

theorem selected_cut_15975 : selected 8 ⟨407222, by decide⟩
    (prefixPartial 13 112002) = some ⟨13, 2, 0, 407222, 112002, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_112002_407222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112002 ⟨407222, by decide⟩ :=
  accepted_of_selected 13 112002 ⟨407222, by decide⟩ ⟨13, 2, 0, 407222, 112002, 1973, 16384⟩
    (by decide) selected_cut_15975

theorem selected_cut_15976 : selected 8 ⟨407229, by decide⟩
    (prefixPartial 13 112003) = some ⟨13, 2, 0, 407229, 112003, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_112003_407229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112003 ⟨407229, by decide⟩ :=
  accepted_of_selected 13 112003 ⟨407229, by decide⟩ ⟨13, 2, 0, 407229, 112003, 1005, 16384⟩
    (by decide) selected_cut_15976

theorem unmarked_context_12_28000_407230 : frontier 9 ⟨407230, by decide⟩
    (prefixCache 12 28000) (prefixPartial 12 28000) = false := by
  decide +kernel

theorem node_context_12_28000_407230 : EJMOriginalGlobalDAGData.nodes 9 ⟨407230, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407204, by decide⟩,⟨407222, by decide⟩,⟨407229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28000_407230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28000 ⟨407230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28000
    ⟨407230, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407204, by decide⟩,⟨407222, by decide⟩,⟨407229, by decide⟩]) unmarked_context_12_28000_407230 node_context_12_28000_407230
  intro a
  fin_cases a
  · exact context_13_112000_3444
  · exact context_13_112001_407204
  · exact context_13_112002_407222
  · exact context_13_112003_407229

theorem selected_cut_15977 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112004) = some ⟨13, 1, 0, 3444, 112004, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112004_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112004 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112004 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112004, 1, 16384⟩
    (by decide) selected_cut_15977

theorem selected_cut_15978 : selected 8 ⟨407274, by decide⟩
    (prefixPartial 13 112005) = some ⟨13, 2, 0, 407274, 112005, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_112005_407274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112005 ⟨407274, by decide⟩ :=
  accepted_of_selected 13 112005 ⟨407274, by decide⟩ ⟨13, 2, 0, 407274, 112005, 2173, 16384⟩
    (by decide) selected_cut_15978

theorem selected_cut_15979 : selected 8 ⟨407349, by decide⟩
    (prefixPartial 13 112006) = some ⟨13, 2, 0, 407349, 112006, 3285, 16384⟩ := by
  decide +kernel

theorem context_13_112006_407349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112006 ⟨407349, by decide⟩ :=
  accepted_of_selected 13 112006 ⟨407349, by decide⟩ ⟨13, 2, 0, 407349, 112006, 3285, 16384⟩
    (by decide) selected_cut_15979

theorem selected_cut_15980 : selected 8 ⟨407387, by decide⟩
    (prefixPartial 13 112007) = some ⟨13, 2, 0, 407387, 112007, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_112007_407387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112007 ⟨407387, by decide⟩ :=
  accepted_of_selected 13 112007 ⟨407387, by decide⟩ ⟨13, 2, 0, 407387, 112007, 1437, 16384⟩
    (by decide) selected_cut_15980

theorem unmarked_context_12_28001_407388 : frontier 9 ⟨407388, by decide⟩
    (prefixCache 12 28001) (prefixPartial 12 28001) = false := by
  decide +kernel

theorem node_context_12_28001_407388 : EJMOriginalGlobalDAGData.nodes 9 ⟨407388, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407274, by decide⟩,⟨407349, by decide⟩,⟨407387, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28001_407388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28001 ⟨407388, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28001
    ⟨407388, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407274, by decide⟩,⟨407349, by decide⟩,⟨407387, by decide⟩]) unmarked_context_12_28001_407388 node_context_12_28001_407388
  intro a
  fin_cases a
  · exact context_13_112004_3444
  · exact context_13_112005_407274
  · exact context_13_112006_407349
  · exact context_13_112007_407387

theorem selected_cut_15981 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112008) = some ⟨13, 1, 0, 3444, 112008, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112008_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112008 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112008 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112008, 1, 16384⟩
    (by decide) selected_cut_15981

theorem selected_cut_15982 : selected 8 ⟨407403, by decide⟩
    (prefixPartial 13 112009) = some ⟨13, 2, 0, 407403, 112009, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_112009_407403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112009 ⟨407403, by decide⟩ :=
  accepted_of_selected 13 112009 ⟨407403, by decide⟩ ⟨13, 2, 0, 407403, 112009, 1565, 16384⟩
    (by decide) selected_cut_15982

theorem selected_cut_15983 : selected 8 ⟨407433, by decide⟩
    (prefixPartial 13 112010) = some ⟨13, 2, 0, 407433, 112010, 2373, 16384⟩ := by
  decide +kernel

theorem context_13_112010_407433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112010 ⟨407433, by decide⟩ :=
  accepted_of_selected 13 112010 ⟨407433, by decide⟩ ⟨13, 2, 0, 407433, 112010, 2373, 16384⟩
    (by decide) selected_cut_15983

theorem selected_cut_15984 : selected 8 ⟨407446, by decide⟩
    (prefixPartial 13 112011) = some ⟨13, 2, 0, 407446, 112011, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_112011_407446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112011 ⟨407446, by decide⟩ :=
  accepted_of_selected 13 112011 ⟨407446, by decide⟩ ⟨13, 2, 0, 407446, 112011, 1209, 16384⟩
    (by decide) selected_cut_15984

theorem unmarked_context_12_28002_407447 : frontier 9 ⟨407447, by decide⟩
    (prefixCache 12 28002) (prefixPartial 12 28002) = false := by
  decide +kernel

theorem node_context_12_28002_407447 : EJMOriginalGlobalDAGData.nodes 9 ⟨407447, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407403, by decide⟩,⟨407433, by decide⟩,⟨407446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28002_407447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28002 ⟨407447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28002
    ⟨407447, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407403, by decide⟩,⟨407433, by decide⟩,⟨407446, by decide⟩]) unmarked_context_12_28002_407447 node_context_12_28002_407447
  intro a
  fin_cases a
  · exact context_13_112008_3444
  · exact context_13_112009_407403
  · exact context_13_112010_407433
  · exact context_13_112011_407446

theorem selected_cut_15985 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112012) = some ⟨13, 1, 0, 3444, 112012, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112012_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112012 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112012 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112012, 1, 16384⟩
    (by decide) selected_cut_15985

theorem selected_cut_15986 : selected 8 ⟨407474, by decide⟩
    (prefixPartial 13 112013) = some ⟨13, 2, 0, 407474, 112013, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_112013_407474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112013 ⟨407474, by decide⟩ :=
  accepted_of_selected 13 112013 ⟨407474, by decide⟩ ⟨13, 2, 0, 407474, 112013, 1721, 16384⟩
    (by decide) selected_cut_15986

theorem selected_cut_15987 : selected 8 ⟨407517, by decide⟩
    (prefixPartial 13 112014) = some ⟨13, 2, 0, 407517, 112014, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_112014_407517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112014 ⟨407517, by decide⟩ :=
  accepted_of_selected 13 112014 ⟨407517, by decide⟩ ⟨13, 2, 0, 407517, 112014, 2633, 16384⟩
    (by decide) selected_cut_15987

theorem selected_cut_15988 : selected 8 ⟨407536, by decide⟩
    (prefixPartial 13 112015) = some ⟨13, 2, 0, 407536, 112015, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_112015_407536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112015 ⟨407536, by decide⟩ :=
  accepted_of_selected 13 112015 ⟨407536, by decide⟩ ⟨13, 2, 0, 407536, 112015, 1261, 16384⟩
    (by decide) selected_cut_15988

theorem unmarked_context_12_28003_407537 : frontier 9 ⟨407537, by decide⟩
    (prefixCache 12 28003) (prefixPartial 12 28003) = false := by
  decide +kernel

theorem node_context_12_28003_407537 : EJMOriginalGlobalDAGData.nodes 9 ⟨407537, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407474, by decide⟩,⟨407517, by decide⟩,⟨407536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28003_407537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28003 ⟨407537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28003
    ⟨407537, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407474, by decide⟩,⟨407517, by decide⟩,⟨407536, by decide⟩]) unmarked_context_12_28003_407537 node_context_12_28003_407537
  intro a
  fin_cases a
  · exact context_13_112012_3444
  · exact context_13_112013_407474
  · exact context_13_112014_407517
  · exact context_13_112015_407536

theorem unmarked_context_11_7000_407538 : frontier 10 ⟨407538, by decide⟩
    (prefixCache 11 7000) (prefixPartial 11 7000) = false := by
  decide +kernel

theorem node_context_11_7000_407538 : EJMOriginalGlobalDAGData.nodes 10 ⟨407538, by decide⟩ =
    .split (coordinate 11) (![⟨407230, by decide⟩,⟨407388, by decide⟩,⟨407447, by decide⟩,⟨407537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7000_407538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7000 ⟨407538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7000
    ⟨407538, by decide⟩ (by decide) (![⟨407230, by decide⟩,⟨407388, by decide⟩,⟨407447, by decide⟩,⟨407537, by decide⟩]) unmarked_context_11_7000_407538 node_context_11_7000_407538
  intro a
  fin_cases a
  · exact context_12_28000_407230
  · exact context_12_28001_407388
  · exact context_12_28002_407447
  · exact context_12_28003_407537

theorem selected_cut_15989 : selected 9 ⟨407579, by decide⟩
    (prefixPartial 12 28004) = some ⟨12, 2, 0, 407579, 28004, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_28004_407579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28004 ⟨407579, by decide⟩ :=
  accepted_of_selected 12 28004 ⟨407579, by decide⟩ ⟨12, 2, 0, 407579, 28004, 3757, 65536⟩
    (by decide) selected_cut_15989

theorem selected_cut_15990 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 28005) = some ⟨12, 1, 0, 126884, 28005, 1, 65536⟩ := by
  decide +kernel

theorem context_12_28005_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28005 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 28005 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 28005, 1, 65536⟩
    (by decide) selected_cut_15990

theorem selected_cut_15991 : selected 9 ⟨407619, by decide⟩
    (prefixPartial 12 28006) = some ⟨12, 2, 0, 407619, 28006, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_28006_407619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28006 ⟨407619, by decide⟩ :=
  accepted_of_selected 12 28006 ⟨407619, by decide⟩ ⟨12, 2, 0, 407619, 28006, 4065, 65536⟩
    (by decide) selected_cut_15991

theorem selected_cut_15992 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112028) = some ⟨13, 1, 0, 3444, 112028, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112028_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112028 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112028 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112028, 1, 16384⟩
    (by decide) selected_cut_15992

theorem selected_cut_15993 : selected 8 ⟨407633, by decide⟩
    (prefixPartial 13 112029) = some ⟨13, 2, 0, 407633, 112029, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_112029_407633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112029 ⟨407633, by decide⟩ :=
  accepted_of_selected 13 112029 ⟨407633, by decide⟩ ⟨13, 2, 0, 407633, 112029, 1209, 16384⟩
    (by decide) selected_cut_15993

theorem selected_cut_15994 : selected 8 ⟨407656, by decide⟩
    (prefixPartial 13 112030) = some ⟨13, 2, 0, 407656, 112030, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_112030_407656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112030 ⟨407656, by decide⟩ :=
  accepted_of_selected 13 112030 ⟨407656, by decide⟩ ⟨13, 2, 0, 407656, 112030, 2093, 16384⟩
    (by decide) selected_cut_15994

theorem selected_cut_15995 : selected 8 ⟨407664, by decide⟩
    (prefixPartial 13 112031) = some ⟨13, 2, 0, 407664, 112031, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_112031_407664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112031 ⟨407664, by decide⟩ :=
  accepted_of_selected 13 112031 ⟨407664, by decide⟩ ⟨13, 2, 0, 407664, 112031, 1057, 16384⟩
    (by decide) selected_cut_15995

theorem unmarked_context_12_28007_407665 : frontier 9 ⟨407665, by decide⟩
    (prefixCache 12 28007) (prefixPartial 12 28007) = false := by
  decide +kernel

theorem node_context_12_28007_407665 : EJMOriginalGlobalDAGData.nodes 9 ⟨407665, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407633, by decide⟩,⟨407656, by decide⟩,⟨407664, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28007_407665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28007 ⟨407665, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28007
    ⟨407665, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407633, by decide⟩,⟨407656, by decide⟩,⟨407664, by decide⟩]) unmarked_context_12_28007_407665 node_context_12_28007_407665
  intro a
  fin_cases a
  · exact context_13_112028_3444
  · exact context_13_112029_407633
  · exact context_13_112030_407656
  · exact context_13_112031_407664

theorem unmarked_context_11_7001_407666 : frontier 10 ⟨407666, by decide⟩
    (prefixCache 11 7001) (prefixPartial 11 7001) = false := by
  decide +kernel

theorem node_context_11_7001_407666 : EJMOriginalGlobalDAGData.nodes 10 ⟨407666, by decide⟩ =
    .split (coordinate 11) (![⟨407579, by decide⟩,⟨126884, by decide⟩,⟨407619, by decide⟩,⟨407665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7001_407666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7001 ⟨407666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7001
    ⟨407666, by decide⟩ (by decide) (![⟨407579, by decide⟩,⟨126884, by decide⟩,⟨407619, by decide⟩,⟨407665, by decide⟩]) unmarked_context_11_7001_407666 node_context_11_7001_407666
  intro a
  fin_cases a
  · exact context_12_28004_407579
  · exact context_12_28005_126884
  · exact context_12_28006_407619
  · exact context_12_28007_407665

theorem selected_cut_15996 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112032) = some ⟨13, 1, 0, 3444, 112032, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112032_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112032 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112032 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112032, 1, 16384⟩
    (by decide) selected_cut_15996

theorem selected_cut_15997 : selected 8 ⟨407682, by decide⟩
    (prefixPartial 13 112033) = some ⟨13, 2, 0, 407682, 112033, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_112033_407682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112033 ⟨407682, by decide⟩ :=
  accepted_of_selected 13 112033 ⟨407682, by decide⟩ ⟨13, 2, 0, 407682, 112033, 1093, 16384⟩
    (by decide) selected_cut_15997

theorem selected_cut_15998 : selected 8 ⟨407708, by decide⟩
    (prefixPartial 13 112034) = some ⟨13, 2, 0, 407708, 112034, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_112034_407708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112034 ⟨407708, by decide⟩ :=
  accepted_of_selected 13 112034 ⟨407708, by decide⟩ ⟨13, 2, 0, 407708, 112034, 2041, 16384⟩
    (by decide) selected_cut_15998

theorem selected_cut_15999 : selected 8 ⟨407714, by decide⟩
    (prefixPartial 13 112035) = some ⟨13, 2, 0, 407714, 112035, 961, 16384⟩ := by
  decide +kernel

theorem context_13_112035_407714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112035 ⟨407714, by decide⟩ :=
  accepted_of_selected 13 112035 ⟨407714, by decide⟩ ⟨13, 2, 0, 407714, 112035, 961, 16384⟩
    (by decide) selected_cut_15999

theorem unmarked_context_12_28008_407715 : frontier 9 ⟨407715, by decide⟩
    (prefixCache 12 28008) (prefixPartial 12 28008) = false := by
  decide +kernel

theorem node_context_12_28008_407715 : EJMOriginalGlobalDAGData.nodes 9 ⟨407715, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407682, by decide⟩,⟨407708, by decide⟩,⟨407714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28008_407715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28008 ⟨407715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28008
    ⟨407715, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407682, by decide⟩,⟨407708, by decide⟩,⟨407714, by decide⟩]) unmarked_context_12_28008_407715 node_context_12_28008_407715
  intro a
  fin_cases a
  · exact context_13_112032_3444
  · exact context_13_112033_407682
  · exact context_13_112034_407708
  · exact context_13_112035_407714

theorem selected_cut_16000 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112036) = some ⟨13, 1, 0, 3444, 112036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112036, 1, 16384⟩
    (by decide) selected_cut_16000

theorem selected_cut_16001 : selected 8 ⟨407740, by decide⟩
    (prefixPartial 13 112037) = some ⟨13, 2, 0, 407740, 112037, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_112037_407740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112037 ⟨407740, by decide⟩ :=
  accepted_of_selected 13 112037 ⟨407740, by decide⟩ ⟨13, 2, 0, 407740, 112037, 1401, 16384⟩
    (by decide) selected_cut_16001

theorem selected_cut_16002 : selected 8 ⟨407789, by decide⟩
    (prefixPartial 13 112038) = some ⟨13, 2, 0, 407789, 112038, 2865, 16384⟩ := by
  decide +kernel

theorem context_13_112038_407789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112038 ⟨407789, by decide⟩ :=
  accepted_of_selected 13 112038 ⟨407789, by decide⟩ ⟨13, 2, 0, 407789, 112038, 2865, 16384⟩
    (by decide) selected_cut_16002

theorem selected_cut_16003 : selected 8 ⟨407808, by decide⟩
    (prefixPartial 13 112039) = some ⟨13, 2, 0, 407808, 112039, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_112039_407808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112039 ⟨407808, by decide⟩ :=
  accepted_of_selected 13 112039 ⟨407808, by decide⟩ ⟨13, 2, 0, 407808, 112039, 1313, 16384⟩
    (by decide) selected_cut_16003

theorem unmarked_context_12_28009_407809 : frontier 9 ⟨407809, by decide⟩
    (prefixCache 12 28009) (prefixPartial 12 28009) = false := by
  decide +kernel

theorem node_context_12_28009_407809 : EJMOriginalGlobalDAGData.nodes 9 ⟨407809, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407740, by decide⟩,⟨407789, by decide⟩,⟨407808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28009_407809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28009 ⟨407809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28009
    ⟨407809, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407740, by decide⟩,⟨407789, by decide⟩,⟨407808, by decide⟩]) unmarked_context_12_28009_407809 node_context_12_28009_407809
  intro a
  fin_cases a
  · exact context_13_112036_3444
  · exact context_13_112037_407740
  · exact context_13_112038_407789
  · exact context_13_112039_407808

theorem selected_cut_16004 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112040) = some ⟨13, 1, 0, 3444, 112040, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112040_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112040 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112040 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112040, 1, 16384⟩
    (by decide) selected_cut_16004

theorem selected_cut_16005 : selected 8 ⟨407818, by decide⟩
    (prefixPartial 13 112041) = some ⟨13, 2, 0, 407818, 112041, 945, 16384⟩ := by
  decide +kernel

theorem context_13_112041_407818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112041 ⟨407818, by decide⟩ :=
  accepted_of_selected 13 112041 ⟨407818, by decide⟩ ⟨13, 2, 0, 407818, 112041, 945, 16384⟩
    (by decide) selected_cut_16005

theorem selected_cut_16006 : selected 8 ⟨407841, by decide⟩
    (prefixPartial 13 112042) = some ⟨13, 2, 0, 407841, 112042, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_112042_407841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112042 ⟨407841, by decide⟩ :=
  accepted_of_selected 13 112042 ⟨407841, by decide⟩ ⟨13, 2, 0, 407841, 112042, 2121, 16384⟩
    (by decide) selected_cut_16006

theorem selected_cut_16007 : selected 8 ⟨407850, by decide⟩
    (prefixPartial 13 112043) = some ⟨13, 2, 0, 407850, 112043, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_112043_407850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112043 ⟨407850, by decide⟩ :=
  accepted_of_selected 13 112043 ⟨407850, by decide⟩ ⟨13, 2, 0, 407850, 112043, 1065, 16384⟩
    (by decide) selected_cut_16007

theorem unmarked_context_12_28010_407851 : frontier 9 ⟨407851, by decide⟩
    (prefixCache 12 28010) (prefixPartial 12 28010) = false := by
  decide +kernel

theorem node_context_12_28010_407851 : EJMOriginalGlobalDAGData.nodes 9 ⟨407851, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407818, by decide⟩,⟨407841, by decide⟩,⟨407850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28010_407851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28010 ⟨407851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28010
    ⟨407851, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407818, by decide⟩,⟨407841, by decide⟩,⟨407850, by decide⟩]) unmarked_context_12_28010_407851 node_context_12_28010_407851
  intro a
  fin_cases a
  · exact context_13_112040_3444
  · exact context_13_112041_407818
  · exact context_13_112042_407841
  · exact context_13_112043_407850

theorem selected_cut_16008 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112044) = some ⟨13, 1, 0, 3444, 112044, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112044_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112044 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112044 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112044, 1, 16384⟩
    (by decide) selected_cut_16008

theorem selected_cut_16009 : selected 8 ⟨407870, by decide⟩
    (prefixPartial 13 112045) = some ⟨13, 2, 0, 407870, 112045, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_112045_407870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112045 ⟨407870, by decide⟩ :=
  accepted_of_selected 13 112045 ⟨407870, by decide⟩ ⟨13, 2, 0, 407870, 112045, 1053, 16384⟩
    (by decide) selected_cut_16009

theorem selected_cut_16010 : selected 8 ⟨407893, by decide⟩
    (prefixPartial 13 112046) = some ⟨13, 2, 0, 407893, 112046, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_112046_407893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112046 ⟨407893, by decide⟩ :=
  accepted_of_selected 13 112046 ⟨407893, by decide⟩ ⟨13, 2, 0, 407893, 112046, 2141, 16384⟩
    (by decide) selected_cut_16010

theorem selected_cut_16011 : selected 8 ⟨407902, by decide⟩
    (prefixPartial 13 112047) = some ⟨13, 2, 0, 407902, 112047, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_112047_407902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112047 ⟨407902, by decide⟩ :=
  accepted_of_selected 13 112047 ⟨407902, by decide⟩ ⟨13, 2, 0, 407902, 112047, 1117, 16384⟩
    (by decide) selected_cut_16011

theorem unmarked_context_12_28011_407903 : frontier 9 ⟨407903, by decide⟩
    (prefixCache 12 28011) (prefixPartial 12 28011) = false := by
  decide +kernel

theorem node_context_12_28011_407903 : EJMOriginalGlobalDAGData.nodes 9 ⟨407903, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407870, by decide⟩,⟨407893, by decide⟩,⟨407902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28011_407903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28011 ⟨407903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28011
    ⟨407903, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407870, by decide⟩,⟨407893, by decide⟩,⟨407902, by decide⟩]) unmarked_context_12_28011_407903 node_context_12_28011_407903
  intro a
  fin_cases a
  · exact context_13_112044_3444
  · exact context_13_112045_407870
  · exact context_13_112046_407893
  · exact context_13_112047_407902

theorem unmarked_context_11_7002_407904 : frontier 10 ⟨407904, by decide⟩
    (prefixCache 11 7002) (prefixPartial 11 7002) = false := by
  decide +kernel

theorem node_context_11_7002_407904 : EJMOriginalGlobalDAGData.nodes 10 ⟨407904, by decide⟩ =
    .split (coordinate 11) (![⟨407715, by decide⟩,⟨407809, by decide⟩,⟨407851, by decide⟩,⟨407903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7002_407904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7002 ⟨407904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7002
    ⟨407904, by decide⟩ (by decide) (![⟨407715, by decide⟩,⟨407809, by decide⟩,⟨407851, by decide⟩,⟨407903, by decide⟩]) unmarked_context_11_7002_407904 node_context_11_7002_407904
  intro a
  fin_cases a
  · exact context_12_28008_407715
  · exact context_12_28009_407809
  · exact context_12_28010_407851
  · exact context_12_28011_407903

theorem selected_cut_16012 : selected 9 ⟨407938, by decide⟩
    (prefixPartial 12 28012) = some ⟨12, 2, 0, 407938, 28012, 3913, 65536⟩ := by
  decide +kernel

theorem context_12_28012_407938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28012 ⟨407938, by decide⟩ :=
  accepted_of_selected 12 28012 ⟨407938, by decide⟩ ⟨12, 2, 0, 407938, 28012, 3913, 65536⟩
    (by decide) selected_cut_16012

theorem selected_cut_16013 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112052) = some ⟨13, 1, 0, 3444, 112052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112052, 1, 16384⟩
    (by decide) selected_cut_16013

theorem selected_cut_16014 : selected 8 ⟨407964, by decide⟩
    (prefixPartial 13 112053) = some ⟨13, 2, 0, 407964, 112053, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_112053_407964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112053 ⟨407964, by decide⟩ :=
  accepted_of_selected 13 112053 ⟨407964, by decide⟩ ⟨13, 2, 0, 407964, 112053, 1245, 16384⟩
    (by decide) selected_cut_16014

theorem selected_cut_16015 : selected 8 ⟨408002, by decide⟩
    (prefixPartial 13 112054) = some ⟨13, 2, 0, 408002, 112054, 2641, 16384⟩ := by
  decide +kernel

theorem context_13_112054_408002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112054 ⟨408002, by decide⟩ :=
  accepted_of_selected 13 112054 ⟨408002, by decide⟩ ⟨13, 2, 0, 408002, 112054, 2641, 16384⟩
    (by decide) selected_cut_16015

theorem selected_cut_16016 : selected 8 ⟨408024, by decide⟩
    (prefixPartial 13 112055) = some ⟨13, 2, 0, 408024, 112055, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_112055_408024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112055 ⟨408024, by decide⟩ :=
  accepted_of_selected 13 112055 ⟨408024, by decide⟩ ⟨13, 2, 0, 408024, 112055, 1361, 16384⟩
    (by decide) selected_cut_16016

theorem unmarked_context_12_28013_408025 : frontier 9 ⟨408025, by decide⟩
    (prefixCache 12 28013) (prefixPartial 12 28013) = false := by
  decide +kernel

theorem node_context_12_28013_408025 : EJMOriginalGlobalDAGData.nodes 9 ⟨408025, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨407964, by decide⟩,⟨408002, by decide⟩,⟨408024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28013_408025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28013 ⟨408025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28013
    ⟨408025, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨407964, by decide⟩,⟨408002, by decide⟩,⟨408024, by decide⟩]) unmarked_context_12_28013_408025 node_context_12_28013_408025
  intro a
  fin_cases a
  · exact context_13_112052_3444
  · exact context_13_112053_407964
  · exact context_13_112054_408002
  · exact context_13_112055_408024

theorem selected_cut_16017 : selected 9 ⟨408063, by decide⟩
    (prefixPartial 12 28014) = some ⟨12, 2, 0, 408063, 28014, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_28014_408063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28014 ⟨408063, by decide⟩ :=
  accepted_of_selected 12 28014 ⟨408063, by decide⟩ ⟨12, 2, 0, 408063, 28014, 4017, 65536⟩
    (by decide) selected_cut_16017

theorem selected_cut_16018 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112060) = some ⟨13, 1, 0, 3444, 112060, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112060_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112060 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112060 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112060, 1, 16384⟩
    (by decide) selected_cut_16018

theorem selected_cut_16019 : selected 8 ⟨408070, by decide⟩
    (prefixPartial 13 112061) = some ⟨13, 2, 0, 408070, 112061, 817, 16384⟩ := by
  decide +kernel

theorem context_13_112061_408070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112061 ⟨408070, by decide⟩ :=
  accepted_of_selected 13 112061 ⟨408070, by decide⟩ ⟨13, 2, 0, 408070, 112061, 817, 16384⟩
    (by decide) selected_cut_16019

theorem selected_cut_16020 : selected 8 ⟨408087, by decide⟩
    (prefixPartial 13 112062) = some ⟨13, 2, 0, 408087, 112062, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_112062_408087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112062 ⟨408087, by decide⟩ :=
  accepted_of_selected 13 112062 ⟨408087, by decide⟩ ⟨13, 2, 0, 408087, 112062, 2097, 16384⟩
    (by decide) selected_cut_16020

theorem selected_cut_16021 : selected 8 ⟨408100, by decide⟩
    (prefixPartial 13 112063) = some ⟨13, 2, 0, 408100, 112063, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_112063_408100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112063 ⟨408100, by decide⟩ :=
  accepted_of_selected 13 112063 ⟨408100, by decide⟩ ⟨13, 2, 0, 408100, 112063, 1293, 16384⟩
    (by decide) selected_cut_16021

theorem unmarked_context_12_28015_408101 : frontier 9 ⟨408101, by decide⟩
    (prefixCache 12 28015) (prefixPartial 12 28015) = false := by
  decide +kernel

theorem node_context_12_28015_408101 : EJMOriginalGlobalDAGData.nodes 9 ⟨408101, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨408070, by decide⟩,⟨408087, by decide⟩,⟨408100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28015_408101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28015 ⟨408101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28015
    ⟨408101, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨408070, by decide⟩,⟨408087, by decide⟩,⟨408100, by decide⟩]) unmarked_context_12_28015_408101 node_context_12_28015_408101
  intro a
  fin_cases a
  · exact context_13_112060_3444
  · exact context_13_112061_408070
  · exact context_13_112062_408087
  · exact context_13_112063_408100

theorem unmarked_context_11_7003_408102 : frontier 10 ⟨408102, by decide⟩
    (prefixCache 11 7003) (prefixPartial 11 7003) = false := by
  decide +kernel

theorem node_context_11_7003_408102 : EJMOriginalGlobalDAGData.nodes 10 ⟨408102, by decide⟩ =
    .split (coordinate 11) (![⟨407938, by decide⟩,⟨408025, by decide⟩,⟨408063, by decide⟩,⟨408101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7003_408102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7003 ⟨408102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7003
    ⟨408102, by decide⟩ (by decide) (![⟨407938, by decide⟩,⟨408025, by decide⟩,⟨408063, by decide⟩,⟨408101, by decide⟩]) unmarked_context_11_7003_408102 node_context_11_7003_408102
  intro a
  fin_cases a
  · exact context_12_28012_407938
  · exact context_12_28013_408025
  · exact context_12_28014_408063
  · exact context_12_28015_408101

theorem unmarked_context_10_1750_408103 : frontier 11 ⟨408103, by decide⟩
    (prefixCache 10 1750) (prefixPartial 10 1750) = false := by
  decide +kernel

theorem node_context_10_1750_408103 : EJMOriginalGlobalDAGData.nodes 11 ⟨408103, by decide⟩ =
    .split (coordinate 10) (![⟨407538, by decide⟩,⟨407666, by decide⟩,⟨407904, by decide⟩,⟨408102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1750_408103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1750 ⟨408103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1750
    ⟨408103, by decide⟩ (by decide) (![⟨407538, by decide⟩,⟨407666, by decide⟩,⟨407904, by decide⟩,⟨408102, by decide⟩]) unmarked_context_10_1750_408103 node_context_10_1750_408103
  intro a
  fin_cases a
  · exact context_11_7000_407538
  · exact context_11_7001_407666
  · exact context_11_7002_407904
  · exact context_11_7003_408102

theorem selected_cut_16022 : selected 9 ⟨408145, by decide⟩
    (prefixPartial 12 28016) = some ⟨12, 2, 0, 408145, 28016, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_28016_408145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28016 ⟨408145, by decide⟩ :=
  accepted_of_selected 12 28016 ⟨408145, by decide⟩ ⟨12, 2, 0, 408145, 28016, 3777, 65536⟩
    (by decide) selected_cut_16022

theorem selected_cut_16023 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112068) = some ⟨13, 1, 0, 3444, 112068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112068, 1, 16384⟩
    (by decide) selected_cut_16023

theorem selected_cut_16024 : selected 8 ⟨408169, by decide⟩
    (prefixPartial 13 112069) = some ⟨13, 2, 0, 408169, 112069, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_112069_408169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112069 ⟨408169, by decide⟩ :=
  accepted_of_selected 13 112069 ⟨408169, by decide⟩ ⟨13, 2, 0, 408169, 112069, 1073, 16384⟩
    (by decide) selected_cut_16024

theorem selected_cut_16025 : selected 8 ⟨408237, by decide⟩
    (prefixPartial 13 112070) = some ⟨13, 2, 0, 408237, 112070, 3293, 16384⟩ := by
  decide +kernel

theorem context_13_112070_408237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112070 ⟨408237, by decide⟩ :=
  accepted_of_selected 13 112070 ⟨408237, by decide⟩ ⟨13, 2, 0, 408237, 112070, 3293, 16384⟩
    (by decide) selected_cut_16025

theorem selected_cut_16026 : selected 8 ⟨408251, by decide⟩
    (prefixPartial 13 112071) = some ⟨13, 2, 0, 408251, 112071, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_112071_408251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112071 ⟨408251, by decide⟩ :=
  accepted_of_selected 13 112071 ⟨408251, by decide⟩ ⟨13, 2, 0, 408251, 112071, 1161, 16384⟩
    (by decide) selected_cut_16026

theorem unmarked_context_12_28017_408252 : frontier 9 ⟨408252, by decide⟩
    (prefixCache 12 28017) (prefixPartial 12 28017) = false := by
  decide +kernel

theorem node_context_12_28017_408252 : EJMOriginalGlobalDAGData.nodes 9 ⟨408252, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨408169, by decide⟩,⟨408237, by decide⟩,⟨408251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28017_408252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28017 ⟨408252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28017
    ⟨408252, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨408169, by decide⟩,⟨408237, by decide⟩,⟨408251, by decide⟩]) unmarked_context_12_28017_408252 node_context_12_28017_408252
  intro a
  fin_cases a
  · exact context_13_112068_3444
  · exact context_13_112069_408169
  · exact context_13_112070_408237
  · exact context_13_112071_408251

theorem selected_cut_16027 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112072) = some ⟨13, 1, 0, 3444, 112072, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112072_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112072 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112072 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112072, 1, 16384⟩
    (by decide) selected_cut_16027

theorem selected_cut_16028 : selected 8 ⟨408266, by decide⟩
    (prefixPartial 13 112073) = some ⟨13, 2, 0, 408266, 112073, 757, 16384⟩ := by
  decide +kernel

theorem context_13_112073_408266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112073 ⟨408266, by decide⟩ :=
  accepted_of_selected 13 112073 ⟨408266, by decide⟩ ⟨13, 2, 0, 408266, 112073, 757, 16384⟩
    (by decide) selected_cut_16028

theorem selected_cut_16029 : selected 8 ⟨408300, by decide⟩
    (prefixPartial 13 112074) = some ⟨13, 2, 0, 408300, 112074, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_112074_408300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112074 ⟨408300, by decide⟩ :=
  accepted_of_selected 13 112074 ⟨408300, by decide⟩ ⟨13, 2, 0, 408300, 112074, 2505, 16384⟩
    (by decide) selected_cut_16029

theorem selected_cut_16030 : selected 8 ⟨408306, by decide⟩
    (prefixPartial 13 112075) = some ⟨13, 2, 0, 408306, 112075, 969, 16384⟩ := by
  decide +kernel

theorem context_13_112075_408306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112075 ⟨408306, by decide⟩ :=
  accepted_of_selected 13 112075 ⟨408306, by decide⟩ ⟨13, 2, 0, 408306, 112075, 969, 16384⟩
    (by decide) selected_cut_16030

theorem unmarked_context_12_28018_408307 : frontier 9 ⟨408307, by decide⟩
    (prefixCache 12 28018) (prefixPartial 12 28018) = false := by
  decide +kernel

theorem node_context_12_28018_408307 : EJMOriginalGlobalDAGData.nodes 9 ⟨408307, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨408266, by decide⟩,⟨408300, by decide⟩,⟨408306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28018_408307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28018 ⟨408307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28018
    ⟨408307, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨408266, by decide⟩,⟨408300, by decide⟩,⟨408306, by decide⟩]) unmarked_context_12_28018_408307 node_context_12_28018_408307
  intro a
  fin_cases a
  · exact context_13_112072_3444
  · exact context_13_112073_408266
  · exact context_13_112074_408300
  · exact context_13_112075_408306

theorem selected_cut_16031 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 112076) = some ⟨13, 1, 0, 3444, 112076, 1, 16384⟩ := by
  decide +kernel

theorem context_13_112076_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112076 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 112076 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 112076, 1, 16384⟩
    (by decide) selected_cut_16031

theorem selected_cut_16032 : selected 8 ⟨408323, by decide⟩
    (prefixPartial 13 112077) = some ⟨13, 2, 0, 408323, 112077, 749, 16384⟩ := by
  decide +kernel

theorem context_13_112077_408323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112077 ⟨408323, by decide⟩ :=
  accepted_of_selected 13 112077 ⟨408323, by decide⟩ ⟨13, 2, 0, 408323, 112077, 749, 16384⟩
    (by decide) selected_cut_16032

theorem selected_cut_16033 : selected 8 ⟨408367, by decide⟩
    (prefixPartial 13 112078) = some ⟨13, 2, 0, 408367, 112078, 2669, 16384⟩ := by
  decide +kernel

theorem context_13_112078_408367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112078 ⟨408367, by decide⟩ :=
  accepted_of_selected 13 112078 ⟨408367, by decide⟩ ⟨13, 2, 0, 408367, 112078, 2669, 16384⟩
    (by decide) selected_cut_16033

theorem selected_cut_16034 : selected 8 ⟨408375, by decide⟩
    (prefixPartial 13 112079) = some ⟨13, 2, 0, 408375, 112079, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_112079_408375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112079 ⟨408375, by decide⟩ :=
  accepted_of_selected 13 112079 ⟨408375, by decide⟩ ⟨13, 2, 0, 408375, 112079, 1005, 16384⟩
    (by decide) selected_cut_16034

theorem unmarked_context_12_28019_408376 : frontier 9 ⟨408376, by decide⟩
    (prefixCache 12 28019) (prefixPartial 12 28019) = false := by
  decide +kernel

theorem node_context_12_28019_408376 : EJMOriginalGlobalDAGData.nodes 9 ⟨408376, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨408323, by decide⟩,⟨408367, by decide⟩,⟨408375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28019_408376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28019 ⟨408376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28019
    ⟨408376, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨408323, by decide⟩,⟨408367, by decide⟩,⟨408375, by decide⟩]) unmarked_context_12_28019_408376 node_context_12_28019_408376
  intro a
  fin_cases a
  · exact context_13_112076_3444
  · exact context_13_112077_408323
  · exact context_13_112078_408367
  · exact context_13_112079_408375

theorem unmarked_context_11_7004_408377 : frontier 10 ⟨408377, by decide⟩
    (prefixCache 11 7004) (prefixPartial 11 7004) = false := by
  decide +kernel

theorem node_context_11_7004_408377 : EJMOriginalGlobalDAGData.nodes 10 ⟨408377, by decide⟩ =
    .split (coordinate 11) (![⟨408145, by decide⟩,⟨408252, by decide⟩,⟨408307, by decide⟩,⟨408376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7004_408377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7004 ⟨408377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7004
    ⟨408377, by decide⟩ (by decide) (![⟨408145, by decide⟩,⟨408252, by decide⟩,⟨408307, by decide⟩,⟨408376, by decide⟩]) unmarked_context_11_7004_408377 node_context_11_7004_408377
  intro a
  fin_cases a
  · exact context_12_28016_408145
  · exact context_12_28017_408252
  · exact context_12_28018_408307
  · exact context_12_28019_408376

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
