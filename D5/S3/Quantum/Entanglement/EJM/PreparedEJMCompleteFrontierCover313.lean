/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover312
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_30053 : selected 8 ⟨758774, by decide⟩
    (prefixPartial 13 375983) = some ⟨13, 2, 0, 758774, 375983, 653, 16384⟩ := by
  decide +kernel

theorem context_13_375983_758774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375983 ⟨758774, by decide⟩ :=
  accepted_of_selected 13 375983 ⟨758774, by decide⟩ ⟨13, 2, 0, 758774, 375983, 653, 16384⟩
    (by decide) selected_cut_30053

theorem unmarked_context_12_93995_758775 : frontier 9 ⟨758775, by decide⟩
    (prefixCache 12 93995) (prefixPartial 12 93995) = false := by
  decide +kernel

theorem node_context_12_93995_758775 : EJMOriginalGlobalDAGData.nodes 9 ⟨758775, by decide⟩ =
    .split (coordinate 12) (![⟨758712, by decide⟩,⟨758747, by decide⟩,⟨758769, by decide⟩,⟨758774, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93995_758775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93995 ⟨758775, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93995
    ⟨758775, by decide⟩ (by decide) (![⟨758712, by decide⟩,⟨758747, by decide⟩,⟨758769, by decide⟩,⟨758774, by decide⟩]) unmarked_context_12_93995_758775 node_context_12_93995_758775
  intro a
  fin_cases a
  · exact context_13_375980_758712
  · exact context_13_375981_758747
  · exact context_13_375982_758769
  · exact context_13_375983_758774

theorem unmarked_context_11_23498_758776 : frontier 10 ⟨758776, by decide⟩
    (prefixCache 11 23498) (prefixPartial 11 23498) = false := by
  decide +kernel

theorem node_context_11_23498_758776 : EJMOriginalGlobalDAGData.nodes 10 ⟨758776, by decide⟩ =
    .split (coordinate 11) (![⟨758564, by decide⟩,⟨758636, by decide⟩,⟨758699, by decide⟩,⟨758775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23498_758776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23498 ⟨758776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23498
    ⟨758776, by decide⟩ (by decide) (![⟨758564, by decide⟩,⟨758636, by decide⟩,⟨758699, by decide⟩,⟨758775, by decide⟩]) unmarked_context_11_23498_758776 node_context_11_23498_758776
  intro a
  fin_cases a
  · exact context_12_93992_758564
  · exact context_12_93993_758636
  · exact context_12_93994_758699
  · exact context_12_93995_758775

theorem selected_cut_30054 : selected 8 ⟨758787, by decide⟩
    (prefixPartial 13 375984) = some ⟨13, 2, 0, 758787, 375984, 717, 16384⟩ := by
  decide +kernel

theorem context_13_375984_758787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375984 ⟨758787, by decide⟩ :=
  accepted_of_selected 13 375984 ⟨758787, by decide⟩ ⟨13, 2, 0, 758787, 375984, 717, 16384⟩
    (by decide) selected_cut_30054

theorem selected_cut_30055 : selected 8 ⟨758812, by decide⟩
    (prefixPartial 13 375985) = some ⟨13, 2, 0, 758812, 375985, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_375985_758812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375985 ⟨758812, by decide⟩ :=
  accepted_of_selected 13 375985 ⟨758812, by decide⟩ ⟨13, 2, 0, 758812, 375985, 1745, 16384⟩
    (by decide) selected_cut_30055

theorem selected_cut_30056 : selected 8 ⟨758829, by decide⟩
    (prefixPartial 13 375986) = some ⟨13, 2, 0, 758829, 375986, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_375986_758829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375986 ⟨758829, by decide⟩ :=
  accepted_of_selected 13 375986 ⟨758829, by decide⟩ ⟨13, 2, 0, 758829, 375986, 1097, 16384⟩
    (by decide) selected_cut_30056

theorem selected_cut_30057 : selected 8 ⟨758837, by decide⟩
    (prefixPartial 13 375987) = some ⟨13, 2, 0, 758837, 375987, 629, 16384⟩ := by
  decide +kernel

theorem context_13_375987_758837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375987 ⟨758837, by decide⟩ :=
  accepted_of_selected 13 375987 ⟨758837, by decide⟩ ⟨13, 2, 0, 758837, 375987, 629, 16384⟩
    (by decide) selected_cut_30057

theorem unmarked_context_12_93996_758838 : frontier 9 ⟨758838, by decide⟩
    (prefixCache 12 93996) (prefixPartial 12 93996) = false := by
  decide +kernel

theorem node_context_12_93996_758838 : EJMOriginalGlobalDAGData.nodes 9 ⟨758838, by decide⟩ =
    .split (coordinate 12) (![⟨758787, by decide⟩,⟨758812, by decide⟩,⟨758829, by decide⟩,⟨758837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93996_758838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93996 ⟨758838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93996
    ⟨758838, by decide⟩ (by decide) (![⟨758787, by decide⟩,⟨758812, by decide⟩,⟨758829, by decide⟩,⟨758837, by decide⟩]) unmarked_context_12_93996_758838 node_context_12_93996_758838
  intro a
  fin_cases a
  · exact context_13_375984_758787
  · exact context_13_375985_758812
  · exact context_13_375986_758829
  · exact context_13_375987_758837

theorem selected_cut_30058 : selected 8 ⟨758851, by decide⟩
    (prefixPartial 13 375988) = some ⟨13, 2, 0, 758851, 375988, 753, 16384⟩ := by
  decide +kernel

theorem context_13_375988_758851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375988 ⟨758851, by decide⟩ :=
  accepted_of_selected 13 375988 ⟨758851, by decide⟩ ⟨13, 2, 0, 758851, 375988, 753, 16384⟩
    (by decide) selected_cut_30058

theorem selected_cut_30059 : selected 8 ⟨758874, by decide⟩
    (prefixPartial 13 375989) = some ⟨13, 2, 0, 758874, 375989, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_375989_758874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375989 ⟨758874, by decide⟩ :=
  accepted_of_selected 13 375989 ⟨758874, by decide⟩ ⟨13, 2, 0, 758874, 375989, 1589, 16384⟩
    (by decide) selected_cut_30059

theorem selected_cut_30060 : selected 8 ⟨758890, by decide⟩
    (prefixPartial 13 375990) = some ⟨13, 2, 0, 758890, 375990, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_375990_758890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375990 ⟨758890, by decide⟩ :=
  accepted_of_selected 13 375990 ⟨758890, by decide⟩ ⟨13, 2, 0, 758890, 375990, 1389, 16384⟩
    (by decide) selected_cut_30060

theorem selected_cut_30061 : selected 8 ⟨758897, by decide⟩
    (prefixPartial 13 375991) = some ⟨13, 2, 0, 758897, 375991, 509, 16384⟩ := by
  decide +kernel

theorem context_13_375991_758897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375991 ⟨758897, by decide⟩ :=
  accepted_of_selected 13 375991 ⟨758897, by decide⟩ ⟨13, 2, 0, 758897, 375991, 509, 16384⟩
    (by decide) selected_cut_30061

theorem unmarked_context_12_93997_758898 : frontier 9 ⟨758898, by decide⟩
    (prefixCache 12 93997) (prefixPartial 12 93997) = false := by
  decide +kernel

theorem node_context_12_93997_758898 : EJMOriginalGlobalDAGData.nodes 9 ⟨758898, by decide⟩ =
    .split (coordinate 12) (![⟨758851, by decide⟩,⟨758874, by decide⟩,⟨758890, by decide⟩,⟨758897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93997_758898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93997 ⟨758898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93997
    ⟨758898, by decide⟩ (by decide) (![⟨758851, by decide⟩,⟨758874, by decide⟩,⟨758890, by decide⟩,⟨758897, by decide⟩]) unmarked_context_12_93997_758898 node_context_12_93997_758898
  intro a
  fin_cases a
  · exact context_13_375988_758851
  · exact context_13_375989_758874
  · exact context_13_375990_758890
  · exact context_13_375991_758897

theorem selected_cut_30062 : selected 8 ⟨758908, by decide⟩
    (prefixPartial 13 375992) = some ⟨13, 2, 0, 758908, 375992, 621, 16384⟩ := by
  decide +kernel

theorem context_13_375992_758908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375992 ⟨758908, by decide⟩ :=
  accepted_of_selected 13 375992 ⟨758908, by decide⟩ ⟨13, 2, 0, 758908, 375992, 621, 16384⟩
    (by decide) selected_cut_30062

theorem selected_cut_30063 : selected 8 ⟨758943, by decide⟩
    (prefixPartial 13 375993) = some ⟨13, 2, 0, 758943, 375993, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_375993_758943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375993 ⟨758943, by decide⟩ :=
  accepted_of_selected 13 375993 ⟨758943, by decide⟩ ⟨13, 2, 0, 758943, 375993, 1881, 16384⟩
    (by decide) selected_cut_30063

theorem selected_cut_30064 : selected 8 ⟨758958, by decide⟩
    (prefixPartial 13 375994) = some ⟨13, 2, 0, 758958, 375994, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_375994_758958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375994 ⟨758958, by decide⟩ :=
  accepted_of_selected 13 375994 ⟨758958, by decide⟩ ⟨13, 2, 0, 758958, 375994, 1305, 16384⟩
    (by decide) selected_cut_30064

theorem selected_cut_30065 : selected 8 ⟨758966, by decide⟩
    (prefixPartial 13 375995) = some ⟨13, 2, 0, 758966, 375995, 709, 16384⟩ := by
  decide +kernel

theorem context_13_375995_758966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375995 ⟨758966, by decide⟩ :=
  accepted_of_selected 13 375995 ⟨758966, by decide⟩ ⟨13, 2, 0, 758966, 375995, 709, 16384⟩
    (by decide) selected_cut_30065

theorem unmarked_context_12_93998_758967 : frontier 9 ⟨758967, by decide⟩
    (prefixCache 12 93998) (prefixPartial 12 93998) = false := by
  decide +kernel

theorem node_context_12_93998_758967 : EJMOriginalGlobalDAGData.nodes 9 ⟨758967, by decide⟩ =
    .split (coordinate 12) (![⟨758908, by decide⟩,⟨758943, by decide⟩,⟨758958, by decide⟩,⟨758966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93998_758967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93998 ⟨758967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93998
    ⟨758967, by decide⟩ (by decide) (![⟨758908, by decide⟩,⟨758943, by decide⟩,⟨758958, by decide⟩,⟨758966, by decide⟩]) unmarked_context_12_93998_758967 node_context_12_93998_758967
  intro a
  fin_cases a
  · exact context_13_375992_758908
  · exact context_13_375993_758943
  · exact context_13_375994_758958
  · exact context_13_375995_758966

theorem selected_cut_30066 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 93999) = some ⟨12, 1, 0, 758968, 93999, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93999_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93999 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 93999 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 93999, 1, 65536⟩
    (by decide) selected_cut_30066

theorem unmarked_context_11_23499_758969 : frontier 10 ⟨758969, by decide⟩
    (prefixCache 11 23499) (prefixPartial 11 23499) = false := by
  decide +kernel

theorem node_context_11_23499_758969 : EJMOriginalGlobalDAGData.nodes 10 ⟨758969, by decide⟩ =
    .split (coordinate 11) (![⟨758838, by decide⟩,⟨758898, by decide⟩,⟨758967, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23499_758969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23499 ⟨758969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23499
    ⟨758969, by decide⟩ (by decide) (![⟨758838, by decide⟩,⟨758898, by decide⟩,⟨758967, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_23499_758969 node_context_11_23499_758969
  intro a
  fin_cases a
  · exact context_12_93996_758838
  · exact context_12_93997_758898
  · exact context_12_93998_758967
  · exact context_12_93999_758968

theorem unmarked_context_10_5874_758970 : frontier 11 ⟨758970, by decide⟩
    (prefixCache 10 5874) (prefixPartial 10 5874) = false := by
  decide +kernel

theorem node_context_10_5874_758970 : EJMOriginalGlobalDAGData.nodes 11 ⟨758970, by decide⟩ =
    .split (coordinate 10) (![⟨758188, by decide⟩,⟨758485, by decide⟩,⟨758776, by decide⟩,⟨758969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5874_758970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5874 ⟨758970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5874
    ⟨758970, by decide⟩ (by decide) (![⟨758188, by decide⟩,⟨758485, by decide⟩,⟨758776, by decide⟩,⟨758969, by decide⟩]) unmarked_context_10_5874_758970 node_context_10_5874_758970
  intro a
  fin_cases a
  · exact context_11_23496_758188
  · exact context_11_23497_758485
  · exact context_11_23498_758776
  · exact context_11_23499_758969

theorem selected_cut_30067 : selected 8 ⟨758981, by decide⟩
    (prefixPartial 13 376000) = some ⟨13, 2, 0, 758981, 376000, 645, 16384⟩ := by
  decide +kernel

theorem context_13_376000_758981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376000 ⟨758981, by decide⟩ :=
  accepted_of_selected 13 376000 ⟨758981, by decide⟩ ⟨13, 2, 0, 758981, 376000, 645, 16384⟩
    (by decide) selected_cut_30067

theorem selected_cut_30068 : selected 8 ⟨759019, by decide⟩
    (prefixPartial 13 376001) = some ⟨13, 2, 0, 759019, 376001, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_376001_759019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376001 ⟨759019, by decide⟩ :=
  accepted_of_selected 13 376001 ⟨759019, by decide⟩ ⟨13, 2, 0, 759019, 376001, 2345, 16384⟩
    (by decide) selected_cut_30068

theorem selected_cut_30069 : selected 8 ⟨759040, by decide⟩
    (prefixPartial 13 376002) = some ⟨13, 2, 0, 759040, 376002, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_376002_759040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376002 ⟨759040, by decide⟩ :=
  accepted_of_selected 13 376002 ⟨759040, by decide⟩ ⟨13, 2, 0, 759040, 376002, 1473, 16384⟩
    (by decide) selected_cut_30069

theorem selected_cut_30070 : selected 8 ⟨759050, by decide⟩
    (prefixPartial 13 376003) = some ⟨13, 2, 0, 759050, 376003, 769, 16384⟩ := by
  decide +kernel

theorem context_13_376003_759050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376003 ⟨759050, by decide⟩ :=
  accepted_of_selected 13 376003 ⟨759050, by decide⟩ ⟨13, 2, 0, 759050, 376003, 769, 16384⟩
    (by decide) selected_cut_30070

theorem unmarked_context_12_94000_759051 : frontier 9 ⟨759051, by decide⟩
    (prefixCache 12 94000) (prefixPartial 12 94000) = false := by
  decide +kernel

theorem node_context_12_94000_759051 : EJMOriginalGlobalDAGData.nodes 9 ⟨759051, by decide⟩ =
    .split (coordinate 12) (![⟨758981, by decide⟩,⟨759019, by decide⟩,⟨759040, by decide⟩,⟨759050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94000_759051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94000 ⟨759051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94000
    ⟨759051, by decide⟩ (by decide) (![⟨758981, by decide⟩,⟨759019, by decide⟩,⟨759040, by decide⟩,⟨759050, by decide⟩]) unmarked_context_12_94000_759051 node_context_12_94000_759051
  intro a
  fin_cases a
  · exact context_13_376000_758981
  · exact context_13_376001_759019
  · exact context_13_376002_759040
  · exact context_13_376003_759050

theorem selected_cut_30071 : selected 8 ⟨759058, by decide⟩
    (prefixPartial 13 376004) = some ⟨13, 2, 0, 759058, 376004, 633, 16384⟩ := by
  decide +kernel

theorem context_13_376004_759058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376004 ⟨759058, by decide⟩ :=
  accepted_of_selected 13 376004 ⟨759058, by decide⟩ ⟨13, 2, 0, 759058, 376004, 633, 16384⟩
    (by decide) selected_cut_30071

theorem selected_cut_30072 : selected 8 ⟨759092, by decide⟩
    (prefixPartial 13 376005) = some ⟨13, 2, 0, 759092, 376005, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_376005_759092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376005 ⟨759092, by decide⟩ :=
  accepted_of_selected 13 376005 ⟨759092, by decide⟩ ⟨13, 2, 0, 759092, 376005, 2153, 16384⟩
    (by decide) selected_cut_30072

theorem selected_cut_30073 : selected 8 ⟨759112, by decide⟩
    (prefixPartial 13 376006) = some ⟨13, 2, 0, 759112, 376006, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_376006_759112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376006 ⟨759112, by decide⟩ :=
  accepted_of_selected 13 376006 ⟨759112, by decide⟩ ⟨13, 2, 0, 759112, 376006, 1709, 16384⟩
    (by decide) selected_cut_30073

theorem selected_cut_30074 : selected 8 ⟨759120, by decide⟩
    (prefixPartial 13 376007) = some ⟨13, 2, 0, 759120, 376007, 661, 16384⟩ := by
  decide +kernel

theorem context_13_376007_759120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376007 ⟨759120, by decide⟩ :=
  accepted_of_selected 13 376007 ⟨759120, by decide⟩ ⟨13, 2, 0, 759120, 376007, 661, 16384⟩
    (by decide) selected_cut_30074

theorem unmarked_context_12_94001_759121 : frontier 9 ⟨759121, by decide⟩
    (prefixCache 12 94001) (prefixPartial 12 94001) = false := by
  decide +kernel

theorem node_context_12_94001_759121 : EJMOriginalGlobalDAGData.nodes 9 ⟨759121, by decide⟩ =
    .split (coordinate 12) (![⟨759058, by decide⟩,⟨759092, by decide⟩,⟨759112, by decide⟩,⟨759120, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94001_759121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94001 ⟨759121, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94001
    ⟨759121, by decide⟩ (by decide) (![⟨759058, by decide⟩,⟨759092, by decide⟩,⟨759112, by decide⟩,⟨759120, by decide⟩]) unmarked_context_12_94001_759121 node_context_12_94001_759121
  intro a
  fin_cases a
  · exact context_13_376004_759058
  · exact context_13_376005_759092
  · exact context_13_376006_759112
  · exact context_13_376007_759120

theorem selected_cut_30075 : selected 8 ⟨759128, by decide⟩
    (prefixPartial 13 376008) = some ⟨13, 2, 0, 759128, 376008, 537, 16384⟩ := by
  decide +kernel

theorem context_13_376008_759128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376008 ⟨759128, by decide⟩ :=
  accepted_of_selected 13 376008 ⟨759128, by decide⟩ ⟨13, 2, 0, 759128, 376008, 537, 16384⟩
    (by decide) selected_cut_30075

theorem selected_cut_30076 : selected 8 ⟨759166, by decide⟩
    (prefixPartial 13 376009) = some ⟨13, 2, 0, 759166, 376009, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_376009_759166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376009 ⟨759166, by decide⟩ :=
  accepted_of_selected 13 376009 ⟨759166, by decide⟩ ⟨13, 2, 0, 759166, 376009, 2237, 16384⟩
    (by decide) selected_cut_30076

theorem selected_cut_30077 : selected 8 ⟨759184, by decide⟩
    (prefixPartial 13 376010) = some ⟨13, 2, 0, 759184, 376010, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_376010_759184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376010 ⟨759184, by decide⟩ :=
  accepted_of_selected 13 376010 ⟨759184, by decide⟩ ⟨13, 2, 0, 759184, 376010, 1641, 16384⟩
    (by decide) selected_cut_30077

theorem selected_cut_30078 : selected 8 ⟨759191, by decide⟩
    (prefixPartial 13 376011) = some ⟨13, 2, 0, 759191, 376011, 765, 16384⟩ := by
  decide +kernel

theorem context_13_376011_759191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376011 ⟨759191, by decide⟩ :=
  accepted_of_selected 13 376011 ⟨759191, by decide⟩ ⟨13, 2, 0, 759191, 376011, 765, 16384⟩
    (by decide) selected_cut_30078

theorem unmarked_context_12_94002_759192 : frontier 9 ⟨759192, by decide⟩
    (prefixCache 12 94002) (prefixPartial 12 94002) = false := by
  decide +kernel

theorem node_context_12_94002_759192 : EJMOriginalGlobalDAGData.nodes 9 ⟨759192, by decide⟩ =
    .split (coordinate 12) (![⟨759128, by decide⟩,⟨759166, by decide⟩,⟨759184, by decide⟩,⟨759191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94002_759192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94002 ⟨759192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94002
    ⟨759192, by decide⟩ (by decide) (![⟨759128, by decide⟩,⟨759166, by decide⟩,⟨759184, by decide⟩,⟨759191, by decide⟩]) unmarked_context_12_94002_759192 node_context_12_94002_759192
  intro a
  fin_cases a
  · exact context_13_376008_759128
  · exact context_13_376009_759166
  · exact context_13_376010_759184
  · exact context_13_376011_759191

theorem selected_cut_30079 : selected 8 ⟨759199, by decide⟩
    (prefixPartial 13 376012) = some ⟨13, 2, 0, 759199, 376012, 489, 16384⟩ := by
  decide +kernel

theorem context_13_376012_759199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376012 ⟨759199, by decide⟩ :=
  accepted_of_selected 13 376012 ⟨759199, by decide⟩ ⟨13, 2, 0, 759199, 376012, 489, 16384⟩
    (by decide) selected_cut_30079

theorem selected_cut_30080 : selected 8 ⟨759223, by decide⟩
    (prefixPartial 13 376013) = some ⟨13, 2, 0, 759223, 376013, 2333, 16384⟩ := by
  decide +kernel

theorem context_13_376013_759223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376013 ⟨759223, by decide⟩ :=
  accepted_of_selected 13 376013 ⟨759223, by decide⟩ ⟨13, 2, 0, 759223, 376013, 2333, 16384⟩
    (by decide) selected_cut_30080

theorem selected_cut_30081 : selected 8 ⟨759243, by decide⟩
    (prefixPartial 13 376014) = some ⟨13, 2, 0, 759243, 376014, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_376014_759243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376014 ⟨759243, by decide⟩ :=
  accepted_of_selected 13 376014 ⟨759243, by decide⟩ ⟨13, 2, 0, 759243, 376014, 1681, 16384⟩
    (by decide) selected_cut_30081

theorem selected_cut_30082 : selected 8 ⟨759249, by decide⟩
    (prefixPartial 13 376015) = some ⟨13, 2, 0, 759249, 376015, 701, 16384⟩ := by
  decide +kernel

theorem context_13_376015_759249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376015 ⟨759249, by decide⟩ :=
  accepted_of_selected 13 376015 ⟨759249, by decide⟩ ⟨13, 2, 0, 759249, 376015, 701, 16384⟩
    (by decide) selected_cut_30082

theorem unmarked_context_12_94003_759250 : frontier 9 ⟨759250, by decide⟩
    (prefixCache 12 94003) (prefixPartial 12 94003) = false := by
  decide +kernel

theorem node_context_12_94003_759250 : EJMOriginalGlobalDAGData.nodes 9 ⟨759250, by decide⟩ =
    .split (coordinate 12) (![⟨759199, by decide⟩,⟨759223, by decide⟩,⟨759243, by decide⟩,⟨759249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94003_759250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94003 ⟨759250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94003
    ⟨759250, by decide⟩ (by decide) (![⟨759199, by decide⟩,⟨759223, by decide⟩,⟨759243, by decide⟩,⟨759249, by decide⟩]) unmarked_context_12_94003_759250 node_context_12_94003_759250
  intro a
  fin_cases a
  · exact context_13_376012_759199
  · exact context_13_376013_759223
  · exact context_13_376014_759243
  · exact context_13_376015_759249

theorem unmarked_context_11_23500_759251 : frontier 10 ⟨759251, by decide⟩
    (prefixCache 11 23500) (prefixPartial 11 23500) = false := by
  decide +kernel

theorem node_context_11_23500_759251 : EJMOriginalGlobalDAGData.nodes 10 ⟨759251, by decide⟩ =
    .split (coordinate 11) (![⟨759051, by decide⟩,⟨759121, by decide⟩,⟨759192, by decide⟩,⟨759250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23500_759251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23500 ⟨759251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23500
    ⟨759251, by decide⟩ (by decide) (![⟨759051, by decide⟩,⟨759121, by decide⟩,⟨759192, by decide⟩,⟨759250, by decide⟩]) unmarked_context_11_23500_759251 node_context_11_23500_759251
  intro a
  fin_cases a
  · exact context_12_94000_759051
  · exact context_12_94001_759121
  · exact context_12_94002_759192
  · exact context_12_94003_759250

theorem selected_cut_30083 : selected 8 ⟨759255, by decide⟩
    (prefixPartial 13 376016) = some ⟨13, 2, 0, 759255, 376016, 317, 16384⟩ := by
  decide +kernel

theorem context_13_376016_759255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376016 ⟨759255, by decide⟩ :=
  accepted_of_selected 13 376016 ⟨759255, by decide⟩ ⟨13, 2, 0, 759255, 376016, 317, 16384⟩
    (by decide) selected_cut_30083

theorem selected_cut_30084 : selected 8 ⟨759310, by decide⟩
    (prefixPartial 13 376017) = some ⟨13, 2, 0, 759310, 376017, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_376017_759310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376017 ⟨759310, by decide⟩ :=
  accepted_of_selected 13 376017 ⟨759310, by decide⟩ ⟨13, 2, 0, 759310, 376017, 2293, 16384⟩
    (by decide) selected_cut_30084

theorem selected_cut_30085 : selected 8 ⟨759337, by decide⟩
    (prefixPartial 13 376018) = some ⟨13, 2, 0, 759337, 376018, 1581, 16384⟩ := by
  decide +kernel

theorem context_13_376018_759337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376018 ⟨759337, by decide⟩ :=
  accepted_of_selected 13 376018 ⟨759337, by decide⟩ ⟨13, 2, 0, 759337, 376018, 1581, 16384⟩
    (by decide) selected_cut_30085

theorem selected_cut_30086 : selected 8 ⟨759348, by decide⟩
    (prefixPartial 13 376019) = some ⟨13, 2, 0, 759348, 376019, 809, 16384⟩ := by
  decide +kernel

theorem context_13_376019_759348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376019 ⟨759348, by decide⟩ :=
  accepted_of_selected 13 376019 ⟨759348, by decide⟩ ⟨13, 2, 0, 759348, 376019, 809, 16384⟩
    (by decide) selected_cut_30086

theorem unmarked_context_12_94004_759349 : frontier 9 ⟨759349, by decide⟩
    (prefixCache 12 94004) (prefixPartial 12 94004) = false := by
  decide +kernel

theorem node_context_12_94004_759349 : EJMOriginalGlobalDAGData.nodes 9 ⟨759349, by decide⟩ =
    .split (coordinate 12) (![⟨759255, by decide⟩,⟨759310, by decide⟩,⟨759337, by decide⟩,⟨759348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94004_759349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94004 ⟨759349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94004
    ⟨759349, by decide⟩ (by decide) (![⟨759255, by decide⟩,⟨759310, by decide⟩,⟨759337, by decide⟩,⟨759348, by decide⟩]) unmarked_context_12_94004_759349 node_context_12_94004_759349
  intro a
  fin_cases a
  · exact context_13_376016_759255
  · exact context_13_376017_759310
  · exact context_13_376018_759337
  · exact context_13_376019_759348

theorem selected_cut_30087 : selected 8 ⟨759354, by decide⟩
    (prefixPartial 13 376020) = some ⟨13, 2, 0, 759354, 376020, 269, 16384⟩ := by
  decide +kernel

theorem context_13_376020_759354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376020 ⟨759354, by decide⟩ :=
  accepted_of_selected 13 376020 ⟨759354, by decide⟩ ⟨13, 2, 0, 759354, 376020, 269, 16384⟩
    (by decide) selected_cut_30087

theorem selected_cut_30088 : selected 8 ⟨759381, by decide⟩
    (prefixPartial 13 376021) = some ⟨13, 2, 0, 759381, 376021, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_376021_759381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376021 ⟨759381, by decide⟩ :=
  accepted_of_selected 13 376021 ⟨759381, by decide⟩ ⟨13, 2, 0, 759381, 376021, 1865, 16384⟩
    (by decide) selected_cut_30088

theorem selected_cut_30089 : selected 8 ⟨759398, by decide⟩
    (prefixPartial 13 376022) = some ⟨13, 2, 0, 759398, 376022, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_376022_759398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376022 ⟨759398, by decide⟩ :=
  accepted_of_selected 13 376022 ⟨759398, by decide⟩ ⟨13, 2, 0, 759398, 376022, 1585, 16384⟩
    (by decide) selected_cut_30089

theorem selected_cut_30090 : selected 8 ⟨759405, by decide⟩
    (prefixPartial 13 376023) = some ⟨13, 2, 0, 759405, 376023, 661, 16384⟩ := by
  decide +kernel

theorem context_13_376023_759405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376023 ⟨759405, by decide⟩ :=
  accepted_of_selected 13 376023 ⟨759405, by decide⟩ ⟨13, 2, 0, 759405, 376023, 661, 16384⟩
    (by decide) selected_cut_30090

theorem unmarked_context_12_94005_759406 : frontier 9 ⟨759406, by decide⟩
    (prefixCache 12 94005) (prefixPartial 12 94005) = false := by
  decide +kernel

theorem node_context_12_94005_759406 : EJMOriginalGlobalDAGData.nodes 9 ⟨759406, by decide⟩ =
    .split (coordinate 12) (![⟨759354, by decide⟩,⟨759381, by decide⟩,⟨759398, by decide⟩,⟨759405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94005_759406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94005 ⟨759406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94005
    ⟨759406, by decide⟩ (by decide) (![⟨759354, by decide⟩,⟨759381, by decide⟩,⟨759398, by decide⟩,⟨759405, by decide⟩]) unmarked_context_12_94005_759406 node_context_12_94005_759406
  intro a
  fin_cases a
  · exact context_13_376020_759354
  · exact context_13_376021_759381
  · exact context_13_376022_759398
  · exact context_13_376023_759405

theorem selected_cut_30091 : selected 8 ⟨759410, by decide⟩
    (prefixPartial 13 376024) = some ⟨13, 2, 0, 759410, 376024, 265, 16384⟩ := by
  decide +kernel

theorem context_13_376024_759410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376024 ⟨759410, by decide⟩ :=
  accepted_of_selected 13 376024 ⟨759410, by decide⟩ ⟨13, 2, 0, 759410, 376024, 265, 16384⟩
    (by decide) selected_cut_30091

theorem selected_cut_30092 : selected 8 ⟨759437, by decide⟩
    (prefixPartial 13 376025) = some ⟨13, 2, 0, 759437, 376025, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_376025_759437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376025 ⟨759437, by decide⟩ :=
  accepted_of_selected 13 376025 ⟨759437, by decide⟩ ⟨13, 2, 0, 759437, 376025, 2013, 16384⟩
    (by decide) selected_cut_30092

theorem selected_cut_30093 : selected 8 ⟨759457, by decide⟩
    (prefixPartial 13 376026) = some ⟨13, 2, 0, 759457, 376026, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_376026_759457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376026 ⟨759457, by decide⟩ :=
  accepted_of_selected 13 376026 ⟨759457, by decide⟩ ⟨13, 2, 0, 759457, 376026, 1521, 16384⟩
    (by decide) selected_cut_30093

theorem selected_cut_30094 : selected 8 ⟨759466, by decide⟩
    (prefixPartial 13 376027) = some ⟨13, 2, 0, 759466, 376027, 829, 16384⟩ := by
  decide +kernel

theorem context_13_376027_759466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376027 ⟨759466, by decide⟩ :=
  accepted_of_selected 13 376027 ⟨759466, by decide⟩ ⟨13, 2, 0, 759466, 376027, 829, 16384⟩
    (by decide) selected_cut_30094

theorem unmarked_context_12_94006_759467 : frontier 9 ⟨759467, by decide⟩
    (prefixCache 12 94006) (prefixPartial 12 94006) = false := by
  decide +kernel

theorem node_context_12_94006_759467 : EJMOriginalGlobalDAGData.nodes 9 ⟨759467, by decide⟩ =
    .split (coordinate 12) (![⟨759410, by decide⟩,⟨759437, by decide⟩,⟨759457, by decide⟩,⟨759466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94006_759467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94006 ⟨759467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94006
    ⟨759467, by decide⟩ (by decide) (![⟨759410, by decide⟩,⟨759437, by decide⟩,⟨759457, by decide⟩,⟨759466, by decide⟩]) unmarked_context_12_94006_759467 node_context_12_94006_759467
  intro a
  fin_cases a
  · exact context_13_376024_759410
  · exact context_13_376025_759437
  · exact context_13_376026_759457
  · exact context_13_376027_759466

theorem selected_cut_30095 : selected 8 ⟨759471, by decide⟩
    (prefixPartial 13 376028) = some ⟨13, 2, 0, 759471, 376028, 241, 16384⟩ := by
  decide +kernel

theorem context_13_376028_759471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376028 ⟨759471, by decide⟩ :=
  accepted_of_selected 13 376028 ⟨759471, by decide⟩ ⟨13, 2, 0, 759471, 376028, 241, 16384⟩
    (by decide) selected_cut_30095

theorem selected_cut_30096 : selected 8 ⟨759497, by decide⟩
    (prefixPartial 13 376029) = some ⟨13, 2, 0, 759497, 376029, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_376029_759497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376029 ⟨759497, by decide⟩ :=
  accepted_of_selected 13 376029 ⟨759497, by decide⟩ ⟨13, 2, 0, 759497, 376029, 2137, 16384⟩
    (by decide) selected_cut_30096

theorem selected_cut_30097 : selected 8 ⟨759515, by decide⟩
    (prefixPartial 13 376030) = some ⟨13, 2, 0, 759515, 376030, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_376030_759515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376030 ⟨759515, by decide⟩ :=
  accepted_of_selected 13 376030 ⟨759515, by decide⟩ ⟨13, 2, 0, 759515, 376030, 1765, 16384⟩
    (by decide) selected_cut_30097

theorem selected_cut_30098 : selected 8 ⟨759521, by decide⟩
    (prefixPartial 13 376031) = some ⟨13, 2, 0, 759521, 376031, 741, 16384⟩ := by
  decide +kernel

theorem context_13_376031_759521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376031 ⟨759521, by decide⟩ :=
  accepted_of_selected 13 376031 ⟨759521, by decide⟩ ⟨13, 2, 0, 759521, 376031, 741, 16384⟩
    (by decide) selected_cut_30098

theorem unmarked_context_12_94007_759522 : frontier 9 ⟨759522, by decide⟩
    (prefixCache 12 94007) (prefixPartial 12 94007) = false := by
  decide +kernel

theorem node_context_12_94007_759522 : EJMOriginalGlobalDAGData.nodes 9 ⟨759522, by decide⟩ =
    .split (coordinate 12) (![⟨759471, by decide⟩,⟨759497, by decide⟩,⟨759515, by decide⟩,⟨759521, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94007_759522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94007 ⟨759522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94007
    ⟨759522, by decide⟩ (by decide) (![⟨759471, by decide⟩,⟨759497, by decide⟩,⟨759515, by decide⟩,⟨759521, by decide⟩]) unmarked_context_12_94007_759522 node_context_12_94007_759522
  intro a
  fin_cases a
  · exact context_13_376028_759471
  · exact context_13_376029_759497
  · exact context_13_376030_759515
  · exact context_13_376031_759521

theorem unmarked_context_11_23501_759523 : frontier 10 ⟨759523, by decide⟩
    (prefixCache 11 23501) (prefixPartial 11 23501) = false := by
  decide +kernel

theorem node_context_11_23501_759523 : EJMOriginalGlobalDAGData.nodes 10 ⟨759523, by decide⟩ =
    .split (coordinate 11) (![⟨759349, by decide⟩,⟨759406, by decide⟩,⟨759467, by decide⟩,⟨759522, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23501_759523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23501 ⟨759523, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23501
    ⟨759523, by decide⟩ (by decide) (![⟨759349, by decide⟩,⟨759406, by decide⟩,⟨759467, by decide⟩,⟨759522, by decide⟩]) unmarked_context_11_23501_759523 node_context_11_23501_759523
  intro a
  fin_cases a
  · exact context_12_94004_759349
  · exact context_12_94005_759406
  · exact context_12_94006_759467
  · exact context_12_94007_759522

theorem selected_cut_30099 : selected 8 ⟨759527, by decide⟩
    (prefixPartial 13 376032) = some ⟨13, 2, 0, 759527, 376032, 189, 16384⟩ := by
  decide +kernel

theorem context_13_376032_759527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376032 ⟨759527, by decide⟩ :=
  accepted_of_selected 13 376032 ⟨759527, by decide⟩ ⟨13, 2, 0, 759527, 376032, 189, 16384⟩
    (by decide) selected_cut_30099

theorem selected_cut_30100 : selected 8 ⟨759575, by decide⟩
    (prefixPartial 13 376033) = some ⟨13, 2, 0, 759575, 376033, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_376033_759575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376033 ⟨759575, by decide⟩ :=
  accepted_of_selected 13 376033 ⟨759575, by decide⟩ ⟨13, 2, 0, 759575, 376033, 2349, 16384⟩
    (by decide) selected_cut_30100

theorem selected_cut_30101 : selected 8 ⟨759595, by decide⟩
    (prefixPartial 13 376034) = some ⟨13, 2, 0, 759595, 376034, 1733, 16384⟩ := by
  decide +kernel

theorem context_13_376034_759595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376034 ⟨759595, by decide⟩ :=
  accepted_of_selected 13 376034 ⟨759595, by decide⟩ ⟨13, 2, 0, 759595, 376034, 1733, 16384⟩
    (by decide) selected_cut_30101

theorem selected_cut_30102 : selected 8 ⟨759604, by decide⟩
    (prefixPartial 13 376035) = some ⟨13, 2, 0, 759604, 376035, 913, 16384⟩ := by
  decide +kernel

theorem context_13_376035_759604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376035 ⟨759604, by decide⟩ :=
  accepted_of_selected 13 376035 ⟨759604, by decide⟩ ⟨13, 2, 0, 759604, 376035, 913, 16384⟩
    (by decide) selected_cut_30102

theorem unmarked_context_12_94008_759605 : frontier 9 ⟨759605, by decide⟩
    (prefixCache 12 94008) (prefixPartial 12 94008) = false := by
  decide +kernel

theorem node_context_12_94008_759605 : EJMOriginalGlobalDAGData.nodes 9 ⟨759605, by decide⟩ =
    .split (coordinate 12) (![⟨759527, by decide⟩,⟨759575, by decide⟩,⟨759595, by decide⟩,⟨759604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94008_759605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94008 ⟨759605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94008
    ⟨759605, by decide⟩ (by decide) (![⟨759527, by decide⟩,⟨759575, by decide⟩,⟨759595, by decide⟩,⟨759604, by decide⟩]) unmarked_context_12_94008_759605 node_context_12_94008_759605
  intro a
  fin_cases a
  · exact context_13_376032_759527
  · exact context_13_376033_759575
  · exact context_13_376034_759595
  · exact context_13_376035_759604

theorem selected_cut_30103 : selected 8 ⟨759608, by decide⟩
    (prefixPartial 13 376036) = some ⟨13, 2, 0, 759608, 376036, 173, 16384⟩ := by
  decide +kernel

theorem context_13_376036_759608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376036 ⟨759608, by decide⟩ :=
  accepted_of_selected 13 376036 ⟨759608, by decide⟩ ⟨13, 2, 0, 759608, 376036, 173, 16384⟩
    (by decide) selected_cut_30103

theorem selected_cut_30104 : selected 8 ⟨759638, by decide⟩
    (prefixPartial 13 376037) = some ⟨13, 2, 0, 759638, 376037, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_376037_759638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376037 ⟨759638, by decide⟩ :=
  accepted_of_selected 13 376037 ⟨759638, by decide⟩ ⟨13, 2, 0, 759638, 376037, 1981, 16384⟩
    (by decide) selected_cut_30104

theorem selected_cut_30105 : selected 8 ⟨759657, by decide⟩
    (prefixPartial 13 376038) = some ⟨13, 2, 0, 759657, 376038, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_376038_759657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376038 ⟨759657, by decide⟩ :=
  accepted_of_selected 13 376038 ⟨759657, by decide⟩ ⟨13, 2, 0, 759657, 376038, 1861, 16384⟩
    (by decide) selected_cut_30105

theorem selected_cut_30106 : selected 8 ⟨759669, by decide⟩
    (prefixPartial 13 376039) = some ⟨13, 2, 0, 759669, 376039, 869, 16384⟩ := by
  decide +kernel

theorem context_13_376039_759669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376039 ⟨759669, by decide⟩ :=
  accepted_of_selected 13 376039 ⟨759669, by decide⟩ ⟨13, 2, 0, 759669, 376039, 869, 16384⟩
    (by decide) selected_cut_30106

theorem unmarked_context_12_94009_759670 : frontier 9 ⟨759670, by decide⟩
    (prefixCache 12 94009) (prefixPartial 12 94009) = false := by
  decide +kernel

theorem node_context_12_94009_759670 : EJMOriginalGlobalDAGData.nodes 9 ⟨759670, by decide⟩ =
    .split (coordinate 12) (![⟨759608, by decide⟩,⟨759638, by decide⟩,⟨759657, by decide⟩,⟨759669, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94009_759670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94009 ⟨759670, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94009
    ⟨759670, by decide⟩ (by decide) (![⟨759608, by decide⟩,⟨759638, by decide⟩,⟨759657, by decide⟩,⟨759669, by decide⟩]) unmarked_context_12_94009_759670 node_context_12_94009_759670
  intro a
  fin_cases a
  · exact context_13_376036_759608
  · exact context_13_376037_759638
  · exact context_13_376038_759657
  · exact context_13_376039_759669

theorem selected_cut_30107 : selected 8 ⟨759673, by decide⟩
    (prefixPartial 13 376040) = some ⟨13, 2, 0, 759673, 376040, 85, 16384⟩ := by
  decide +kernel

theorem context_13_376040_759673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376040 ⟨759673, by decide⟩ :=
  accepted_of_selected 13 376040 ⟨759673, by decide⟩ ⟨13, 2, 0, 759673, 376040, 85, 16384⟩
    (by decide) selected_cut_30107

theorem selected_cut_30108 : selected 8 ⟨759710, by decide⟩
    (prefixPartial 13 376041) = some ⟨13, 2, 0, 759710, 376041, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_376041_759710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376041 ⟨759710, by decide⟩ :=
  accepted_of_selected 13 376041 ⟨759710, by decide⟩ ⟨13, 2, 0, 759710, 376041, 2213, 16384⟩
    (by decide) selected_cut_30108

theorem selected_cut_30109 : selected 8 ⟨759730, by decide⟩
    (prefixPartial 13 376042) = some ⟨13, 2, 0, 759730, 376042, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_376042_759730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376042 ⟨759730, by decide⟩ :=
  accepted_of_selected 13 376042 ⟨759730, by decide⟩ ⟨13, 2, 0, 759730, 376042, 1721, 16384⟩
    (by decide) selected_cut_30109

theorem selected_cut_30110 : selected 8 ⟨759738, by decide⟩
    (prefixPartial 13 376043) = some ⟨13, 2, 0, 759738, 376043, 853, 16384⟩ := by
  decide +kernel

theorem context_13_376043_759738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376043 ⟨759738, by decide⟩ :=
  accepted_of_selected 13 376043 ⟨759738, by decide⟩ ⟨13, 2, 0, 759738, 376043, 853, 16384⟩
    (by decide) selected_cut_30110

theorem unmarked_context_12_94010_759739 : frontier 9 ⟨759739, by decide⟩
    (prefixCache 12 94010) (prefixPartial 12 94010) = false := by
  decide +kernel

theorem node_context_12_94010_759739 : EJMOriginalGlobalDAGData.nodes 9 ⟨759739, by decide⟩ =
    .split (coordinate 12) (![⟨759673, by decide⟩,⟨759710, by decide⟩,⟨759730, by decide⟩,⟨759738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94010_759739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94010 ⟨759739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94010
    ⟨759739, by decide⟩ (by decide) (![⟨759673, by decide⟩,⟨759710, by decide⟩,⟨759730, by decide⟩,⟨759738, by decide⟩]) unmarked_context_12_94010_759739 node_context_12_94010_759739
  intro a
  fin_cases a
  · exact context_13_376040_759673
  · exact context_13_376041_759710
  · exact context_13_376042_759730
  · exact context_13_376043_759738

theorem selected_cut_30111 : selected 8 ⟨759742, by decide⟩
    (prefixPartial 13 376044) = some ⟨13, 2, 0, 759742, 376044, 73, 16384⟩ := by
  decide +kernel

theorem context_13_376044_759742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376044 ⟨759742, by decide⟩ :=
  accepted_of_selected 13 376044 ⟨759742, by decide⟩ ⟨13, 2, 0, 759742, 376044, 73, 16384⟩
    (by decide) selected_cut_30111

theorem selected_cut_30112 : selected 8 ⟨759780, by decide⟩
    (prefixPartial 13 376045) = some ⟨13, 2, 0, 759780, 376045, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_376045_759780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376045 ⟨759780, by decide⟩ :=
  accepted_of_selected 13 376045 ⟨759780, by decide⟩ ⟨13, 2, 0, 759780, 376045, 2357, 16384⟩
    (by decide) selected_cut_30112

theorem selected_cut_30113 : selected 8 ⟨759798, by decide⟩
    (prefixPartial 13 376046) = some ⟨13, 2, 0, 759798, 376046, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_376046_759798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376046 ⟨759798, by decide⟩ :=
  accepted_of_selected 13 376046 ⟨759798, by decide⟩ ⟨13, 2, 0, 759798, 376046, 1813, 16384⟩
    (by decide) selected_cut_30113

theorem selected_cut_30114 : selected 8 ⟨759807, by decide⟩
    (prefixPartial 13 376047) = some ⟨13, 2, 0, 759807, 376047, 857, 16384⟩ := by
  decide +kernel

theorem context_13_376047_759807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376047 ⟨759807, by decide⟩ :=
  accepted_of_selected 13 376047 ⟨759807, by decide⟩ ⟨13, 2, 0, 759807, 376047, 857, 16384⟩
    (by decide) selected_cut_30114

theorem unmarked_context_12_94011_759808 : frontier 9 ⟨759808, by decide⟩
    (prefixCache 12 94011) (prefixPartial 12 94011) = false := by
  decide +kernel

theorem node_context_12_94011_759808 : EJMOriginalGlobalDAGData.nodes 9 ⟨759808, by decide⟩ =
    .split (coordinate 12) (![⟨759742, by decide⟩,⟨759780, by decide⟩,⟨759798, by decide⟩,⟨759807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94011_759808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94011 ⟨759808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94011
    ⟨759808, by decide⟩ (by decide) (![⟨759742, by decide⟩,⟨759780, by decide⟩,⟨759798, by decide⟩,⟨759807, by decide⟩]) unmarked_context_12_94011_759808 node_context_12_94011_759808
  intro a
  fin_cases a
  · exact context_13_376044_759742
  · exact context_13_376045_759780
  · exact context_13_376046_759798
  · exact context_13_376047_759807

theorem unmarked_context_11_23502_759809 : frontier 10 ⟨759809, by decide⟩
    (prefixCache 11 23502) (prefixPartial 11 23502) = false := by
  decide +kernel

theorem node_context_11_23502_759809 : EJMOriginalGlobalDAGData.nodes 10 ⟨759809, by decide⟩ =
    .split (coordinate 11) (![⟨759605, by decide⟩,⟨759670, by decide⟩,⟨759739, by decide⟩,⟨759808, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23502_759809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23502 ⟨759809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23502
    ⟨759809, by decide⟩ (by decide) (![⟨759605, by decide⟩,⟨759670, by decide⟩,⟨759739, by decide⟩,⟨759808, by decide⟩]) unmarked_context_11_23502_759809 node_context_11_23502_759809
  intro a
  fin_cases a
  · exact context_12_94008_759605
  · exact context_12_94009_759670
  · exact context_12_94010_759739
  · exact context_12_94011_759808

theorem selected_cut_30115 : selected 10 ⟨399386, by decide⟩
    (prefixPartial 11 23503) = some ⟨11, 2, 0, 399386, 23503, 5, 262144⟩ := by
  decide +kernel

theorem context_11_23503_399386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23503 ⟨399386, by decide⟩ :=
  accepted_of_selected 11 23503 ⟨399386, by decide⟩ ⟨11, 2, 0, 399386, 23503, 5, 262144⟩
    (by decide) selected_cut_30115

theorem unmarked_context_10_5875_759810 : frontier 11 ⟨759810, by decide⟩
    (prefixCache 10 5875) (prefixPartial 10 5875) = false := by
  decide +kernel

theorem node_context_10_5875_759810 : EJMOriginalGlobalDAGData.nodes 11 ⟨759810, by decide⟩ =
    .split (coordinate 10) (![⟨759251, by decide⟩,⟨759523, by decide⟩,⟨759809, by decide⟩,⟨399386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5875_759810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5875 ⟨759810, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5875
    ⟨759810, by decide⟩ (by decide) (![⟨759251, by decide⟩,⟨759523, by decide⟩,⟨759809, by decide⟩,⟨399386, by decide⟩]) unmarked_context_10_5875_759810 node_context_10_5875_759810
  intro a
  fin_cases a
  · exact context_11_23500_759251
  · exact context_11_23501_759523
  · exact context_11_23502_759809
  · exact context_11_23503_399386

theorem unmarked_context_9_1468_759811 : frontier 12 ⟨759811, by decide⟩
    (prefixCache 9 1468) (prefixPartial 9 1468) = false := by
  decide +kernel

theorem node_context_9_1468_759811 : EJMOriginalGlobalDAGData.nodes 12 ⟨759811, by decide⟩ =
    .split (coordinate 9) (![⟨756299, by decide⟩,⟨757809, by decide⟩,⟨758970, by decide⟩,⟨759810, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1468_759811 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1468 ⟨759811, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1468
    ⟨759811, by decide⟩ (by decide) (![⟨756299, by decide⟩,⟨757809, by decide⟩,⟨758970, by decide⟩,⟨759810, by decide⟩]) unmarked_context_9_1468_759811 node_context_9_1468_759811
  intro a
  fin_cases a
  · exact context_10_5872_756299
  · exact context_10_5873_757809
  · exact context_10_5874_758970
  · exact context_10_5875_759810

theorem selected_cut_30116 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 376064) = some ⟨13, 1, 0, 3444, 376064, 1, 16384⟩ := by
  decide +kernel

theorem context_13_376064_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376064 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 376064 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 376064, 1, 16384⟩
    (by decide) selected_cut_30116

theorem selected_cut_30117 : selected 8 ⟨759850, by decide⟩
    (prefixPartial 13 376065) = some ⟨13, 2, 0, 759850, 376065, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_376065_759850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376065 ⟨759850, by decide⟩ :=
  accepted_of_selected 13 376065 ⟨759850, by decide⟩ ⟨13, 2, 0, 759850, 376065, 2429, 16384⟩
    (by decide) selected_cut_30117

theorem selected_cut_30118 : selected 8 ⟨759870, by decide⟩
    (prefixPartial 13 376066) = some ⟨13, 2, 0, 759870, 376066, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_376066_759870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376066 ⟨759870, by decide⟩ :=
  accepted_of_selected 13 376066 ⟨759870, by decide⟩ ⟨13, 2, 0, 759870, 376066, 1245, 16384⟩
    (by decide) selected_cut_30118

theorem selected_cut_30119 : selected 8 ⟨759877, by decide⟩
    (prefixPartial 13 376067) = some ⟨13, 2, 0, 759877, 376067, 637, 16384⟩ := by
  decide +kernel

theorem context_13_376067_759877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376067 ⟨759877, by decide⟩ :=
  accepted_of_selected 13 376067 ⟨759877, by decide⟩ ⟨13, 2, 0, 759877, 376067, 637, 16384⟩
    (by decide) selected_cut_30119

theorem unmarked_context_12_94016_759878 : frontier 9 ⟨759878, by decide⟩
    (prefixCache 12 94016) (prefixPartial 12 94016) = false := by
  decide +kernel

theorem node_context_12_94016_759878 : EJMOriginalGlobalDAGData.nodes 9 ⟨759878, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨759850, by decide⟩,⟨759870, by decide⟩,⟨759877, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94016_759878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94016 ⟨759878, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94016
    ⟨759878, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨759850, by decide⟩,⟨759870, by decide⟩,⟨759877, by decide⟩]) unmarked_context_12_94016_759878 node_context_12_94016_759878
  intro a
  fin_cases a
  · exact context_13_376064_3444
  · exact context_13_376065_759850
  · exact context_13_376066_759870
  · exact context_13_376067_759877

theorem selected_cut_30120 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 94017) = some ⟨12, 1, 0, 170504, 94017, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94017_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94017 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 94017 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 94017, 1, 65536⟩
    (by decide) selected_cut_30120

theorem selected_cut_30121 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 376072) = some ⟨13, 1, 0, 3444, 376072, 1, 16384⟩ := by
  decide +kernel

theorem context_13_376072_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376072 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 376072 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 376072, 1, 16384⟩
    (by decide) selected_cut_30121

theorem selected_cut_30122 : selected 8 ⟨759919, by decide⟩
    (prefixPartial 13 376073) = some ⟨13, 2, 0, 759919, 376073, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_376073_759919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376073 ⟨759919, by decide⟩ :=
  accepted_of_selected 13 376073 ⟨759919, by decide⟩ ⟨13, 2, 0, 759919, 376073, 2257, 16384⟩
    (by decide) selected_cut_30122

theorem selected_cut_30123 : selected 8 ⟨759938, by decide⟩
    (prefixPartial 13 376074) = some ⟨13, 2, 0, 759938, 376074, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_376074_759938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376074 ⟨759938, by decide⟩ :=
  accepted_of_selected 13 376074 ⟨759938, by decide⟩ ⟨13, 2, 0, 759938, 376074, 1409, 16384⟩
    (by decide) selected_cut_30123

theorem selected_cut_30124 : selected 8 ⟨759942, by decide⟩
    (prefixPartial 13 376075) = some ⟨13, 2, 0, 759942, 376075, 529, 16384⟩ := by
  decide +kernel

theorem context_13_376075_759942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 376075 ⟨759942, by decide⟩ :=
  accepted_of_selected 13 376075 ⟨759942, by decide⟩ ⟨13, 2, 0, 759942, 376075, 529, 16384⟩
    (by decide) selected_cut_30124

theorem unmarked_context_12_94018_759943 : frontier 9 ⟨759943, by decide⟩
    (prefixCache 12 94018) (prefixPartial 12 94018) = false := by
  decide +kernel

theorem node_context_12_94018_759943 : EJMOriginalGlobalDAGData.nodes 9 ⟨759943, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨759919, by decide⟩,⟨759938, by decide⟩,⟨759942, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_94018_759943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94018 ⟨759943, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 94018
    ⟨759943, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨759919, by decide⟩,⟨759938, by decide⟩,⟨759942, by decide⟩]) unmarked_context_12_94018_759943 node_context_12_94018_759943
  intro a
  fin_cases a
  · exact context_13_376072_3444
  · exact context_13_376073_759919
  · exact context_13_376074_759938
  · exact context_13_376075_759942

theorem selected_cut_30125 : selected 9 ⟨759996, by decide⟩
    (prefixPartial 12 94019) = some ⟨12, 2, 0, 759996, 94019, 4057, 65536⟩ := by
  decide +kernel

theorem context_12_94019_759996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94019 ⟨759996, by decide⟩ :=
  accepted_of_selected 12 94019 ⟨759996, by decide⟩ ⟨12, 2, 0, 759996, 94019, 4057, 65536⟩
    (by decide) selected_cut_30125

theorem unmarked_context_11_23504_759997 : frontier 10 ⟨759997, by decide⟩
    (prefixCache 11 23504) (prefixPartial 11 23504) = false := by
  decide +kernel

theorem node_context_11_23504_759997 : EJMOriginalGlobalDAGData.nodes 10 ⟨759997, by decide⟩ =
    .split (coordinate 11) (![⟨759878, by decide⟩,⟨170504, by decide⟩,⟨759943, by decide⟩,⟨759996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23504_759997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23504 ⟨759997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23504
    ⟨759997, by decide⟩ (by decide) (![⟨759878, by decide⟩,⟨170504, by decide⟩,⟨759943, by decide⟩,⟨759996, by decide⟩]) unmarked_context_11_23504_759997 node_context_11_23504_759997
  intro a
  fin_cases a
  · exact context_12_94016_759878
  · exact context_12_94017_170504
  · exact context_12_94018_759943
  · exact context_12_94019_759996

theorem selected_cut_30126 : selected 9 ⟨760056, by decide⟩
    (prefixPartial 12 94020) = some ⟨12, 2, 0, 760056, 94020, 4073, 65536⟩ := by
  decide +kernel

theorem context_12_94020_760056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94020 ⟨760056, by decide⟩ :=
  accepted_of_selected 12 94020 ⟨760056, by decide⟩ ⟨12, 2, 0, 760056, 94020, 4073, 65536⟩
    (by decide) selected_cut_30126

theorem selected_cut_30127 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 94021) = some ⟨12, 1, 0, 170504, 94021, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94021_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94021 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 94021 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 94021, 1, 65536⟩
    (by decide) selected_cut_30127

theorem selected_cut_30128 : selected 9 ⟨760106, by decide⟩
    (prefixPartial 12 94022) = some ⟨12, 2, 0, 760106, 94022, 3809, 65536⟩ := by
  decide +kernel

theorem context_12_94022_760106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94022 ⟨760106, by decide⟩ :=
  accepted_of_selected 12 94022 ⟨760106, by decide⟩ ⟨12, 2, 0, 760106, 94022, 3809, 65536⟩
    (by decide) selected_cut_30128

theorem selected_cut_30129 : selected 9 ⟨760153, by decide⟩
    (prefixPartial 12 94023) = some ⟨12, 2, 0, 760153, 94023, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_94023_760153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94023 ⟨760153, by decide⟩ :=
  accepted_of_selected 12 94023 ⟨760153, by decide⟩ ⟨12, 2, 0, 760153, 94023, 3825, 65536⟩
    (by decide) selected_cut_30129

theorem unmarked_context_11_23505_760154 : frontier 10 ⟨760154, by decide⟩
    (prefixCache 11 23505) (prefixPartial 11 23505) = false := by
  decide +kernel

theorem node_context_11_23505_760154 : EJMOriginalGlobalDAGData.nodes 10 ⟨760154, by decide⟩ =
    .split (coordinate 11) (![⟨760056, by decide⟩,⟨170504, by decide⟩,⟨760106, by decide⟩,⟨760153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23505_760154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23505 ⟨760154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23505
    ⟨760154, by decide⟩ (by decide) (![⟨760056, by decide⟩,⟨170504, by decide⟩,⟨760106, by decide⟩,⟨760153, by decide⟩]) unmarked_context_11_23505_760154 node_context_11_23505_760154
  intro a
  fin_cases a
  · exact context_12_94020_760056
  · exact context_12_94021_170504
  · exact context_12_94022_760106
  · exact context_12_94023_760153

theorem selected_cut_30130 : selected 9 ⟨760225, by decide⟩
    (prefixPartial 12 94024) = some ⟨12, 2, 0, 760225, 94024, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_94024_760225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94024 ⟨760225, by decide⟩ :=
  accepted_of_selected 12 94024 ⟨760225, by decide⟩ ⟨12, 2, 0, 760225, 94024, 3917, 65536⟩
    (by decide) selected_cut_30130

theorem selected_cut_30131 : selected 9 ⟨760313, by decide⟩
    (prefixPartial 12 94025) = some ⟨12, 2, 0, 760313, 94025, 2005, 65536⟩ := by
  decide +kernel

theorem context_12_94025_760313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94025 ⟨760313, by decide⟩ :=
  accepted_of_selected 12 94025 ⟨760313, by decide⟩ ⟨12, 2, 0, 760313, 94025, 2005, 65536⟩
    (by decide) selected_cut_30131

theorem selected_cut_30132 : selected 9 ⟨760365, by decide⟩
    (prefixPartial 12 94026) = some ⟨12, 2, 0, 760365, 94026, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_94026_760365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94026 ⟨760365, by decide⟩ :=
  accepted_of_selected 12 94026 ⟨760365, by decide⟩ ⟨12, 2, 0, 760365, 94026, 3637, 65536⟩
    (by decide) selected_cut_30132

theorem selected_cut_30133 : selected 9 ⟨760415, by decide⟩
    (prefixPartial 12 94027) = some ⟨12, 2, 0, 760415, 94027, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_94027_760415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94027 ⟨760415, by decide⟩ :=
  accepted_of_selected 12 94027 ⟨760415, by decide⟩ ⟨12, 2, 0, 760415, 94027, 3641, 65536⟩
    (by decide) selected_cut_30133

theorem unmarked_context_11_23506_760416 : frontier 10 ⟨760416, by decide⟩
    (prefixCache 11 23506) (prefixPartial 11 23506) = false := by
  decide +kernel

theorem node_context_11_23506_760416 : EJMOriginalGlobalDAGData.nodes 10 ⟨760416, by decide⟩ =
    .split (coordinate 11) (![⟨760225, by decide⟩,⟨760313, by decide⟩,⟨760365, by decide⟩,⟨760415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23506_760416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23506 ⟨760416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23506
    ⟨760416, by decide⟩ (by decide) (![⟨760225, by decide⟩,⟨760313, by decide⟩,⟨760365, by decide⟩,⟨760415, by decide⟩]) unmarked_context_11_23506_760416 node_context_11_23506_760416
  intro a
  fin_cases a
  · exact context_12_94024_760225
  · exact context_12_94025_760313
  · exact context_12_94026_760365
  · exact context_12_94027_760415

theorem selected_cut_30134 : selected 9 ⟨760460, by decide⟩
    (prefixPartial 12 94028) = some ⟨12, 2, 0, 760460, 94028, 2933, 65536⟩ := by
  decide +kernel

theorem context_12_94028_760460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94028 ⟨760460, by decide⟩ :=
  accepted_of_selected 12 94028 ⟨760460, by decide⟩ ⟨12, 2, 0, 760460, 94028, 2933, 65536⟩
    (by decide) selected_cut_30134

theorem selected_cut_30135 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 94029) = some ⟨12, 1, 0, 320864, 94029, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94029_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94029 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 94029 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 94029, 1, 65536⟩
    (by decide) selected_cut_30135

theorem selected_cut_30136 : selected 9 ⟨760510, by decide⟩
    (prefixPartial 12 94030) = some ⟨12, 2, 0, 760510, 94030, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_94030_760510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94030 ⟨760510, by decide⟩ :=
  accepted_of_selected 12 94030 ⟨760510, by decide⟩ ⟨12, 2, 0, 760510, 94030, 2689, 65536⟩
    (by decide) selected_cut_30136

theorem selected_cut_30137 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 94031) = some ⟨12, 1, 0, 760511, 94031, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94031_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94031 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 94031 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 94031, 1, 65536⟩
    (by decide) selected_cut_30137

theorem unmarked_context_11_23507_760512 : frontier 10 ⟨760512, by decide⟩
    (prefixCache 11 23507) (prefixPartial 11 23507) = false := by
  decide +kernel

theorem node_context_11_23507_760512 : EJMOriginalGlobalDAGData.nodes 10 ⟨760512, by decide⟩ =
    .split (coordinate 11) (![⟨760460, by decide⟩,⟨320864, by decide⟩,⟨760510, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23507_760512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23507 ⟨760512, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23507
    ⟨760512, by decide⟩ (by decide) (![⟨760460, by decide⟩,⟨320864, by decide⟩,⟨760510, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_23507_760512 node_context_11_23507_760512
  intro a
  fin_cases a
  · exact context_12_94028_760460
  · exact context_12_94029_320864
  · exact context_12_94030_760510
  · exact context_12_94031_760511

theorem unmarked_context_10_5876_760513 : frontier 11 ⟨760513, by decide⟩
    (prefixCache 10 5876) (prefixPartial 10 5876) = false := by
  decide +kernel

theorem node_context_10_5876_760513 : EJMOriginalGlobalDAGData.nodes 11 ⟨760513, by decide⟩ =
    .split (coordinate 10) (![⟨759997, by decide⟩,⟨760154, by decide⟩,⟨760416, by decide⟩,⟨760512, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5876_760513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5876 ⟨760513, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5876
    ⟨760513, by decide⟩ (by decide) (![⟨759997, by decide⟩,⟨760154, by decide⟩,⟨760416, by decide⟩,⟨760512, by decide⟩]) unmarked_context_10_5876_760513 node_context_10_5876_760513
  intro a
  fin_cases a
  · exact context_11_23504_759997
  · exact context_11_23505_760154
  · exact context_11_23506_760416
  · exact context_11_23507_760512

theorem selected_cut_30138 : selected 9 ⟨760563, by decide⟩
    (prefixPartial 12 94032) = some ⟨12, 2, 0, 760563, 94032, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_94032_760563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94032 ⟨760563, by decide⟩ :=
  accepted_of_selected 12 94032 ⟨760563, by decide⟩ ⟨12, 2, 0, 760563, 94032, 3757, 65536⟩
    (by decide) selected_cut_30138

theorem selected_cut_30139 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 94033) = some ⟨12, 1, 0, 642341, 94033, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94033_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94033 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 94033 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 94033, 1, 65536⟩
    (by decide) selected_cut_30139

theorem selected_cut_30140 : selected 9 ⟨760623, by decide⟩
    (prefixPartial 12 94034) = some ⟨12, 2, 0, 760623, 94034, 3845, 65536⟩ := by
  decide +kernel

theorem context_12_94034_760623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94034 ⟨760623, by decide⟩ :=
  accepted_of_selected 12 94034 ⟨760623, by decide⟩ ⟨12, 2, 0, 760623, 94034, 3845, 65536⟩
    (by decide) selected_cut_30140

theorem selected_cut_30141 : selected 9 ⟨760672, by decide⟩
    (prefixPartial 12 94035) = some ⟨12, 2, 0, 760672, 94035, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_94035_760672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94035 ⟨760672, by decide⟩ :=
  accepted_of_selected 12 94035 ⟨760672, by decide⟩ ⟨12, 2, 0, 760672, 94035, 3665, 65536⟩
    (by decide) selected_cut_30141

theorem unmarked_context_11_23508_760673 : frontier 10 ⟨760673, by decide⟩
    (prefixCache 11 23508) (prefixPartial 11 23508) = false := by
  decide +kernel

theorem node_context_11_23508_760673 : EJMOriginalGlobalDAGData.nodes 10 ⟨760673, by decide⟩ =
    .split (coordinate 11) (![⟨760563, by decide⟩,⟨642341, by decide⟩,⟨760623, by decide⟩,⟨760672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23508_760673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23508 ⟨760673, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23508
    ⟨760673, by decide⟩ (by decide) (![⟨760563, by decide⟩,⟨642341, by decide⟩,⟨760623, by decide⟩,⟨760672, by decide⟩]) unmarked_context_11_23508_760673 node_context_11_23508_760673
  intro a
  fin_cases a
  · exact context_12_94032_760563
  · exact context_12_94033_642341
  · exact context_12_94034_760623
  · exact context_12_94035_760672

theorem selected_cut_30142 : selected 9 ⟨760720, by decide⟩
    (prefixPartial 12 94036) = some ⟨12, 2, 0, 760720, 94036, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_94036_760720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94036 ⟨760720, by decide⟩ :=
  accepted_of_selected 12 94036 ⟨760720, by decide⟩ ⟨12, 2, 0, 760720, 94036, 3825, 65536⟩
    (by decide) selected_cut_30142

theorem selected_cut_30143 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 94037) = some ⟨12, 1, 0, 642341, 94037, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94037_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94037 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 94037 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 94037, 1, 65536⟩
    (by decide) selected_cut_30143

theorem selected_cut_30144 : selected 9 ⟨760765, by decide⟩
    (prefixPartial 12 94038) = some ⟨12, 2, 0, 760765, 94038, 3669, 65536⟩ := by
  decide +kernel

theorem context_12_94038_760765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94038 ⟨760765, by decide⟩ :=
  accepted_of_selected 12 94038 ⟨760765, by decide⟩ ⟨12, 2, 0, 760765, 94038, 3669, 65536⟩
    (by decide) selected_cut_30144

theorem selected_cut_30145 : selected 9 ⟨760804, by decide⟩
    (prefixPartial 12 94039) = some ⟨12, 2, 0, 760804, 94039, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_94039_760804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94039 ⟨760804, by decide⟩ :=
  accepted_of_selected 12 94039 ⟨760804, by decide⟩ ⟨12, 2, 0, 760804, 94039, 3653, 65536⟩
    (by decide) selected_cut_30145

theorem unmarked_context_11_23509_760805 : frontier 10 ⟨760805, by decide⟩
    (prefixCache 11 23509) (prefixPartial 11 23509) = false := by
  decide +kernel

theorem node_context_11_23509_760805 : EJMOriginalGlobalDAGData.nodes 10 ⟨760805, by decide⟩ =
    .split (coordinate 11) (![⟨760720, by decide⟩,⟨642341, by decide⟩,⟨760765, by decide⟩,⟨760804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23509_760805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23509 ⟨760805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23509
    ⟨760805, by decide⟩ (by decide) (![⟨760720, by decide⟩,⟨642341, by decide⟩,⟨760765, by decide⟩,⟨760804, by decide⟩]) unmarked_context_11_23509_760805 node_context_11_23509_760805
  intro a
  fin_cases a
  · exact context_12_94036_760720
  · exact context_12_94037_642341
  · exact context_12_94038_760765
  · exact context_12_94039_760804

theorem selected_cut_30146 : selected 9 ⟨760856, by decide⟩
    (prefixPartial 12 94040) = some ⟨12, 2, 0, 760856, 94040, 3249, 65536⟩ := by
  decide +kernel

theorem context_12_94040_760856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94040 ⟨760856, by decide⟩ :=
  accepted_of_selected 12 94040 ⟨760856, by decide⟩ ⟨12, 2, 0, 760856, 94040, 3249, 65536⟩
    (by decide) selected_cut_30146

theorem selected_cut_30147 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 94041) = some ⟨12, 1, 0, 642341, 94041, 1, 65536⟩ := by
  decide +kernel

theorem context_12_94041_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 94041 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 94041 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 94041, 1, 65536⟩
    (by decide) selected_cut_30147

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
