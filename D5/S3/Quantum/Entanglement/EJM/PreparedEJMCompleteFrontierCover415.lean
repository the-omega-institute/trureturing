/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover414
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_39843 : selected 8 ⟨1081035, by decide⟩
    (prefixPartial 13 1231893) = some ⟨13, 2, 0, 1081035, 1231893, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_1231893_1081035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231893 ⟨1081035, by decide⟩ :=
  accepted_of_selected 13 1231893 ⟨1081035, by decide⟩ ⟨13, 2, 0, 1081035, 1231893, 1201, 16384⟩
    (by decide) selected_cut_39843

theorem selected_cut_39844 : selected 8 ⟨1081047, by decide⟩
    (prefixPartial 13 1231894) = some ⟨13, 2, 0, 1081047, 1231894, 665, 16384⟩ := by
  decide +kernel

theorem context_13_1231894_1081047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231894 ⟨1081047, by decide⟩ :=
  accepted_of_selected 13 1231894 ⟨1081047, by decide⟩ ⟨13, 2, 0, 1081047, 1231894, 665, 16384⟩
    (by decide) selected_cut_39844

theorem selected_cut_39845 : selected 8 ⟨1081054, by decide⟩
    (prefixPartial 13 1231895) = some ⟨13, 2, 0, 1081054, 1231895, 509, 16384⟩ := by
  decide +kernel

theorem context_13_1231895_1081054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231895 ⟨1081054, by decide⟩ :=
  accepted_of_selected 13 1231895 ⟨1081054, by decide⟩ ⟨13, 2, 0, 1081054, 1231895, 509, 16384⟩
    (by decide) selected_cut_39845

theorem unmarked_context_12_307973_1081055 : frontier 9 ⟨1081055, by decide⟩
    (prefixCache 12 307973) (prefixPartial 12 307973) = false := by
  decide +kernel

theorem node_context_12_307973_1081055 : EJMOriginalGlobalDAGData.nodes 9 ⟨1081055, by decide⟩ =
    .split (coordinate 12) (![⟨1081014, by decide⟩,⟨1081035, by decide⟩,⟨1081047, by decide⟩,⟨1081054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307973_1081055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307973 ⟨1081055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307973
    ⟨1081055, by decide⟩ (by decide) (![⟨1081014, by decide⟩,⟨1081035, by decide⟩,⟨1081047, by decide⟩,⟨1081054, by decide⟩]) unmarked_context_12_307973_1081055 node_context_12_307973_1081055
  intro a
  fin_cases a
  · exact context_13_1231892_1081014
  · exact context_13_1231893_1081035
  · exact context_13_1231894_1081047
  · exact context_13_1231895_1081054

theorem selected_cut_39846 : selected 9 ⟨1081118, by decide⟩
    (prefixPartial 12 307974) = some ⟨12, 2, 0, 1081118, 307974, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_307974_1081118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307974 ⟨1081118, by decide⟩ :=
  accepted_of_selected 12 307974 ⟨1081118, by decide⟩ ⟨12, 2, 0, 1081118, 307974, 3909, 65536⟩
    (by decide) selected_cut_39846

theorem selected_cut_39847 : selected 9 ⟨1081169, by decide⟩
    (prefixPartial 12 307975) = some ⟨12, 2, 0, 1081169, 307975, 3477, 65536⟩ := by
  decide +kernel

theorem context_12_307975_1081169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307975 ⟨1081169, by decide⟩ :=
  accepted_of_selected 12 307975 ⟨1081169, by decide⟩ ⟨12, 2, 0, 1081169, 307975, 3477, 65536⟩
    (by decide) selected_cut_39847

theorem unmarked_context_11_76993_1081170 : frontier 10 ⟨1081170, by decide⟩
    (prefixCache 11 76993) (prefixPartial 11 76993) = false := by
  decide +kernel

theorem node_context_11_76993_1081170 : EJMOriginalGlobalDAGData.nodes 10 ⟨1081170, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1081055, by decide⟩,⟨1081118, by decide⟩,⟨1081169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76993_1081170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76993 ⟨1081170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76993
    ⟨1081170, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1081055, by decide⟩,⟨1081118, by decide⟩,⟨1081169, by decide⟩]) unmarked_context_11_76993_1081170 node_context_11_76993_1081170
  intro a
  fin_cases a
  · exact context_12_307972_34034
  · exact context_12_307973_1081055
  · exact context_12_307974_1081118
  · exact context_12_307975_1081169

theorem selected_cut_39848 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 307976) = some ⟨12, 1, 0, 34034, 307976, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307976_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307976 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 307976 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 307976, 1, 65536⟩
    (by decide) selected_cut_39848

theorem selected_cut_39849 : selected 9 ⟨1081230, by decide⟩
    (prefixPartial 12 307977) = some ⟨12, 2, 0, 1081230, 307977, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_307977_1081230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307977 ⟨1081230, by decide⟩ :=
  accepted_of_selected 12 307977 ⟨1081230, by decide⟩ ⟨12, 2, 0, 1081230, 307977, 3917, 65536⟩
    (by decide) selected_cut_39849

theorem selected_cut_39850 : selected 9 ⟨1081287, by decide⟩
    (prefixPartial 12 307978) = some ⟨12, 2, 0, 1081287, 307978, 3605, 65536⟩ := by
  decide +kernel

theorem context_12_307978_1081287 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307978 ⟨1081287, by decide⟩ :=
  accepted_of_selected 12 307978 ⟨1081287, by decide⟩ ⟨12, 2, 0, 1081287, 307978, 3605, 65536⟩
    (by decide) selected_cut_39850

theorem selected_cut_39851 : selected 9 ⟨1081335, by decide⟩
    (prefixPartial 12 307979) = some ⟨12, 2, 0, 1081335, 307979, 3345, 65536⟩ := by
  decide +kernel

theorem context_12_307979_1081335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307979 ⟨1081335, by decide⟩ :=
  accepted_of_selected 12 307979 ⟨1081335, by decide⟩ ⟨12, 2, 0, 1081335, 307979, 3345, 65536⟩
    (by decide) selected_cut_39851

theorem unmarked_context_11_76994_1081336 : frontier 10 ⟨1081336, by decide⟩
    (prefixCache 11 76994) (prefixPartial 11 76994) = false := by
  decide +kernel

theorem node_context_11_76994_1081336 : EJMOriginalGlobalDAGData.nodes 10 ⟨1081336, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1081230, by decide⟩,⟨1081287, by decide⟩,⟨1081335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76994_1081336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76994 ⟨1081336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76994
    ⟨1081336, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1081230, by decide⟩,⟨1081287, by decide⟩,⟨1081335, by decide⟩]) unmarked_context_11_76994_1081336 node_context_11_76994_1081336
  intro a
  fin_cases a
  · exact context_12_307976_34034
  · exact context_12_307977_1081230
  · exact context_12_307978_1081287
  · exact context_12_307979_1081335

theorem selected_cut_39852 : selected 8 ⟨1081389, by decide⟩
    (prefixPartial 13 1231920) = some ⟨13, 2, 0, 1081389, 1231920, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_1231920_1081389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231920 ⟨1081389, by decide⟩ :=
  accepted_of_selected 13 1231920 ⟨1081389, by decide⟩ ⟨13, 2, 0, 1081389, 1231920, 1729, 16384⟩
    (by decide) selected_cut_39852

theorem selected_cut_39853 : selected 8 ⟨1081425, by decide⟩
    (prefixPartial 13 1231921) = some ⟨13, 2, 0, 1081425, 1231921, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_1231921_1081425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231921 ⟨1081425, by decide⟩ :=
  accepted_of_selected 13 1231921 ⟨1081425, by decide⟩ ⟨13, 2, 0, 1081425, 1231921, 1693, 16384⟩
    (by decide) selected_cut_39853

theorem selected_cut_39854 : selected 8 ⟨1081450, by decide⟩
    (prefixPartial 13 1231922) = some ⟨13, 2, 0, 1081450, 1231922, 961, 16384⟩ := by
  decide +kernel

theorem context_13_1231922_1081450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231922 ⟨1081450, by decide⟩ :=
  accepted_of_selected 13 1231922 ⟨1081450, by decide⟩ ⟨13, 2, 0, 1081450, 1231922, 961, 16384⟩
    (by decide) selected_cut_39854

theorem selected_cut_39855 : selected 8 ⟨1081464, by decide⟩
    (prefixPartial 13 1231923) = some ⟨13, 2, 0, 1081464, 1231923, 589, 16384⟩ := by
  decide +kernel

theorem context_13_1231923_1081464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231923 ⟨1081464, by decide⟩ :=
  accepted_of_selected 13 1231923 ⟨1081464, by decide⟩ ⟨13, 2, 0, 1081464, 1231923, 589, 16384⟩
    (by decide) selected_cut_39855

theorem unmarked_context_12_307980_1081465 : frontier 9 ⟨1081465, by decide⟩
    (prefixCache 12 307980) (prefixPartial 12 307980) = false := by
  decide +kernel

theorem node_context_12_307980_1081465 : EJMOriginalGlobalDAGData.nodes 9 ⟨1081465, by decide⟩ =
    .split (coordinate 12) (![⟨1081389, by decide⟩,⟨1081425, by decide⟩,⟨1081450, by decide⟩,⟨1081464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307980_1081465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307980 ⟨1081465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307980
    ⟨1081465, by decide⟩ (by decide) (![⟨1081389, by decide⟩,⟨1081425, by decide⟩,⟨1081450, by decide⟩,⟨1081464, by decide⟩]) unmarked_context_12_307980_1081465 node_context_12_307980_1081465
  intro a
  fin_cases a
  · exact context_13_1231920_1081389
  · exact context_13_1231921_1081425
  · exact context_13_1231922_1081450
  · exact context_13_1231923_1081464

theorem selected_cut_39856 : selected 9 ⟨1081528, by decide⟩
    (prefixPartial 12 307981) = some ⟨12, 2, 0, 1081528, 307981, 4093, 65536⟩ := by
  decide +kernel

theorem context_12_307981_1081528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307981 ⟨1081528, by decide⟩ :=
  accepted_of_selected 12 307981 ⟨1081528, by decide⟩ ⟨12, 2, 0, 1081528, 307981, 4093, 65536⟩
    (by decide) selected_cut_39856

theorem selected_cut_39857 : selected 9 ⟨1081595, by decide⟩
    (prefixPartial 12 307982) = some ⟨12, 2, 0, 1081595, 307982, 3993, 65536⟩ := by
  decide +kernel

theorem context_12_307982_1081595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307982 ⟨1081595, by decide⟩ :=
  accepted_of_selected 12 307982 ⟨1081595, by decide⟩ ⟨12, 2, 0, 1081595, 307982, 3993, 65536⟩
    (by decide) selected_cut_39857

theorem selected_cut_39858 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 307983) = some ⟨12, 1, 0, 903806, 307983, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307983_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307983 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 307983 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 307983, 1, 65536⟩
    (by decide) selected_cut_39858

theorem unmarked_context_11_76995_1081596 : frontier 10 ⟨1081596, by decide⟩
    (prefixCache 11 76995) (prefixPartial 11 76995) = false := by
  decide +kernel

theorem node_context_11_76995_1081596 : EJMOriginalGlobalDAGData.nodes 10 ⟨1081596, by decide⟩ =
    .split (coordinate 11) (![⟨1081465, by decide⟩,⟨1081528, by decide⟩,⟨1081595, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76995_1081596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76995 ⟨1081596, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76995
    ⟨1081596, by decide⟩ (by decide) (![⟨1081465, by decide⟩,⟨1081528, by decide⟩,⟨1081595, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_76995_1081596 node_context_11_76995_1081596
  intro a
  fin_cases a
  · exact context_12_307980_1081465
  · exact context_12_307981_1081528
  · exact context_12_307982_1081595
  · exact context_12_307983_903806

theorem unmarked_context_10_19248_1081597 : frontier 11 ⟨1081597, by decide⟩
    (prefixCache 10 19248) (prefixPartial 10 19248) = false := by
  decide +kernel

theorem node_context_10_19248_1081597 : EJMOriginalGlobalDAGData.nodes 11 ⟨1081597, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨1081170, by decide⟩,⟨1081336, by decide⟩,⟨1081596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19248_1081597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19248 ⟨1081597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19248
    ⟨1081597, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨1081170, by decide⟩,⟨1081336, by decide⟩,⟨1081596, by decide⟩]) unmarked_context_10_19248_1081597 node_context_10_19248_1081597
  intro a
  fin_cases a
  · exact context_11_76992_167448
  · exact context_11_76993_1081170
  · exact context_11_76994_1081336
  · exact context_11_76995_1081596

theorem selected_cut_39859 : selected 9 ⟨1081657, by decide⟩
    (prefixPartial 12 307984) = some ⟨12, 2, 0, 1081657, 307984, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_307984_1081657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307984 ⟨1081657, by decide⟩ :=
  accepted_of_selected 12 307984 ⟨1081657, by decide⟩ ⟨12, 2, 0, 1081657, 307984, 2157, 65536⟩
    (by decide) selected_cut_39859

theorem selected_cut_39860 : selected 9 ⟨1081696, by decide⟩
    (prefixPartial 12 307985) = some ⟨12, 2, 0, 1081696, 307985, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_307985_1081696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307985 ⟨1081696, by decide⟩ :=
  accepted_of_selected 12 307985 ⟨1081696, by decide⟩ ⟨12, 2, 0, 1081696, 307985, 2937, 65536⟩
    (by decide) selected_cut_39860

theorem selected_cut_39861 : selected 9 ⟨1081734, by decide⟩
    (prefixPartial 12 307986) = some ⟨12, 2, 0, 1081734, 307986, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_307986_1081734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307986 ⟨1081734, by decide⟩ :=
  accepted_of_selected 12 307986 ⟨1081734, by decide⟩ ⟨12, 2, 0, 1081734, 307986, 2761, 65536⟩
    (by decide) selected_cut_39861

theorem selected_cut_39862 : selected 9 ⟨1081768, by decide⟩
    (prefixPartial 12 307987) = some ⟨12, 2, 0, 1081768, 307987, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_307987_1081768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307987 ⟨1081768, by decide⟩ :=
  accepted_of_selected 12 307987 ⟨1081768, by decide⟩ ⟨12, 2, 0, 1081768, 307987, 2705, 65536⟩
    (by decide) selected_cut_39862

theorem unmarked_context_11_76996_1081769 : frontier 10 ⟨1081769, by decide⟩
    (prefixCache 11 76996) (prefixPartial 11 76996) = false := by
  decide +kernel

theorem node_context_11_76996_1081769 : EJMOriginalGlobalDAGData.nodes 10 ⟨1081769, by decide⟩ =
    .split (coordinate 11) (![⟨1081657, by decide⟩,⟨1081696, by decide⟩,⟨1081734, by decide⟩,⟨1081768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76996_1081769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76996 ⟨1081769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76996
    ⟨1081769, by decide⟩ (by decide) (![⟨1081657, by decide⟩,⟨1081696, by decide⟩,⟨1081734, by decide⟩,⟨1081768, by decide⟩]) unmarked_context_11_76996_1081769 node_context_11_76996_1081769
  intro a
  fin_cases a
  · exact context_12_307984_1081657
  · exact context_12_307985_1081696
  · exact context_12_307986_1081734
  · exact context_12_307987_1081768

theorem selected_cut_39863 : selected 8 ⟨1081809, by decide⟩
    (prefixPartial 13 1231952) = some ⟨13, 2, 0, 1081809, 1231952, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_1231952_1081809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231952 ⟨1081809, by decide⟩ :=
  accepted_of_selected 13 1231952 ⟨1081809, by decide⟩ ⟨13, 2, 0, 1081809, 1231952, 1853, 16384⟩
    (by decide) selected_cut_39863

theorem selected_cut_39864 : selected 8 ⟨1081826, by decide⟩
    (prefixPartial 13 1231953) = some ⟨13, 2, 0, 1081826, 1231953, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_1231953_1081826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231953 ⟨1081826, by decide⟩ :=
  accepted_of_selected 13 1231953 ⟨1081826, by decide⟩ ⟨13, 2, 0, 1081826, 1231953, 1041, 16384⟩
    (by decide) selected_cut_39864

theorem selected_cut_39865 : selected 8 ⟨1081840, by decide⟩
    (prefixPartial 13 1231954) = some ⟨13, 2, 0, 1081840, 1231954, 713, 16384⟩ := by
  decide +kernel

theorem context_13_1231954_1081840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231954 ⟨1081840, by decide⟩ :=
  accepted_of_selected 13 1231954 ⟨1081840, by decide⟩ ⟨13, 2, 0, 1081840, 1231954, 713, 16384⟩
    (by decide) selected_cut_39865

theorem selected_cut_39866 : selected 8 ⟨1081843, by decide⟩
    (prefixPartial 13 1231955) = some ⟨13, 2, 0, 1081843, 1231955, 501, 16384⟩ := by
  decide +kernel

theorem context_13_1231955_1081843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231955 ⟨1081843, by decide⟩ :=
  accepted_of_selected 13 1231955 ⟨1081843, by decide⟩ ⟨13, 2, 0, 1081843, 1231955, 501, 16384⟩
    (by decide) selected_cut_39866

theorem unmarked_context_12_307988_1081844 : frontier 9 ⟨1081844, by decide⟩
    (prefixCache 12 307988) (prefixPartial 12 307988) = false := by
  decide +kernel

theorem node_context_12_307988_1081844 : EJMOriginalGlobalDAGData.nodes 9 ⟨1081844, by decide⟩ =
    .split (coordinate 12) (![⟨1081809, by decide⟩,⟨1081826, by decide⟩,⟨1081840, by decide⟩,⟨1081843, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307988_1081844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307988 ⟨1081844, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307988
    ⟨1081844, by decide⟩ (by decide) (![⟨1081809, by decide⟩,⟨1081826, by decide⟩,⟨1081840, by decide⟩,⟨1081843, by decide⟩]) unmarked_context_12_307988_1081844 node_context_12_307988_1081844
  intro a
  fin_cases a
  · exact context_13_1231952_1081809
  · exact context_13_1231953_1081826
  · exact context_13_1231954_1081840
  · exact context_13_1231955_1081843

theorem selected_cut_39867 : selected 9 ⟨1081845, by decide⟩
    (prefixPartial 12 307989) = some ⟨12, 1, 0, 1081845, 307989, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307989_1081845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307989 ⟨1081845, by decide⟩ :=
  accepted_of_selected 12 307989 ⟨1081845, by decide⟩ ⟨12, 1, 0, 1081845, 307989, 1, 65536⟩
    (by decide) selected_cut_39867

theorem selected_cut_39868 : selected 9 ⟨1081900, by decide⟩
    (prefixPartial 12 307990) = some ⟨12, 2, 0, 1081900, 307990, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_307990_1081900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307990 ⟨1081900, by decide⟩ :=
  accepted_of_selected 12 307990 ⟨1081900, by decide⟩ ⟨12, 2, 0, 1081900, 307990, 3437, 65536⟩
    (by decide) selected_cut_39868

theorem selected_cut_39869 : selected 9 ⟨1081954, by decide⟩
    (prefixPartial 12 307991) = some ⟨12, 2, 0, 1081954, 307991, 3281, 65536⟩ := by
  decide +kernel

theorem context_12_307991_1081954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307991 ⟨1081954, by decide⟩ :=
  accepted_of_selected 12 307991 ⟨1081954, by decide⟩ ⟨12, 2, 0, 1081954, 307991, 3281, 65536⟩
    (by decide) selected_cut_39869

theorem unmarked_context_11_76997_1081955 : frontier 10 ⟨1081955, by decide⟩
    (prefixCache 11 76997) (prefixPartial 11 76997) = false := by
  decide +kernel

theorem node_context_11_76997_1081955 : EJMOriginalGlobalDAGData.nodes 10 ⟨1081955, by decide⟩ =
    .split (coordinate 11) (![⟨1081844, by decide⟩,⟨1081845, by decide⟩,⟨1081900, by decide⟩,⟨1081954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76997_1081955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76997 ⟨1081955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76997
    ⟨1081955, by decide⟩ (by decide) (![⟨1081844, by decide⟩,⟨1081845, by decide⟩,⟨1081900, by decide⟩,⟨1081954, by decide⟩]) unmarked_context_11_76997_1081955 node_context_11_76997_1081955
  intro a
  fin_cases a
  · exact context_12_307988_1081844
  · exact context_12_307989_1081845
  · exact context_12_307990_1081900
  · exact context_12_307991_1081954

theorem selected_cut_39870 : selected 9 ⟨1082008, by decide⟩
    (prefixPartial 12 307992) = some ⟨12, 2, 0, 1082008, 307992, 3785, 65536⟩ := by
  decide +kernel

theorem context_12_307992_1082008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307992 ⟨1082008, by decide⟩ :=
  accepted_of_selected 12 307992 ⟨1082008, by decide⟩ ⟨12, 2, 0, 1082008, 307992, 3785, 65536⟩
    (by decide) selected_cut_39870

theorem selected_cut_39871 : selected 9 ⟨1082055, by decide⟩
    (prefixPartial 12 307993) = some ⟨12, 2, 0, 1082055, 307993, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_307993_1082055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307993 ⟨1082055, by decide⟩ :=
  accepted_of_selected 12 307993 ⟨1082055, by decide⟩ ⟨12, 2, 0, 1082055, 307993, 3317, 65536⟩
    (by decide) selected_cut_39871

theorem selected_cut_39872 : selected 9 ⟨1082095, by decide⟩
    (prefixPartial 12 307994) = some ⟨12, 2, 0, 1082095, 307994, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_307994_1082095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307994 ⟨1082095, by decide⟩ :=
  accepted_of_selected 12 307994 ⟨1082095, by decide⟩ ⟨12, 2, 0, 1082095, 307994, 3013, 65536⟩
    (by decide) selected_cut_39872

theorem selected_cut_39873 : selected 9 ⟨1082140, by decide⟩
    (prefixPartial 12 307995) = some ⟨12, 2, 0, 1082140, 307995, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_307995_1082140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307995 ⟨1082140, by decide⟩ :=
  accepted_of_selected 12 307995 ⟨1082140, by decide⟩ ⟨12, 2, 0, 1082140, 307995, 3193, 65536⟩
    (by decide) selected_cut_39873

theorem unmarked_context_11_76998_1082141 : frontier 10 ⟨1082141, by decide⟩
    (prefixCache 11 76998) (prefixPartial 11 76998) = false := by
  decide +kernel

theorem node_context_11_76998_1082141 : EJMOriginalGlobalDAGData.nodes 10 ⟨1082141, by decide⟩ =
    .split (coordinate 11) (![⟨1082008, by decide⟩,⟨1082055, by decide⟩,⟨1082095, by decide⟩,⟨1082140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76998_1082141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76998 ⟨1082141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76998
    ⟨1082141, by decide⟩ (by decide) (![⟨1082008, by decide⟩,⟨1082055, by decide⟩,⟨1082095, by decide⟩,⟨1082140, by decide⟩]) unmarked_context_11_76998_1082141 node_context_11_76998_1082141
  intro a
  fin_cases a
  · exact context_12_307992_1082008
  · exact context_12_307993_1082055
  · exact context_12_307994_1082095
  · exact context_12_307995_1082140

theorem selected_cut_39874 : selected 8 ⟨1082166, by decide⟩
    (prefixPartial 13 1231984) = some ⟨13, 2, 0, 1082166, 1231984, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_1231984_1082166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231984 ⟨1082166, by decide⟩ :=
  accepted_of_selected 13 1231984 ⟨1082166, by decide⟩ ⟨13, 2, 0, 1082166, 1231984, 1361, 16384⟩
    (by decide) selected_cut_39874

theorem selected_cut_39875 : selected 8 ⟨1082186, by decide⟩
    (prefixPartial 13 1231985) = some ⟨13, 2, 0, 1082186, 1231985, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_1231985_1082186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231985 ⟨1082186, by decide⟩ :=
  accepted_of_selected 13 1231985 ⟨1082186, by decide⟩ ⟨13, 2, 0, 1082186, 1231985, 1437, 16384⟩
    (by decide) selected_cut_39875

theorem selected_cut_39876 : selected 8 ⟨1082199, by decide⟩
    (prefixPartial 13 1231986) = some ⟨13, 2, 0, 1082199, 1231986, 805, 16384⟩ := by
  decide +kernel

theorem context_13_1231986_1082199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231986 ⟨1082199, by decide⟩ :=
  accepted_of_selected 13 1231986 ⟨1082199, by decide⟩ ⟨13, 2, 0, 1082199, 1231986, 805, 16384⟩
    (by decide) selected_cut_39876

theorem selected_cut_39877 : selected 8 ⟨1082206, by decide⟩
    (prefixPartial 13 1231987) = some ⟨13, 2, 0, 1082206, 1231987, 553, 16384⟩ := by
  decide +kernel

theorem context_13_1231987_1082206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1231987 ⟨1082206, by decide⟩ :=
  accepted_of_selected 13 1231987 ⟨1082206, by decide⟩ ⟨13, 2, 0, 1082206, 1231987, 553, 16384⟩
    (by decide) selected_cut_39877

theorem unmarked_context_12_307996_1082207 : frontier 9 ⟨1082207, by decide⟩
    (prefixCache 12 307996) (prefixPartial 12 307996) = false := by
  decide +kernel

theorem node_context_12_307996_1082207 : EJMOriginalGlobalDAGData.nodes 9 ⟨1082207, by decide⟩ =
    .split (coordinate 12) (![⟨1082166, by decide⟩,⟨1082186, by decide⟩,⟨1082199, by decide⟩,⟨1082206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_307996_1082207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307996 ⟨1082207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 307996
    ⟨1082207, by decide⟩ (by decide) (![⟨1082166, by decide⟩,⟨1082186, by decide⟩,⟨1082199, by decide⟩,⟨1082206, by decide⟩]) unmarked_context_12_307996_1082207 node_context_12_307996_1082207
  intro a
  fin_cases a
  · exact context_13_1231984_1082166
  · exact context_13_1231985_1082186
  · exact context_13_1231986_1082199
  · exact context_13_1231987_1082206

theorem selected_cut_39878 : selected 9 ⟨1082266, by decide⟩
    (prefixPartial 12 307997) = some ⟨12, 2, 0, 1082266, 307997, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_307997_1082266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307997 ⟨1082266, by decide⟩ :=
  accepted_of_selected 12 307997 ⟨1082266, by decide⟩ ⟨12, 2, 0, 1082266, 307997, 3673, 65536⟩
    (by decide) selected_cut_39878

theorem selected_cut_39879 : selected 9 ⟨1082319, by decide⟩
    (prefixPartial 12 307998) = some ⟨12, 2, 0, 1082319, 307998, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_307998_1082319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307998 ⟨1082319, by decide⟩ :=
  accepted_of_selected 12 307998 ⟨1082319, by decide⟩ ⟨12, 2, 0, 1082319, 307998, 3517, 65536⟩
    (by decide) selected_cut_39879

theorem selected_cut_39880 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 307999) = some ⟨12, 1, 0, 903806, 307999, 1, 65536⟩ := by
  decide +kernel

theorem context_12_307999_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 307999 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 307999 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 307999, 1, 65536⟩
    (by decide) selected_cut_39880

theorem unmarked_context_11_76999_1082320 : frontier 10 ⟨1082320, by decide⟩
    (prefixCache 11 76999) (prefixPartial 11 76999) = false := by
  decide +kernel

theorem node_context_11_76999_1082320 : EJMOriginalGlobalDAGData.nodes 10 ⟨1082320, by decide⟩ =
    .split (coordinate 11) (![⟨1082207, by decide⟩,⟨1082266, by decide⟩,⟨1082319, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_76999_1082320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 76999 ⟨1082320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 76999
    ⟨1082320, by decide⟩ (by decide) (![⟨1082207, by decide⟩,⟨1082266, by decide⟩,⟨1082319, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_76999_1082320 node_context_11_76999_1082320
  intro a
  fin_cases a
  · exact context_12_307996_1082207
  · exact context_12_307997_1082266
  · exact context_12_307998_1082319
  · exact context_12_307999_903806

theorem unmarked_context_10_19249_1082321 : frontier 11 ⟨1082321, by decide⟩
    (prefixCache 10 19249) (prefixPartial 10 19249) = false := by
  decide +kernel

theorem node_context_10_19249_1082321 : EJMOriginalGlobalDAGData.nodes 11 ⟨1082321, by decide⟩ =
    .split (coordinate 10) (![⟨1081769, by decide⟩,⟨1081955, by decide⟩,⟨1082141, by decide⟩,⟨1082320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19249_1082321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19249 ⟨1082321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19249
    ⟨1082321, by decide⟩ (by decide) (![⟨1081769, by decide⟩,⟨1081955, by decide⟩,⟨1082141, by decide⟩,⟨1082320, by decide⟩]) unmarked_context_10_19249_1082321 node_context_10_19249_1082321
  intro a
  fin_cases a
  · exact context_11_76996_1081769
  · exact context_11_76997_1081955
  · exact context_11_76998_1082141
  · exact context_11_76999_1082320

theorem selected_cut_39881 : selected 9 ⟨1082322, by decide⟩
    (prefixPartial 12 308000) = some ⟨12, 1, 0, 1082322, 308000, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308000_1082322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308000 ⟨1082322, by decide⟩ :=
  accepted_of_selected 12 308000 ⟨1082322, by decide⟩ ⟨12, 1, 0, 1082322, 308000, 1, 65536⟩
    (by decide) selected_cut_39881

theorem selected_cut_39882 : selected 9 ⟨1082363, by decide⟩
    (prefixPartial 12 308001) = some ⟨12, 2, 0, 1082363, 308001, 2681, 65536⟩ := by
  decide +kernel

theorem context_12_308001_1082363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308001 ⟨1082363, by decide⟩ :=
  accepted_of_selected 12 308001 ⟨1082363, by decide⟩ ⟨12, 2, 0, 1082363, 308001, 2681, 65536⟩
    (by decide) selected_cut_39882

theorem selected_cut_39883 : selected 9 ⟨1082402, by decide⟩
    (prefixPartial 12 308002) = some ⟨12, 2, 0, 1082402, 308002, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_308002_1082402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308002 ⟨1082402, by decide⟩ :=
  accepted_of_selected 12 308002 ⟨1082402, by decide⟩ ⟨12, 2, 0, 1082402, 308002, 2597, 65536⟩
    (by decide) selected_cut_39883

theorem selected_cut_39884 : selected 9 ⟨1082434, by decide⟩
    (prefixPartial 12 308003) = some ⟨12, 2, 0, 1082434, 308003, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_308003_1082434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308003 ⟨1082434, by decide⟩ :=
  accepted_of_selected 12 308003 ⟨1082434, by decide⟩ ⟨12, 2, 0, 1082434, 308003, 2437, 65536⟩
    (by decide) selected_cut_39884

theorem unmarked_context_11_77000_1082435 : frontier 10 ⟨1082435, by decide⟩
    (prefixCache 11 77000) (prefixPartial 11 77000) = false := by
  decide +kernel

theorem node_context_11_77000_1082435 : EJMOriginalGlobalDAGData.nodes 10 ⟨1082435, by decide⟩ =
    .split (coordinate 11) (![⟨1082322, by decide⟩,⟨1082363, by decide⟩,⟨1082402, by decide⟩,⟨1082434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77000_1082435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77000 ⟨1082435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77000
    ⟨1082435, by decide⟩ (by decide) (![⟨1082322, by decide⟩,⟨1082363, by decide⟩,⟨1082402, by decide⟩,⟨1082434, by decide⟩]) unmarked_context_11_77000_1082435 node_context_11_77000_1082435
  intro a
  fin_cases a
  · exact context_12_308000_1082322
  · exact context_12_308001_1082363
  · exact context_12_308002_1082402
  · exact context_12_308003_1082434

theorem selected_cut_39885 : selected 9 ⟨1082492, by decide⟩
    (prefixPartial 12 308004) = some ⟨12, 2, 0, 1082492, 308004, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_308004_1082492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308004 ⟨1082492, by decide⟩ :=
  accepted_of_selected 12 308004 ⟨1082492, by decide⟩ ⟨12, 2, 0, 1082492, 308004, 3657, 65536⟩
    (by decide) selected_cut_39885

theorem selected_cut_39886 : selected 9 ⟨1082544, by decide⟩
    (prefixPartial 12 308005) = some ⟨12, 2, 0, 1082544, 308005, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_308005_1082544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308005 ⟨1082544, by decide⟩ :=
  accepted_of_selected 12 308005 ⟨1082544, by decide⟩ ⟨12, 2, 0, 1082544, 308005, 3437, 65536⟩
    (by decide) selected_cut_39886

theorem selected_cut_39887 : selected 9 ⟨1082587, by decide⟩
    (prefixPartial 12 308006) = some ⟨12, 2, 0, 1082587, 308006, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_308006_1082587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308006 ⟨1082587, by decide⟩ :=
  accepted_of_selected 12 308006 ⟨1082587, by decide⟩ ⟨12, 2, 0, 1082587, 308006, 3101, 65536⟩
    (by decide) selected_cut_39887

theorem selected_cut_39888 : selected 9 ⟨1082624, by decide⟩
    (prefixPartial 12 308007) = some ⟨12, 2, 0, 1082624, 308007, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_308007_1082624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308007 ⟨1082624, by decide⟩ :=
  accepted_of_selected 12 308007 ⟨1082624, by decide⟩ ⟨12, 2, 0, 1082624, 308007, 2821, 65536⟩
    (by decide) selected_cut_39888

theorem unmarked_context_11_77001_1082625 : frontier 10 ⟨1082625, by decide⟩
    (prefixCache 11 77001) (prefixPartial 11 77001) = false := by
  decide +kernel

theorem node_context_11_77001_1082625 : EJMOriginalGlobalDAGData.nodes 10 ⟨1082625, by decide⟩ =
    .split (coordinate 11) (![⟨1082492, by decide⟩,⟨1082544, by decide⟩,⟨1082587, by decide⟩,⟨1082624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77001_1082625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77001 ⟨1082625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77001
    ⟨1082625, by decide⟩ (by decide) (![⟨1082492, by decide⟩,⟨1082544, by decide⟩,⟨1082587, by decide⟩,⟨1082624, by decide⟩]) unmarked_context_11_77001_1082625 node_context_11_77001_1082625
  intro a
  fin_cases a
  · exact context_12_308004_1082492
  · exact context_12_308005_1082544
  · exact context_12_308006_1082587
  · exact context_12_308007_1082624

theorem selected_cut_39889 : selected 9 ⟨1082680, by decide⟩
    (prefixPartial 12 308008) = some ⟨12, 2, 0, 1082680, 308008, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_308008_1082680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308008 ⟨1082680, by decide⟩ :=
  accepted_of_selected 12 308008 ⟨1082680, by decide⟩ ⟨12, 2, 0, 1082680, 308008, 3109, 65536⟩
    (by decide) selected_cut_39889

theorem selected_cut_39890 : selected 9 ⟨1082723, by decide⟩
    (prefixPartial 12 308009) = some ⟨12, 2, 0, 1082723, 308009, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_308009_1082723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308009 ⟨1082723, by decide⟩ :=
  accepted_of_selected 12 308009 ⟨1082723, by decide⟩ ⟨12, 2, 0, 1082723, 308009, 2909, 65536⟩
    (by decide) selected_cut_39890

theorem selected_cut_39891 : selected 9 ⟨1082724, by decide⟩
    (prefixPartial 12 308010) = some ⟨12, 1, 0, 1082724, 308010, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308010_1082724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308010 ⟨1082724, by decide⟩ :=
  accepted_of_selected 12 308010 ⟨1082724, by decide⟩ ⟨12, 1, 0, 1082724, 308010, 1, 65536⟩
    (by decide) selected_cut_39891

theorem selected_cut_39892 : selected 9 ⟨1082762, by decide⟩
    (prefixPartial 12 308011) = some ⟨12, 2, 0, 1082762, 308011, 2709, 65536⟩ := by
  decide +kernel

theorem context_12_308011_1082762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308011 ⟨1082762, by decide⟩ :=
  accepted_of_selected 12 308011 ⟨1082762, by decide⟩ ⟨12, 2, 0, 1082762, 308011, 2709, 65536⟩
    (by decide) selected_cut_39892

theorem unmarked_context_11_77002_1082763 : frontier 10 ⟨1082763, by decide⟩
    (prefixCache 11 77002) (prefixPartial 11 77002) = false := by
  decide +kernel

theorem node_context_11_77002_1082763 : EJMOriginalGlobalDAGData.nodes 10 ⟨1082763, by decide⟩ =
    .split (coordinate 11) (![⟨1082680, by decide⟩,⟨1082723, by decide⟩,⟨1082724, by decide⟩,⟨1082762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77002_1082763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77002 ⟨1082763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77002
    ⟨1082763, by decide⟩ (by decide) (![⟨1082680, by decide⟩,⟨1082723, by decide⟩,⟨1082724, by decide⟩,⟨1082762, by decide⟩]) unmarked_context_11_77002_1082763 node_context_11_77002_1082763
  intro a
  fin_cases a
  · exact context_12_308008_1082680
  · exact context_12_308009_1082723
  · exact context_12_308010_1082724
  · exact context_12_308011_1082762

theorem selected_cut_39893 : selected 9 ⟨1082816, by decide⟩
    (prefixPartial 12 308012) = some ⟨12, 2, 0, 1082816, 308012, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_308012_1082816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308012 ⟨1082816, by decide⟩ :=
  accepted_of_selected 12 308012 ⟨1082816, by decide⟩ ⟨12, 2, 0, 1082816, 308012, 3293, 65536⟩
    (by decide) selected_cut_39893

theorem selected_cut_39894 : selected 9 ⟨1082856, by decide⟩
    (prefixPartial 12 308013) = some ⟨12, 2, 0, 1082856, 308013, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_308013_1082856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308013 ⟨1082856, by decide⟩ :=
  accepted_of_selected 12 308013 ⟨1082856, by decide⟩ ⟨12, 2, 0, 1082856, 308013, 3053, 65536⟩
    (by decide) selected_cut_39894

theorem selected_cut_39895 : selected 9 ⟨1082896, by decide⟩
    (prefixPartial 12 308014) = some ⟨12, 2, 0, 1082896, 308014, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_308014_1082896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308014 ⟨1082896, by decide⟩ :=
  accepted_of_selected 12 308014 ⟨1082896, by decide⟩ ⟨12, 2, 0, 1082896, 308014, 2977, 65536⟩
    (by decide) selected_cut_39895

theorem selected_cut_39896 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 308015) = some ⟨12, 1, 0, 903806, 308015, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308015_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308015 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 308015 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 308015, 1, 65536⟩
    (by decide) selected_cut_39896

theorem unmarked_context_11_77003_1082897 : frontier 10 ⟨1082897, by decide⟩
    (prefixCache 11 77003) (prefixPartial 11 77003) = false := by
  decide +kernel

theorem node_context_11_77003_1082897 : EJMOriginalGlobalDAGData.nodes 10 ⟨1082897, by decide⟩ =
    .split (coordinate 11) (![⟨1082816, by decide⟩,⟨1082856, by decide⟩,⟨1082896, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77003_1082897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77003 ⟨1082897, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77003
    ⟨1082897, by decide⟩ (by decide) (![⟨1082816, by decide⟩,⟨1082856, by decide⟩,⟨1082896, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77003_1082897 node_context_11_77003_1082897
  intro a
  fin_cases a
  · exact context_12_308012_1082816
  · exact context_12_308013_1082856
  · exact context_12_308014_1082896
  · exact context_12_308015_903806

theorem unmarked_context_10_19250_1082898 : frontier 11 ⟨1082898, by decide⟩
    (prefixCache 10 19250) (prefixPartial 10 19250) = false := by
  decide +kernel

theorem node_context_10_19250_1082898 : EJMOriginalGlobalDAGData.nodes 11 ⟨1082898, by decide⟩ =
    .split (coordinate 10) (![⟨1082435, by decide⟩,⟨1082625, by decide⟩,⟨1082763, by decide⟩,⟨1082897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19250_1082898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19250 ⟨1082898, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19250
    ⟨1082898, by decide⟩ (by decide) (![⟨1082435, by decide⟩,⟨1082625, by decide⟩,⟨1082763, by decide⟩,⟨1082897, by decide⟩]) unmarked_context_10_19250_1082898 node_context_10_19250_1082898
  intro a
  fin_cases a
  · exact context_11_77000_1082435
  · exact context_11_77001_1082625
  · exact context_11_77002_1082763
  · exact context_11_77003_1082897

theorem selected_cut_39897 : selected 9 ⟨1082322, by decide⟩
    (prefixPartial 12 308016) = some ⟨12, 1, 0, 1082322, 308016, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308016_1082322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308016 ⟨1082322, by decide⟩ :=
  accepted_of_selected 12 308016 ⟨1082322, by decide⟩ ⟨12, 1, 0, 1082322, 308016, 1, 65536⟩
    (by decide) selected_cut_39897

theorem selected_cut_39898 : selected 9 ⟨1082933, by decide⟩
    (prefixPartial 12 308017) = some ⟨12, 2, 0, 1082933, 308017, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_308017_1082933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308017 ⟨1082933, by decide⟩ :=
  accepted_of_selected 12 308017 ⟨1082933, by decide⟩ ⟨12, 2, 0, 1082933, 308017, 2469, 65536⟩
    (by decide) selected_cut_39898

theorem selected_cut_39899 : selected 9 ⟨1082968, by decide⟩
    (prefixPartial 12 308018) = some ⟨12, 2, 0, 1082968, 308018, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_308018_1082968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308018 ⟨1082968, by decide⟩ :=
  accepted_of_selected 12 308018 ⟨1082968, by decide⟩ ⟨12, 2, 0, 1082968, 308018, 2321, 65536⟩
    (by decide) selected_cut_39899

theorem selected_cut_39900 : selected 9 ⟨1083000, by decide⟩
    (prefixPartial 12 308019) = some ⟨12, 2, 0, 1083000, 308019, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_308019_1083000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308019 ⟨1083000, by decide⟩ :=
  accepted_of_selected 12 308019 ⟨1083000, by decide⟩ ⟨12, 2, 0, 1083000, 308019, 2093, 65536⟩
    (by decide) selected_cut_39900

theorem unmarked_context_11_77004_1083001 : frontier 10 ⟨1083001, by decide⟩
    (prefixCache 11 77004) (prefixPartial 11 77004) = false := by
  decide +kernel

theorem node_context_11_77004_1083001 : EJMOriginalGlobalDAGData.nodes 10 ⟨1083001, by decide⟩ =
    .split (coordinate 11) (![⟨1082322, by decide⟩,⟨1082933, by decide⟩,⟨1082968, by decide⟩,⟨1083000, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77004_1083001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77004 ⟨1083001, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77004
    ⟨1083001, by decide⟩ (by decide) (![⟨1082322, by decide⟩,⟨1082933, by decide⟩,⟨1082968, by decide⟩,⟨1083000, by decide⟩]) unmarked_context_11_77004_1083001 node_context_11_77004_1083001
  intro a
  fin_cases a
  · exact context_12_308016_1082322
  · exact context_12_308017_1082933
  · exact context_12_308018_1082968
  · exact context_12_308019_1083000

theorem selected_cut_39901 : selected 9 ⟨1083052, by decide⟩
    (prefixPartial 12 308020) = some ⟨12, 2, 0, 1083052, 308020, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_308020_1083052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308020 ⟨1083052, by decide⟩ :=
  accepted_of_selected 12 308020 ⟨1083052, by decide⟩ ⟨12, 2, 0, 1083052, 308020, 3189, 65536⟩
    (by decide) selected_cut_39901

theorem selected_cut_39902 : selected 9 ⟨1083088, by decide⟩
    (prefixPartial 12 308021) = some ⟨12, 2, 0, 1083088, 308021, 3133, 65536⟩ := by
  decide +kernel

theorem context_12_308021_1083088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308021 ⟨1083088, by decide⟩ :=
  accepted_of_selected 12 308021 ⟨1083088, by decide⟩ ⟨12, 2, 0, 1083088, 308021, 3133, 65536⟩
    (by decide) selected_cut_39902

theorem selected_cut_39903 : selected 9 ⟨1083127, by decide⟩
    (prefixPartial 12 308022) = some ⟨12, 2, 0, 1083127, 308022, 2817, 65536⟩ := by
  decide +kernel

theorem context_12_308022_1083127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308022 ⟨1083127, by decide⟩ :=
  accepted_of_selected 12 308022 ⟨1083127, by decide⟩ ⟨12, 2, 0, 1083127, 308022, 2817, 65536⟩
    (by decide) selected_cut_39903

theorem selected_cut_39904 : selected 9 ⟨1083161, by decide⟩
    (prefixPartial 12 308023) = some ⟨12, 2, 0, 1083161, 308023, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_308023_1083161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308023 ⟨1083161, by decide⟩ :=
  accepted_of_selected 12 308023 ⟨1083161, by decide⟩ ⟨12, 2, 0, 1083161, 308023, 2557, 65536⟩
    (by decide) selected_cut_39904

theorem unmarked_context_11_77005_1083162 : frontier 10 ⟨1083162, by decide⟩
    (prefixCache 11 77005) (prefixPartial 11 77005) = false := by
  decide +kernel

theorem node_context_11_77005_1083162 : EJMOriginalGlobalDAGData.nodes 10 ⟨1083162, by decide⟩ =
    .split (coordinate 11) (![⟨1083052, by decide⟩,⟨1083088, by decide⟩,⟨1083127, by decide⟩,⟨1083161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77005_1083162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77005 ⟨1083162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77005
    ⟨1083162, by decide⟩ (by decide) (![⟨1083052, by decide⟩,⟨1083088, by decide⟩,⟨1083127, by decide⟩,⟨1083161, by decide⟩]) unmarked_context_11_77005_1083162 node_context_11_77005_1083162
  intro a
  fin_cases a
  · exact context_12_308020_1083052
  · exact context_12_308021_1083088
  · exact context_12_308022_1083127
  · exact context_12_308023_1083161

theorem selected_cut_39905 : selected 9 ⟨1083201, by decide⟩
    (prefixPartial 12 308024) = some ⟨12, 2, 0, 1083201, 308024, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_308024_1083201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308024 ⟨1083201, by decide⟩ :=
  accepted_of_selected 12 308024 ⟨1083201, by decide⟩ ⟨12, 2, 0, 1083201, 308024, 2701, 65536⟩
    (by decide) selected_cut_39905

theorem selected_cut_39906 : selected 9 ⟨1083243, by decide⟩
    (prefixPartial 12 308025) = some ⟨12, 2, 0, 1083243, 308025, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_308025_1083243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308025 ⟨1083243, by decide⟩ :=
  accepted_of_selected 12 308025 ⟨1083243, by decide⟩ ⟨12, 2, 0, 1083243, 308025, 2609, 65536⟩
    (by decide) selected_cut_39906

theorem selected_cut_39907 : selected 9 ⟨1083279, by decide⟩
    (prefixPartial 12 308026) = some ⟨12, 2, 0, 1083279, 308026, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_308026_1083279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308026 ⟨1083279, by decide⟩ :=
  accepted_of_selected 12 308026 ⟨1083279, by decide⟩ ⟨12, 2, 0, 1083279, 308026, 2337, 65536⟩
    (by decide) selected_cut_39907

theorem selected_cut_39908 : selected 9 ⟨1083312, by decide⟩
    (prefixPartial 12 308027) = some ⟨12, 2, 0, 1083312, 308027, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_308027_1083312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308027 ⟨1083312, by decide⟩ :=
  accepted_of_selected 12 308027 ⟨1083312, by decide⟩ ⟨12, 2, 0, 1083312, 308027, 2345, 65536⟩
    (by decide) selected_cut_39908

theorem unmarked_context_11_77006_1083313 : frontier 10 ⟨1083313, by decide⟩
    (prefixCache 11 77006) (prefixPartial 11 77006) = false := by
  decide +kernel

theorem node_context_11_77006_1083313 : EJMOriginalGlobalDAGData.nodes 10 ⟨1083313, by decide⟩ =
    .split (coordinate 11) (![⟨1083201, by decide⟩,⟨1083243, by decide⟩,⟨1083279, by decide⟩,⟨1083312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77006_1083313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77006 ⟨1083313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77006
    ⟨1083313, by decide⟩ (by decide) (![⟨1083201, by decide⟩,⟨1083243, by decide⟩,⟨1083279, by decide⟩,⟨1083312, by decide⟩]) unmarked_context_11_77006_1083313 node_context_11_77006_1083313
  intro a
  fin_cases a
  · exact context_12_308024_1083201
  · exact context_12_308025_1083243
  · exact context_12_308026_1083279
  · exact context_12_308027_1083312

theorem selected_cut_39909 : selected 9 ⟨1083359, by decide⟩
    (prefixPartial 12 308028) = some ⟨12, 2, 0, 1083359, 308028, 2897, 65536⟩ := by
  decide +kernel

theorem context_12_308028_1083359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308028 ⟨1083359, by decide⟩ :=
  accepted_of_selected 12 308028 ⟨1083359, by decide⟩ ⟨12, 2, 0, 1083359, 308028, 2897, 65536⟩
    (by decide) selected_cut_39909

theorem selected_cut_39910 : selected 9 ⟨1083397, by decide⟩
    (prefixPartial 12 308029) = some ⟨12, 2, 0, 1083397, 308029, 2597, 65536⟩ := by
  decide +kernel

theorem context_12_308029_1083397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308029 ⟨1083397, by decide⟩ :=
  accepted_of_selected 12 308029 ⟨1083397, by decide⟩ ⟨12, 2, 0, 1083397, 308029, 2597, 65536⟩
    (by decide) selected_cut_39910

theorem selected_cut_39911 : selected 9 ⟨1083434, by decide⟩
    (prefixPartial 12 308030) = some ⟨12, 2, 0, 1083434, 308030, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_308030_1083434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308030 ⟨1083434, by decide⟩ :=
  accepted_of_selected 12 308030 ⟨1083434, by decide⟩ ⟨12, 2, 0, 1083434, 308030, 2633, 65536⟩
    (by decide) selected_cut_39911

theorem selected_cut_39912 : selected 9 ⟨429285, by decide⟩
    (prefixPartial 12 308031) = some ⟨12, 1, 0, 429285, 308031, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308031_429285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308031 ⟨429285, by decide⟩ :=
  accepted_of_selected 12 308031 ⟨429285, by decide⟩ ⟨12, 1, 0, 429285, 308031, 1, 65536⟩
    (by decide) selected_cut_39912

theorem unmarked_context_11_77007_1083435 : frontier 10 ⟨1083435, by decide⟩
    (prefixCache 11 77007) (prefixPartial 11 77007) = false := by
  decide +kernel

theorem node_context_11_77007_1083435 : EJMOriginalGlobalDAGData.nodes 10 ⟨1083435, by decide⟩ =
    .split (coordinate 11) (![⟨1083359, by decide⟩,⟨1083397, by decide⟩,⟨1083434, by decide⟩,⟨429285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77007_1083435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77007 ⟨1083435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77007
    ⟨1083435, by decide⟩ (by decide) (![⟨1083359, by decide⟩,⟨1083397, by decide⟩,⟨1083434, by decide⟩,⟨429285, by decide⟩]) unmarked_context_11_77007_1083435 node_context_11_77007_1083435
  intro a
  fin_cases a
  · exact context_12_308028_1083359
  · exact context_12_308029_1083397
  · exact context_12_308030_1083434
  · exact context_12_308031_429285

theorem unmarked_context_10_19251_1083436 : frontier 11 ⟨1083436, by decide⟩
    (prefixCache 10 19251) (prefixPartial 10 19251) = false := by
  decide +kernel

theorem node_context_10_19251_1083436 : EJMOriginalGlobalDAGData.nodes 11 ⟨1083436, by decide⟩ =
    .split (coordinate 10) (![⟨1083001, by decide⟩,⟨1083162, by decide⟩,⟨1083313, by decide⟩,⟨1083435, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19251_1083436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19251 ⟨1083436, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19251
    ⟨1083436, by decide⟩ (by decide) (![⟨1083001, by decide⟩,⟨1083162, by decide⟩,⟨1083313, by decide⟩,⟨1083435, by decide⟩]) unmarked_context_10_19251_1083436 node_context_10_19251_1083436
  intro a
  fin_cases a
  · exact context_11_77004_1083001
  · exact context_11_77005_1083162
  · exact context_11_77006_1083313
  · exact context_11_77007_1083435

theorem unmarked_context_9_4812_1083437 : frontier 12 ⟨1083437, by decide⟩
    (prefixCache 9 4812) (prefixPartial 9 4812) = false := by
  decide +kernel

theorem node_context_9_4812_1083437 : EJMOriginalGlobalDAGData.nodes 12 ⟨1083437, by decide⟩ =
    .split (coordinate 9) (![⟨1081597, by decide⟩,⟨1082321, by decide⟩,⟨1082898, by decide⟩,⟨1083436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4812_1083437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4812 ⟨1083437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4812
    ⟨1083437, by decide⟩ (by decide) (![⟨1081597, by decide⟩,⟨1082321, by decide⟩,⟨1082898, by decide⟩,⟨1083436, by decide⟩]) unmarked_context_9_4812_1083437 node_context_9_4812_1083437
  intro a
  fin_cases a
  · exact context_10_19248_1081597
  · exact context_10_19249_1082321
  · exact context_10_19250_1082898
  · exact context_10_19251_1083436

theorem selected_cut_39913 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 77008) = some ⟨11, 1, 0, 907917, 77008, 1, 262144⟩ := by
  decide +kernel

theorem context_11_77008_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77008 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 77008 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 77008, 1, 262144⟩
    (by decide) selected_cut_39913

theorem selected_cut_39914 : selected 9 ⟨1083481, by decide⟩
    (prefixPartial 12 308036) = some ⟨12, 2, 0, 1083481, 308036, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_308036_1083481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308036 ⟨1083481, by decide⟩ :=
  accepted_of_selected 12 308036 ⟨1083481, by decide⟩ ⟨12, 2, 0, 1083481, 308036, 2725, 65536⟩
    (by decide) selected_cut_39914

theorem selected_cut_39915 : selected 9 ⟨1083546, by decide⟩
    (prefixPartial 12 308037) = some ⟨12, 2, 0, 1083546, 308037, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_308037_1083546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308037 ⟨1083546, by decide⟩ :=
  accepted_of_selected 12 308037 ⟨1083546, by decide⟩ ⟨12, 2, 0, 1083546, 308037, 1821, 65536⟩
    (by decide) selected_cut_39915

theorem selected_cut_39916 : selected 9 ⟨1083585, by decide⟩
    (prefixPartial 12 308038) = some ⟨12, 2, 0, 1083585, 308038, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_308038_1083585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308038 ⟨1083585, by decide⟩ :=
  accepted_of_selected 12 308038 ⟨1083585, by decide⟩ ⟨12, 2, 0, 1083585, 308038, 2405, 65536⟩
    (by decide) selected_cut_39916

theorem selected_cut_39917 : selected 9 ⟨1083618, by decide⟩
    (prefixPartial 12 308039) = some ⟨12, 2, 0, 1083618, 308039, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_308039_1083618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308039 ⟨1083618, by decide⟩ :=
  accepted_of_selected 12 308039 ⟨1083618, by decide⟩ ⟨12, 2, 0, 1083618, 308039, 2381, 65536⟩
    (by decide) selected_cut_39917

theorem unmarked_context_11_77009_1083619 : frontier 10 ⟨1083619, by decide⟩
    (prefixCache 11 77009) (prefixPartial 11 77009) = false := by
  decide +kernel

theorem node_context_11_77009_1083619 : EJMOriginalGlobalDAGData.nodes 10 ⟨1083619, by decide⟩ =
    .split (coordinate 11) (![⟨1083481, by decide⟩,⟨1083546, by decide⟩,⟨1083585, by decide⟩,⟨1083618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77009_1083619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77009 ⟨1083619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77009
    ⟨1083619, by decide⟩ (by decide) (![⟨1083481, by decide⟩,⟨1083546, by decide⟩,⟨1083585, by decide⟩,⟨1083618, by decide⟩]) unmarked_context_11_77009_1083619 node_context_11_77009_1083619
  intro a
  fin_cases a
  · exact context_12_308036_1083481
  · exact context_12_308037_1083546
  · exact context_12_308038_1083585
  · exact context_12_308039_1083618

theorem selected_cut_39918 : selected 9 ⟨1083662, by decide⟩
    (prefixPartial 12 308040) = some ⟨12, 2, 0, 1083662, 308040, 2629, 65536⟩ := by
  decide +kernel

theorem context_12_308040_1083662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308040 ⟨1083662, by decide⟩ :=
  accepted_of_selected 12 308040 ⟨1083662, by decide⟩ ⟨12, 2, 0, 1083662, 308040, 2629, 65536⟩
    (by decide) selected_cut_39918

theorem selected_cut_39919 : selected 9 ⟨1083703, by decide⟩
    (prefixPartial 12 308041) = some ⟨12, 2, 0, 1083703, 308041, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_308041_1083703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308041 ⟨1083703, by decide⟩ :=
  accepted_of_selected 12 308041 ⟨1083703, by decide⟩ ⟨12, 2, 0, 1083703, 308041, 2353, 65536⟩
    (by decide) selected_cut_39919

theorem selected_cut_39920 : selected 9 ⟨1083738, by decide⟩
    (prefixPartial 12 308042) = some ⟨12, 2, 0, 1083738, 308042, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_308042_1083738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308042 ⟨1083738, by decide⟩ :=
  accepted_of_selected 12 308042 ⟨1083738, by decide⟩ ⟨12, 2, 0, 1083738, 308042, 2193, 65536⟩
    (by decide) selected_cut_39920

theorem selected_cut_39921 : selected 9 ⟨1083775, by decide⟩
    (prefixPartial 12 308043) = some ⟨12, 2, 0, 1083775, 308043, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_308043_1083775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308043 ⟨1083775, by decide⟩ :=
  accepted_of_selected 12 308043 ⟨1083775, by decide⟩ ⟨12, 2, 0, 1083775, 308043, 2285, 65536⟩
    (by decide) selected_cut_39921

theorem unmarked_context_11_77010_1083776 : frontier 10 ⟨1083776, by decide⟩
    (prefixCache 11 77010) (prefixPartial 11 77010) = false := by
  decide +kernel

theorem node_context_11_77010_1083776 : EJMOriginalGlobalDAGData.nodes 10 ⟨1083776, by decide⟩ =
    .split (coordinate 11) (![⟨1083662, by decide⟩,⟨1083703, by decide⟩,⟨1083738, by decide⟩,⟨1083775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77010_1083776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77010 ⟨1083776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77010
    ⟨1083776, by decide⟩ (by decide) (![⟨1083662, by decide⟩,⟨1083703, by decide⟩,⟨1083738, by decide⟩,⟨1083775, by decide⟩]) unmarked_context_11_77010_1083776 node_context_11_77010_1083776
  intro a
  fin_cases a
  · exact context_12_308040_1083662
  · exact context_12_308041_1083703
  · exact context_12_308042_1083738
  · exact context_12_308043_1083775

theorem selected_cut_39922 : selected 9 ⟨1083820, by decide⟩
    (prefixPartial 12 308044) = some ⟨12, 2, 0, 1083820, 308044, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_308044_1083820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308044 ⟨1083820, by decide⟩ :=
  accepted_of_selected 12 308044 ⟨1083820, by decide⟩ ⟨12, 2, 0, 1083820, 308044, 2649, 65536⟩
    (by decide) selected_cut_39922

theorem selected_cut_39923 : selected 9 ⟨1083854, by decide⟩
    (prefixPartial 12 308045) = some ⟨12, 2, 0, 1083854, 308045, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_308045_1083854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308045 ⟨1083854, by decide⟩ :=
  accepted_of_selected 12 308045 ⟨1083854, by decide⟩ ⟨12, 2, 0, 1083854, 308045, 2501, 65536⟩
    (by decide) selected_cut_39923

theorem selected_cut_39924 : selected 9 ⟨1083891, by decide⟩
    (prefixPartial 12 308046) = some ⟨12, 2, 0, 1083891, 308046, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_308046_1083891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308046 ⟨1083891, by decide⟩ :=
  accepted_of_selected 12 308046 ⟨1083891, by decide⟩ ⟨12, 2, 0, 1083891, 308046, 2317, 65536⟩
    (by decide) selected_cut_39924

theorem selected_cut_39925 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 308047) = some ⟨12, 1, 0, 903806, 308047, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308047_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308047 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 308047 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 308047, 1, 65536⟩
    (by decide) selected_cut_39925

theorem unmarked_context_11_77011_1083892 : frontier 10 ⟨1083892, by decide⟩
    (prefixCache 11 77011) (prefixPartial 11 77011) = false := by
  decide +kernel

theorem node_context_11_77011_1083892 : EJMOriginalGlobalDAGData.nodes 10 ⟨1083892, by decide⟩ =
    .split (coordinate 11) (![⟨1083820, by decide⟩,⟨1083854, by decide⟩,⟨1083891, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77011_1083892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77011 ⟨1083892, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77011
    ⟨1083892, by decide⟩ (by decide) (![⟨1083820, by decide⟩,⟨1083854, by decide⟩,⟨1083891, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_77011_1083892 node_context_11_77011_1083892
  intro a
  fin_cases a
  · exact context_12_308044_1083820
  · exact context_12_308045_1083854
  · exact context_12_308046_1083891
  · exact context_12_308047_903806

theorem unmarked_context_10_19252_1083893 : frontier 11 ⟨1083893, by decide⟩
    (prefixCache 10 19252) (prefixPartial 10 19252) = false := by
  decide +kernel

theorem node_context_10_19252_1083893 : EJMOriginalGlobalDAGData.nodes 11 ⟨1083893, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1083619, by decide⟩,⟨1083776, by decide⟩,⟨1083892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_19252_1083893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19252 ⟨1083893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 19252
    ⟨1083893, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1083619, by decide⟩,⟨1083776, by decide⟩,⟨1083892, by decide⟩]) unmarked_context_10_19252_1083893 node_context_10_19252_1083893
  intro a
  fin_cases a
  · exact context_11_77008_907917
  · exact context_11_77009_1083619
  · exact context_11_77010_1083776
  · exact context_11_77011_1083892

theorem selected_cut_39926 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 19253) = some ⟨10, 1, 0, 893098, 19253, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_19253_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 19253 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 19253 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 19253, 1, 1048576⟩
    (by decide) selected_cut_39926

theorem selected_cut_39927 : selected 9 ⟨1083918, by decide⟩
    (prefixPartial 12 308064) = some ⟨12, 2, 0, 1083918, 308064, 1753, 65536⟩ := by
  decide +kernel

theorem context_12_308064_1083918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308064 ⟨1083918, by decide⟩ :=
  accepted_of_selected 12 308064 ⟨1083918, by decide⟩ ⟨12, 2, 0, 1083918, 308064, 1753, 65536⟩
    (by decide) selected_cut_39927

theorem selected_cut_39928 : selected 9 ⟨1083943, by decide⟩
    (prefixPartial 12 308065) = some ⟨12, 2, 0, 1083943, 308065, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_308065_1083943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308065 ⟨1083943, by decide⟩ :=
  accepted_of_selected 12 308065 ⟨1083943, by decide⟩ ⟨12, 2, 0, 1083943, 308065, 1857, 65536⟩
    (by decide) selected_cut_39928

theorem selected_cut_39929 : selected 9 ⟨1083969, by decide⟩
    (prefixPartial 12 308066) = some ⟨12, 2, 0, 1083969, 308066, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_308066_1083969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308066 ⟨1083969, by decide⟩ :=
  accepted_of_selected 12 308066 ⟨1083969, by decide⟩ ⟨12, 2, 0, 1083969, 308066, 1809, 65536⟩
    (by decide) selected_cut_39929

theorem selected_cut_39930 : selected 9 ⟨1083992, by decide⟩
    (prefixPartial 12 308067) = some ⟨12, 2, 0, 1083992, 308067, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_308067_1083992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308067 ⟨1083992, by decide⟩ :=
  accepted_of_selected 12 308067 ⟨1083992, by decide⟩ ⟨12, 2, 0, 1083992, 308067, 1657, 65536⟩
    (by decide) selected_cut_39930

theorem unmarked_context_11_77016_1083993 : frontier 10 ⟨1083993, by decide⟩
    (prefixCache 11 77016) (prefixPartial 11 77016) = false := by
  decide +kernel

theorem node_context_11_77016_1083993 : EJMOriginalGlobalDAGData.nodes 10 ⟨1083993, by decide⟩ =
    .split (coordinate 11) (![⟨1083918, by decide⟩,⟨1083943, by decide⟩,⟨1083969, by decide⟩,⟨1083992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77016_1083993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77016 ⟨1083993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77016
    ⟨1083993, by decide⟩ (by decide) (![⟨1083918, by decide⟩,⟨1083943, by decide⟩,⟨1083969, by decide⟩,⟨1083992, by decide⟩]) unmarked_context_11_77016_1083993 node_context_11_77016_1083993
  intro a
  fin_cases a
  · exact context_12_308064_1083918
  · exact context_12_308065_1083943
  · exact context_12_308066_1083969
  · exact context_12_308067_1083992

theorem selected_cut_39931 : selected 9 ⟨1084017, by decide⟩
    (prefixPartial 12 308068) = some ⟨12, 2, 0, 1084017, 308068, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_308068_1084017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308068 ⟨1084017, by decide⟩ :=
  accepted_of_selected 12 308068 ⟨1084017, by decide⟩ ⟨12, 2, 0, 1084017, 308068, 1785, 65536⟩
    (by decide) selected_cut_39931

theorem selected_cut_39932 : selected 9 ⟨1084018, by decide⟩
    (prefixPartial 12 308069) = some ⟨12, 1, 0, 1084018, 308069, 1, 65536⟩ := by
  decide +kernel

theorem context_12_308069_1084018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308069 ⟨1084018, by decide⟩ :=
  accepted_of_selected 12 308069 ⟨1084018, by decide⟩ ⟨12, 1, 0, 1084018, 308069, 1, 65536⟩
    (by decide) selected_cut_39932

theorem selected_cut_39933 : selected 9 ⟨1084047, by decide⟩
    (prefixPartial 12 308070) = some ⟨12, 2, 0, 1084047, 308070, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_308070_1084047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308070 ⟨1084047, by decide⟩ :=
  accepted_of_selected 12 308070 ⟨1084047, by decide⟩ ⟨12, 2, 0, 1084047, 308070, 1881, 65536⟩
    (by decide) selected_cut_39933

theorem selected_cut_39934 : selected 9 ⟨1084072, by decide⟩
    (prefixPartial 12 308071) = some ⟨12, 2, 0, 1084072, 308071, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_308071_1084072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308071 ⟨1084072, by decide⟩ :=
  accepted_of_selected 12 308071 ⟨1084072, by decide⟩ ⟨12, 2, 0, 1084072, 308071, 1845, 65536⟩
    (by decide) selected_cut_39934

theorem unmarked_context_11_77017_1084073 : frontier 10 ⟨1084073, by decide⟩
    (prefixCache 11 77017) (prefixPartial 11 77017) = false := by
  decide +kernel

theorem node_context_11_77017_1084073 : EJMOriginalGlobalDAGData.nodes 10 ⟨1084073, by decide⟩ =
    .split (coordinate 11) (![⟨1084017, by decide⟩,⟨1084018, by decide⟩,⟨1084047, by decide⟩,⟨1084072, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77017_1084073 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77017 ⟨1084073, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77017
    ⟨1084073, by decide⟩ (by decide) (![⟨1084017, by decide⟩,⟨1084018, by decide⟩,⟨1084047, by decide⟩,⟨1084072, by decide⟩]) unmarked_context_11_77017_1084073 node_context_11_77017_1084073
  intro a
  fin_cases a
  · exact context_12_308068_1084017
  · exact context_12_308069_1084018
  · exact context_12_308070_1084047
  · exact context_12_308071_1084072

theorem selected_cut_39935 : selected 9 ⟨1084098, by decide⟩
    (prefixPartial 12 308072) = some ⟨12, 2, 0, 1084098, 308072, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_308072_1084098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308072 ⟨1084098, by decide⟩ :=
  accepted_of_selected 12 308072 ⟨1084098, by decide⟩ ⟨12, 2, 0, 1084098, 308072, 1797, 65536⟩
    (by decide) selected_cut_39935

theorem selected_cut_39936 : selected 9 ⟨1084129, by decide⟩
    (prefixPartial 12 308073) = some ⟨12, 2, 0, 1084129, 308073, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_308073_1084129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308073 ⟨1084129, by decide⟩ :=
  accepted_of_selected 12 308073 ⟨1084129, by decide⟩ ⟨12, 2, 0, 1084129, 308073, 1853, 65536⟩
    (by decide) selected_cut_39936

theorem selected_cut_39937 : selected 9 ⟨1084180, by decide⟩
    (prefixPartial 12 308074) = some ⟨12, 2, 0, 1084180, 308074, 689, 65536⟩ := by
  decide +kernel

theorem context_12_308074_1084180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308074 ⟨1084180, by decide⟩ :=
  accepted_of_selected 12 308074 ⟨1084180, by decide⟩ ⟨12, 2, 0, 1084180, 308074, 689, 65536⟩
    (by decide) selected_cut_39937

theorem selected_cut_39938 : selected 9 ⟨1084208, by decide⟩
    (prefixPartial 12 308075) = some ⟨12, 2, 0, 1084208, 308075, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_308075_1084208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308075 ⟨1084208, by decide⟩ :=
  accepted_of_selected 12 308075 ⟨1084208, by decide⟩ ⟨12, 2, 0, 1084208, 308075, 1817, 65536⟩
    (by decide) selected_cut_39938

theorem unmarked_context_11_77018_1084209 : frontier 10 ⟨1084209, by decide⟩
    (prefixCache 11 77018) (prefixPartial 11 77018) = false := by
  decide +kernel

theorem node_context_11_77018_1084209 : EJMOriginalGlobalDAGData.nodes 10 ⟨1084209, by decide⟩ =
    .split (coordinate 11) (![⟨1084098, by decide⟩,⟨1084129, by decide⟩,⟨1084180, by decide⟩,⟨1084208, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_77018_1084209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 77018 ⟨1084209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 77018
    ⟨1084209, by decide⟩ (by decide) (![⟨1084098, by decide⟩,⟨1084129, by decide⟩,⟨1084180, by decide⟩,⟨1084208, by decide⟩]) unmarked_context_11_77018_1084209 node_context_11_77018_1084209
  intro a
  fin_cases a
  · exact context_12_308072_1084098
  · exact context_12_308073_1084129
  · exact context_12_308074_1084180
  · exact context_12_308075_1084208

theorem selected_cut_39939 : selected 9 ⟨1084234, by decide⟩
    (prefixPartial 12 308076) = some ⟨12, 2, 0, 1084234, 308076, 1749, 65536⟩ := by
  decide +kernel

theorem context_12_308076_1084234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 308076 ⟨1084234, by decide⟩ :=
  accepted_of_selected 12 308076 ⟨1084234, by decide⟩ ⟨12, 2, 0, 1084234, 308076, 1749, 65536⟩
    (by decide) selected_cut_39939

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
