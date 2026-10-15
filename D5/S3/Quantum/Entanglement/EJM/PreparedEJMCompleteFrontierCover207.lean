/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover206
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_18116_508769 : frontier 10 ⟨508769, by decide⟩
    (prefixCache 11 18116) (prefixPartial 11 18116) = false := by
  decide +kernel

theorem node_context_11_18116_508769 : EJMOriginalGlobalDAGData.nodes 10 ⟨508769, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨508547, by decide⟩,⟨508669, by decide⟩,⟨508768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18116_508769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18116 ⟨508769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18116
    ⟨508769, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨508547, by decide⟩,⟨508669, by decide⟩,⟨508768, by decide⟩]) unmarked_context_11_18116_508769 node_context_11_18116_508769
  intro a
  fin_cases a
  · exact context_12_72464_435160
  · exact context_12_72465_508547
  · exact context_12_72466_508669
  · exact context_12_72467_508768

theorem selected_cut_19875 : selected 8 ⟨508825, by decide⟩
    (prefixPartial 13 289872) = some ⟨13, 2, 0, 508825, 289872, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_289872_508825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289872 ⟨508825, by decide⟩ :=
  accepted_of_selected 13 289872 ⟨508825, by decide⟩ ⟨13, 2, 0, 508825, 289872, 1273, 16384⟩
    (by decide) selected_cut_19875

theorem selected_cut_19876 : selected 8 ⟨508886, by decide⟩
    (prefixPartial 13 289873) = some ⟨13, 2, 0, 508886, 289873, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_289873_508886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289873 ⟨508886, by decide⟩ :=
  accepted_of_selected 13 289873 ⟨508886, by decide⟩ ⟨13, 2, 0, 508886, 289873, 1973, 16384⟩
    (by decide) selected_cut_19876

theorem selected_cut_19877 : selected 8 ⟨508984, by decide⟩
    (prefixPartial 13 289874) = some ⟨13, 2, 0, 508984, 289874, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_289874_508984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289874 ⟨508984, by decide⟩ :=
  accepted_of_selected 13 289874 ⟨508984, by decide⟩ ⟨13, 2, 0, 508984, 289874, 2305, 16384⟩
    (by decide) selected_cut_19877

theorem selected_cut_19878 : selected 8 ⟨508985, by decide⟩
    (prefixPartial 13 289875) = some ⟨13, 1, 0, 508985, 289875, 1, 16384⟩ := by
  decide +kernel

theorem context_13_289875_508985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289875 ⟨508985, by decide⟩ :=
  accepted_of_selected 13 289875 ⟨508985, by decide⟩ ⟨13, 1, 0, 508985, 289875, 1, 16384⟩
    (by decide) selected_cut_19878

theorem unmarked_context_12_72468_508986 : frontier 9 ⟨508986, by decide⟩
    (prefixCache 12 72468) (prefixPartial 12 72468) = false := by
  decide +kernel

theorem node_context_12_72468_508986 : EJMOriginalGlobalDAGData.nodes 9 ⟨508986, by decide⟩ =
    .split (coordinate 12) (![⟨508825, by decide⟩,⟨508886, by decide⟩,⟨508984, by decide⟩,⟨508985, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72468_508986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72468 ⟨508986, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72468
    ⟨508986, by decide⟩ (by decide) (![⟨508825, by decide⟩,⟨508886, by decide⟩,⟨508984, by decide⟩,⟨508985, by decide⟩]) unmarked_context_12_72468_508986 node_context_12_72468_508986
  intro a
  fin_cases a
  · exact context_13_289872_508825
  · exact context_13_289873_508886
  · exact context_13_289874_508984
  · exact context_13_289875_508985

theorem selected_cut_19879 : selected 8 ⟨509028, by decide⟩
    (prefixPartial 13 289876) = some ⟨13, 2, 0, 509028, 289876, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_289876_509028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289876 ⟨509028, by decide⟩ :=
  accepted_of_selected 13 289876 ⟨509028, by decide⟩ ⟨13, 2, 0, 509028, 289876, 2349, 16384⟩
    (by decide) selected_cut_19879

theorem selected_cut_19880 : selected 8 ⟨509059, by decide⟩
    (prefixPartial 13 289877) = some ⟨13, 2, 0, 509059, 289877, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_289877_509059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289877 ⟨509059, by decide⟩ :=
  accepted_of_selected 13 289877 ⟨509059, by decide⟩ ⟨13, 2, 0, 509059, 289877, 2213, 16384⟩
    (by decide) selected_cut_19880

theorem selected_cut_19881 : selected 8 ⟨509079, by decide⟩
    (prefixPartial 13 289878) = some ⟨13, 2, 0, 509079, 289878, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_289878_509079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289878 ⟨509079, by decide⟩ :=
  accepted_of_selected 13 289878 ⟨509079, by decide⟩ ⟨13, 2, 0, 509079, 289878, 1577, 16384⟩
    (by decide) selected_cut_19881

theorem selected_cut_19882 : selected 8 ⟨509086, by decide⟩
    (prefixPartial 13 289879) = some ⟨13, 2, 0, 509086, 289879, 721, 16384⟩ := by
  decide +kernel

theorem context_13_289879_509086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289879 ⟨509086, by decide⟩ :=
  accepted_of_selected 13 289879 ⟨509086, by decide⟩ ⟨13, 2, 0, 509086, 289879, 721, 16384⟩
    (by decide) selected_cut_19882

theorem unmarked_context_12_72469_509087 : frontier 9 ⟨509087, by decide⟩
    (prefixCache 12 72469) (prefixPartial 12 72469) = false := by
  decide +kernel

theorem node_context_12_72469_509087 : EJMOriginalGlobalDAGData.nodes 9 ⟨509087, by decide⟩ =
    .split (coordinate 12) (![⟨509028, by decide⟩,⟨509059, by decide⟩,⟨509079, by decide⟩,⟨509086, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72469_509087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72469 ⟨509087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72469
    ⟨509087, by decide⟩ (by decide) (![⟨509028, by decide⟩,⟨509059, by decide⟩,⟨509079, by decide⟩,⟨509086, by decide⟩]) unmarked_context_12_72469_509087 node_context_12_72469_509087
  intro a
  fin_cases a
  · exact context_13_289876_509028
  · exact context_13_289877_509059
  · exact context_13_289878_509079
  · exact context_13_289879_509086

theorem selected_cut_19883 : selected 8 ⟨509126, by decide⟩
    (prefixPartial 13 289880) = some ⟨13, 2, 0, 509126, 289880, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_289880_509126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289880 ⟨509126, by decide⟩ :=
  accepted_of_selected 13 289880 ⟨509126, by decide⟩ ⟨13, 2, 0, 509126, 289880, 2305, 16384⟩
    (by decide) selected_cut_19883

theorem selected_cut_19884 : selected 8 ⟨509155, by decide⟩
    (prefixPartial 13 289881) = some ⟨13, 2, 0, 509155, 289881, 2629, 16384⟩ := by
  decide +kernel

theorem context_13_289881_509155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289881 ⟨509155, by decide⟩ :=
  accepted_of_selected 13 289881 ⟨509155, by decide⟩ ⟨13, 2, 0, 509155, 289881, 2629, 16384⟩
    (by decide) selected_cut_19884

theorem selected_cut_19885 : selected 8 ⟨509189, by decide⟩
    (prefixPartial 13 289882) = some ⟨13, 2, 0, 509189, 289882, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_289882_509189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289882 ⟨509189, by decide⟩ :=
  accepted_of_selected 13 289882 ⟨509189, by decide⟩ ⟨13, 2, 0, 509189, 289882, 1973, 16384⟩
    (by decide) selected_cut_19885

theorem selected_cut_19886 : selected 8 ⟨509198, by decide⟩
    (prefixPartial 13 289883) = some ⟨13, 2, 0, 509198, 289883, 797, 16384⟩ := by
  decide +kernel

theorem context_13_289883_509198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289883 ⟨509198, by decide⟩ :=
  accepted_of_selected 13 289883 ⟨509198, by decide⟩ ⟨13, 2, 0, 509198, 289883, 797, 16384⟩
    (by decide) selected_cut_19886

theorem unmarked_context_12_72470_509199 : frontier 9 ⟨509199, by decide⟩
    (prefixCache 12 72470) (prefixPartial 12 72470) = false := by
  decide +kernel

theorem node_context_12_72470_509199 : EJMOriginalGlobalDAGData.nodes 9 ⟨509199, by decide⟩ =
    .split (coordinate 12) (![⟨509126, by decide⟩,⟨509155, by decide⟩,⟨509189, by decide⟩,⟨509198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72470_509199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72470 ⟨509199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72470
    ⟨509199, by decide⟩ (by decide) (![⟨509126, by decide⟩,⟨509155, by decide⟩,⟨509189, by decide⟩,⟨509198, by decide⟩]) unmarked_context_12_72470_509199 node_context_12_72470_509199
  intro a
  fin_cases a
  · exact context_13_289880_509126
  · exact context_13_289881_509155
  · exact context_13_289882_509189
  · exact context_13_289883_509198

theorem selected_cut_19887 : selected 8 ⟨509238, by decide⟩
    (prefixPartial 13 289884) = some ⟨13, 2, 0, 509238, 289884, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_289884_509238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289884 ⟨509238, by decide⟩ :=
  accepted_of_selected 13 289884 ⟨509238, by decide⟩ ⟨13, 2, 0, 509238, 289884, 2045, 16384⟩
    (by decide) selected_cut_19887

theorem selected_cut_19888 : selected 8 ⟨509272, by decide⟩
    (prefixPartial 13 289885) = some ⟨13, 2, 0, 509272, 289885, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_289885_509272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289885 ⟨509272, by decide⟩ :=
  accepted_of_selected 13 289885 ⟨509272, by decide⟩ ⟨13, 2, 0, 509272, 289885, 2557, 16384⟩
    (by decide) selected_cut_19888

theorem selected_cut_19889 : selected 8 ⟨509294, by decide⟩
    (prefixPartial 13 289886) = some ⟨13, 2, 0, 509294, 289886, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_289886_509294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289886 ⟨509294, by decide⟩ :=
  accepted_of_selected 13 289886 ⟨509294, by decide⟩ ⟨13, 2, 0, 509294, 289886, 1693, 16384⟩
    (by decide) selected_cut_19889

theorem selected_cut_19890 : selected 8 ⟨509300, by decide⟩
    (prefixPartial 13 289887) = some ⟨13, 2, 0, 509300, 289887, 609, 16384⟩ := by
  decide +kernel

theorem context_13_289887_509300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289887 ⟨509300, by decide⟩ :=
  accepted_of_selected 13 289887 ⟨509300, by decide⟩ ⟨13, 2, 0, 509300, 289887, 609, 16384⟩
    (by decide) selected_cut_19890

theorem unmarked_context_12_72471_509301 : frontier 9 ⟨509301, by decide⟩
    (prefixCache 12 72471) (prefixPartial 12 72471) = false := by
  decide +kernel

theorem node_context_12_72471_509301 : EJMOriginalGlobalDAGData.nodes 9 ⟨509301, by decide⟩ =
    .split (coordinate 12) (![⟨509238, by decide⟩,⟨509272, by decide⟩,⟨509294, by decide⟩,⟨509300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72471_509301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72471 ⟨509301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72471
    ⟨509301, by decide⟩ (by decide) (![⟨509238, by decide⟩,⟨509272, by decide⟩,⟨509294, by decide⟩,⟨509300, by decide⟩]) unmarked_context_12_72471_509301 node_context_12_72471_509301
  intro a
  fin_cases a
  · exact context_13_289884_509238
  · exact context_13_289885_509272
  · exact context_13_289886_509294
  · exact context_13_289887_509300

theorem unmarked_context_11_18117_509302 : frontier 10 ⟨509302, by decide⟩
    (prefixCache 11 18117) (prefixPartial 11 18117) = false := by
  decide +kernel

theorem node_context_11_18117_509302 : EJMOriginalGlobalDAGData.nodes 10 ⟨509302, by decide⟩ =
    .split (coordinate 11) (![⟨508986, by decide⟩,⟨509087, by decide⟩,⟨509199, by decide⟩,⟨509301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18117_509302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18117 ⟨509302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18117
    ⟨509302, by decide⟩ (by decide) (![⟨508986, by decide⟩,⟨509087, by decide⟩,⟨509199, by decide⟩,⟨509301, by decide⟩]) unmarked_context_11_18117_509302 node_context_11_18117_509302
  intro a
  fin_cases a
  · exact context_12_72468_508986
  · exact context_12_72469_509087
  · exact context_12_72470_509199
  · exact context_12_72471_509301

theorem selected_cut_19891 : selected 8 ⟨509359, by decide⟩
    (prefixPartial 13 289888) = some ⟨13, 2, 0, 509359, 289888, 2593, 16384⟩ := by
  decide +kernel

theorem context_13_289888_509359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289888 ⟨509359, by decide⟩ :=
  accepted_of_selected 13 289888 ⟨509359, by decide⟩ ⟨13, 2, 0, 509359, 289888, 2593, 16384⟩
    (by decide) selected_cut_19891

theorem selected_cut_19892 : selected 8 ⟨509403, by decide⟩
    (prefixPartial 13 289889) = some ⟨13, 2, 0, 509403, 289889, 3145, 16384⟩ := by
  decide +kernel

theorem context_13_289889_509403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289889 ⟨509403, by decide⟩ :=
  accepted_of_selected 13 289889 ⟨509403, by decide⟩ ⟨13, 2, 0, 509403, 289889, 3145, 16384⟩
    (by decide) selected_cut_19892

theorem selected_cut_19893 : selected 8 ⟨509440, by decide⟩
    (prefixPartial 13 289890) = some ⟨13, 2, 0, 509440, 289890, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_289890_509440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289890 ⟨509440, by decide⟩ :=
  accepted_of_selected 13 289890 ⟨509440, by decide⟩ ⟨13, 2, 0, 509440, 289890, 2189, 16384⟩
    (by decide) selected_cut_19893

theorem selected_cut_19894 : selected 8 ⟨509454, by decide⟩
    (prefixPartial 13 289891) = some ⟨13, 2, 0, 509454, 289891, 933, 16384⟩ := by
  decide +kernel

theorem context_13_289891_509454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289891 ⟨509454, by decide⟩ :=
  accepted_of_selected 13 289891 ⟨509454, by decide⟩ ⟨13, 2, 0, 509454, 289891, 933, 16384⟩
    (by decide) selected_cut_19894

theorem unmarked_context_12_72472_509455 : frontier 9 ⟨509455, by decide⟩
    (prefixCache 12 72472) (prefixPartial 12 72472) = false := by
  decide +kernel

theorem node_context_12_72472_509455 : EJMOriginalGlobalDAGData.nodes 9 ⟨509455, by decide⟩ =
    .split (coordinate 12) (![⟨509359, by decide⟩,⟨509403, by decide⟩,⟨509440, by decide⟩,⟨509454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72472_509455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72472 ⟨509455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72472
    ⟨509455, by decide⟩ (by decide) (![⟨509359, by decide⟩,⟨509403, by decide⟩,⟨509440, by decide⟩,⟨509454, by decide⟩]) unmarked_context_12_72472_509455 node_context_12_72472_509455
  intro a
  fin_cases a
  · exact context_13_289888_509359
  · exact context_13_289889_509403
  · exact context_13_289890_509440
  · exact context_13_289891_509454

theorem selected_cut_19895 : selected 8 ⟨509490, by decide⟩
    (prefixPartial 13 289892) = some ⟨13, 2, 0, 509490, 289892, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_289892_509490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289892 ⟨509490, by decide⟩ :=
  accepted_of_selected 13 289892 ⟨509490, by decide⟩ ⟨13, 2, 0, 509490, 289892, 1965, 16384⟩
    (by decide) selected_cut_19895

theorem selected_cut_19896 : selected 8 ⟨509522, by decide⟩
    (prefixPartial 13 289893) = some ⟨13, 2, 0, 509522, 289893, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_289893_509522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289893 ⟨509522, by decide⟩ :=
  accepted_of_selected 13 289893 ⟨509522, by decide⟩ ⟨13, 2, 0, 509522, 289893, 1969, 16384⟩
    (by decide) selected_cut_19896

theorem selected_cut_19897 : selected 8 ⟨509542, by decide⟩
    (prefixPartial 13 289894) = some ⟨13, 2, 0, 509542, 289894, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_289894_509542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289894 ⟨509542, by decide⟩ :=
  accepted_of_selected 13 289894 ⟨509542, by decide⟩ ⟨13, 2, 0, 509542, 289894, 1621, 16384⟩
    (by decide) selected_cut_19897

theorem selected_cut_19898 : selected 8 ⟨509551, by decide⟩
    (prefixPartial 13 289895) = some ⟨13, 2, 0, 509551, 289895, 709, 16384⟩ := by
  decide +kernel

theorem context_13_289895_509551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289895 ⟨509551, by decide⟩ :=
  accepted_of_selected 13 289895 ⟨509551, by decide⟩ ⟨13, 2, 0, 509551, 289895, 709, 16384⟩
    (by decide) selected_cut_19898

theorem unmarked_context_12_72473_509552 : frontier 9 ⟨509552, by decide⟩
    (prefixCache 12 72473) (prefixPartial 12 72473) = false := by
  decide +kernel

theorem node_context_12_72473_509552 : EJMOriginalGlobalDAGData.nodes 9 ⟨509552, by decide⟩ =
    .split (coordinate 12) (![⟨509490, by decide⟩,⟨509522, by decide⟩,⟨509542, by decide⟩,⟨509551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72473_509552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72473 ⟨509552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72473
    ⟨509552, by decide⟩ (by decide) (![⟨509490, by decide⟩,⟨509522, by decide⟩,⟨509542, by decide⟩,⟨509551, by decide⟩]) unmarked_context_12_72473_509552 node_context_12_72473_509552
  intro a
  fin_cases a
  · exact context_13_289892_509490
  · exact context_13_289893_509522
  · exact context_13_289894_509542
  · exact context_13_289895_509551

theorem selected_cut_19899 : selected 8 ⟨509585, by decide⟩
    (prefixPartial 13 289896) = some ⟨13, 2, 0, 509585, 289896, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_289896_509585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289896 ⟨509585, by decide⟩ :=
  accepted_of_selected 13 289896 ⟨509585, by decide⟩ ⟨13, 2, 0, 509585, 289896, 1957, 16384⟩
    (by decide) selected_cut_19899

theorem selected_cut_19900 : selected 8 ⟨509618, by decide⟩
    (prefixPartial 13 289897) = some ⟨13, 2, 0, 509618, 289897, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_289897_509618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289897 ⟨509618, by decide⟩ :=
  accepted_of_selected 13 289897 ⟨509618, by decide⟩ ⟨13, 2, 0, 509618, 289897, 2577, 16384⟩
    (by decide) selected_cut_19900

theorem selected_cut_19901 : selected 8 ⟨509637, by decide⟩
    (prefixPartial 13 289898) = some ⟨13, 2, 0, 509637, 289898, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_289898_509637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289898 ⟨509637, by decide⟩ :=
  accepted_of_selected 13 289898 ⟨509637, by decide⟩ ⟨13, 2, 0, 509637, 289898, 1813, 16384⟩
    (by decide) selected_cut_19901

theorem selected_cut_19902 : selected 8 ⟨509648, by decide⟩
    (prefixPartial 13 289899) = some ⟨13, 2, 0, 509648, 289899, 801, 16384⟩ := by
  decide +kernel

theorem context_13_289899_509648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289899 ⟨509648, by decide⟩ :=
  accepted_of_selected 13 289899 ⟨509648, by decide⟩ ⟨13, 2, 0, 509648, 289899, 801, 16384⟩
    (by decide) selected_cut_19902

theorem unmarked_context_12_72474_509649 : frontier 9 ⟨509649, by decide⟩
    (prefixCache 12 72474) (prefixPartial 12 72474) = false := by
  decide +kernel

theorem node_context_12_72474_509649 : EJMOriginalGlobalDAGData.nodes 9 ⟨509649, by decide⟩ =
    .split (coordinate 12) (![⟨509585, by decide⟩,⟨509618, by decide⟩,⟨509637, by decide⟩,⟨509648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72474_509649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72474 ⟨509649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72474
    ⟨509649, by decide⟩ (by decide) (![⟨509585, by decide⟩,⟨509618, by decide⟩,⟨509637, by decide⟩,⟨509648, by decide⟩]) unmarked_context_12_72474_509649 node_context_12_72474_509649
  intro a
  fin_cases a
  · exact context_13_289896_509585
  · exact context_13_289897_509618
  · exact context_13_289898_509637
  · exact context_13_289899_509648

theorem selected_cut_19903 : selected 8 ⟨509676, by decide⟩
    (prefixPartial 13 289900) = some ⟨13, 2, 0, 509676, 289900, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_289900_509676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289900 ⟨509676, by decide⟩ :=
  accepted_of_selected 13 289900 ⟨509676, by decide⟩ ⟨13, 2, 0, 509676, 289900, 1589, 16384⟩
    (by decide) selected_cut_19903

theorem selected_cut_19904 : selected 8 ⟨509713, by decide⟩
    (prefixPartial 13 289901) = some ⟨13, 2, 0, 509713, 289901, 2569, 16384⟩ := by
  decide +kernel

theorem context_13_289901_509713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289901 ⟨509713, by decide⟩ :=
  accepted_of_selected 13 289901 ⟨509713, by decide⟩ ⟨13, 2, 0, 509713, 289901, 2569, 16384⟩
    (by decide) selected_cut_19904

theorem selected_cut_19905 : selected 8 ⟨509730, by decide⟩
    (prefixPartial 13 289902) = some ⟨13, 2, 0, 509730, 289902, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_289902_509730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289902 ⟨509730, by decide⟩ :=
  accepted_of_selected 13 289902 ⟨509730, by decide⟩ ⟨13, 2, 0, 509730, 289902, 1621, 16384⟩
    (by decide) selected_cut_19905

theorem selected_cut_19906 : selected 8 ⟨509738, by decide⟩
    (prefixPartial 13 289903) = some ⟨13, 2, 0, 509738, 289903, 657, 16384⟩ := by
  decide +kernel

theorem context_13_289903_509738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289903 ⟨509738, by decide⟩ :=
  accepted_of_selected 13 289903 ⟨509738, by decide⟩ ⟨13, 2, 0, 509738, 289903, 657, 16384⟩
    (by decide) selected_cut_19906

theorem unmarked_context_12_72475_509739 : frontier 9 ⟨509739, by decide⟩
    (prefixCache 12 72475) (prefixPartial 12 72475) = false := by
  decide +kernel

theorem node_context_12_72475_509739 : EJMOriginalGlobalDAGData.nodes 9 ⟨509739, by decide⟩ =
    .split (coordinate 12) (![⟨509676, by decide⟩,⟨509713, by decide⟩,⟨509730, by decide⟩,⟨509738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72475_509739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72475 ⟨509739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72475
    ⟨509739, by decide⟩ (by decide) (![⟨509676, by decide⟩,⟨509713, by decide⟩,⟨509730, by decide⟩,⟨509738, by decide⟩]) unmarked_context_12_72475_509739 node_context_12_72475_509739
  intro a
  fin_cases a
  · exact context_13_289900_509676
  · exact context_13_289901_509713
  · exact context_13_289902_509730
  · exact context_13_289903_509738

theorem unmarked_context_11_18118_509740 : frontier 10 ⟨509740, by decide⟩
    (prefixCache 11 18118) (prefixPartial 11 18118) = false := by
  decide +kernel

theorem node_context_11_18118_509740 : EJMOriginalGlobalDAGData.nodes 10 ⟨509740, by decide⟩ =
    .split (coordinate 11) (![⟨509455, by decide⟩,⟨509552, by decide⟩,⟨509649, by decide⟩,⟨509739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18118_509740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18118 ⟨509740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18118
    ⟨509740, by decide⟩ (by decide) (![⟨509455, by decide⟩,⟨509552, by decide⟩,⟨509649, by decide⟩,⟨509739, by decide⟩]) unmarked_context_11_18118_509740 node_context_11_18118_509740
  intro a
  fin_cases a
  · exact context_12_72472_509455
  · exact context_12_72473_509552
  · exact context_12_72474_509649
  · exact context_12_72475_509739

theorem selected_cut_19907 : selected 8 ⟨509778, by decide⟩
    (prefixPartial 13 289904) = some ⟨13, 2, 0, 509778, 289904, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_289904_509778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289904 ⟨509778, by decide⟩ :=
  accepted_of_selected 13 289904 ⟨509778, by decide⟩ ⟨13, 2, 0, 509778, 289904, 2301, 16384⟩
    (by decide) selected_cut_19907

theorem selected_cut_19908 : selected 8 ⟨509810, by decide⟩
    (prefixPartial 13 289905) = some ⟨13, 2, 0, 509810, 289905, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_289905_509810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289905 ⟨509810, by decide⟩ :=
  accepted_of_selected 13 289905 ⟨509810, by decide⟩ ⟨13, 2, 0, 509810, 289905, 2809, 16384⟩
    (by decide) selected_cut_19908

theorem selected_cut_19909 : selected 8 ⟨509841, by decide⟩
    (prefixPartial 13 289906) = some ⟨13, 2, 0, 509841, 289906, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_289906_509841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289906 ⟨509841, by decide⟩ :=
  accepted_of_selected 13 289906 ⟨509841, by decide⟩ ⟨13, 2, 0, 509841, 289906, 2349, 16384⟩
    (by decide) selected_cut_19909

theorem selected_cut_19910 : selected 8 ⟨509855, by decide⟩
    (prefixPartial 13 289907) = some ⟨13, 2, 0, 509855, 289907, 965, 16384⟩ := by
  decide +kernel

theorem context_13_289907_509855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289907 ⟨509855, by decide⟩ :=
  accepted_of_selected 13 289907 ⟨509855, by decide⟩ ⟨13, 2, 0, 509855, 289907, 965, 16384⟩
    (by decide) selected_cut_19910

theorem unmarked_context_12_72476_509856 : frontier 9 ⟨509856, by decide⟩
    (prefixCache 12 72476) (prefixPartial 12 72476) = false := by
  decide +kernel

theorem node_context_12_72476_509856 : EJMOriginalGlobalDAGData.nodes 9 ⟨509856, by decide⟩ =
    .split (coordinate 12) (![⟨509778, by decide⟩,⟨509810, by decide⟩,⟨509841, by decide⟩,⟨509855, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72476_509856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72476 ⟨509856, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72476
    ⟨509856, by decide⟩ (by decide) (![⟨509778, by decide⟩,⟨509810, by decide⟩,⟨509841, by decide⟩,⟨509855, by decide⟩]) unmarked_context_12_72476_509856 node_context_12_72476_509856
  intro a
  fin_cases a
  · exact context_13_289904_509778
  · exact context_13_289905_509810
  · exact context_13_289906_509841
  · exact context_13_289907_509855

theorem selected_cut_19911 : selected 8 ⟨509883, by decide⟩
    (prefixPartial 13 289908) = some ⟨13, 2, 0, 509883, 289908, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_289908_509883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289908 ⟨509883, by decide⟩ :=
  accepted_of_selected 13 289908 ⟨509883, by decide⟩ ⟨13, 2, 0, 509883, 289908, 1609, 16384⟩
    (by decide) selected_cut_19911

theorem selected_cut_19912 : selected 8 ⟨509910, by decide⟩
    (prefixPartial 13 289909) = some ⟨13, 2, 0, 509910, 289909, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_289909_509910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289909 ⟨509910, by decide⟩ :=
  accepted_of_selected 13 289909 ⟨509910, by decide⟩ ⟨13, 2, 0, 509910, 289909, 1837, 16384⟩
    (by decide) selected_cut_19912

theorem selected_cut_19913 : selected 8 ⟨509929, by decide⟩
    (prefixPartial 13 289910) = some ⟨13, 2, 0, 509929, 289910, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_289910_509929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289910 ⟨509929, by decide⟩ :=
  accepted_of_selected 13 289910 ⟨509929, by decide⟩ ⟨13, 2, 0, 509929, 289910, 1901, 16384⟩
    (by decide) selected_cut_19913

theorem selected_cut_19914 : selected 8 ⟨509937, by decide⟩
    (prefixPartial 13 289911) = some ⟨13, 2, 0, 509937, 289911, 681, 16384⟩ := by
  decide +kernel

theorem context_13_289911_509937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289911 ⟨509937, by decide⟩ :=
  accepted_of_selected 13 289911 ⟨509937, by decide⟩ ⟨13, 2, 0, 509937, 289911, 681, 16384⟩
    (by decide) selected_cut_19914

theorem unmarked_context_12_72477_509938 : frontier 9 ⟨509938, by decide⟩
    (prefixCache 12 72477) (prefixPartial 12 72477) = false := by
  decide +kernel

theorem node_context_12_72477_509938 : EJMOriginalGlobalDAGData.nodes 9 ⟨509938, by decide⟩ =
    .split (coordinate 12) (![⟨509883, by decide⟩,⟨509910, by decide⟩,⟨509929, by decide⟩,⟨509937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72477_509938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72477 ⟨509938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72477
    ⟨509938, by decide⟩ (by decide) (![⟨509883, by decide⟩,⟨509910, by decide⟩,⟨509929, by decide⟩,⟨509937, by decide⟩]) unmarked_context_12_72477_509938 node_context_12_72477_509938
  intro a
  fin_cases a
  · exact context_13_289908_509883
  · exact context_13_289909_509910
  · exact context_13_289910_509929
  · exact context_13_289911_509937

theorem selected_cut_19915 : selected 8 ⟨509961, by decide⟩
    (prefixPartial 13 289912) = some ⟨13, 2, 0, 509961, 289912, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_289912_509961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289912 ⟨509961, by decide⟩ :=
  accepted_of_selected 13 289912 ⟨509961, by decide⟩ ⟨13, 2, 0, 509961, 289912, 1721, 16384⟩
    (by decide) selected_cut_19915

theorem selected_cut_19916 : selected 8 ⟨509999, by decide⟩
    (prefixPartial 13 289913) = some ⟨13, 2, 0, 509999, 289913, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_289913_509999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289913 ⟨509999, by decide⟩ :=
  accepted_of_selected 13 289913 ⟨509999, by decide⟩ ⟨13, 2, 0, 509999, 289913, 2689, 16384⟩
    (by decide) selected_cut_19916

theorem selected_cut_19917 : selected 8 ⟨510026, by decide⟩
    (prefixPartial 13 289914) = some ⟨13, 2, 0, 510026, 289914, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_289914_510026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289914 ⟨510026, by decide⟩ :=
  accepted_of_selected 13 289914 ⟨510026, by decide⟩ ⟨13, 2, 0, 510026, 289914, 2017, 16384⟩
    (by decide) selected_cut_19917

theorem selected_cut_19918 : selected 8 ⟨510032, by decide⟩
    (prefixPartial 13 289915) = some ⟨13, 2, 0, 510032, 289915, 753, 16384⟩ := by
  decide +kernel

theorem context_13_289915_510032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289915 ⟨510032, by decide⟩ :=
  accepted_of_selected 13 289915 ⟨510032, by decide⟩ ⟨13, 2, 0, 510032, 289915, 753, 16384⟩
    (by decide) selected_cut_19918

theorem unmarked_context_12_72478_510033 : frontier 9 ⟨510033, by decide⟩
    (prefixCache 12 72478) (prefixPartial 12 72478) = false := by
  decide +kernel

theorem node_context_12_72478_510033 : EJMOriginalGlobalDAGData.nodes 9 ⟨510033, by decide⟩ =
    .split (coordinate 12) (![⟨509961, by decide⟩,⟨509999, by decide⟩,⟨510026, by decide⟩,⟨510032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72478_510033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72478 ⟨510033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72478
    ⟨510033, by decide⟩ (by decide) (![⟨509961, by decide⟩,⟨509999, by decide⟩,⟨510026, by decide⟩,⟨510032, by decide⟩]) unmarked_context_12_72478_510033 node_context_12_72478_510033
  intro a
  fin_cases a
  · exact context_13_289912_509961
  · exact context_13_289913_509999
  · exact context_13_289914_510026
  · exact context_13_289915_510032

theorem selected_cut_19919 : selected 8 ⟨510075, by decide⟩
    (prefixPartial 13 289916) = some ⟨13, 2, 0, 510075, 289916, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_289916_510075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289916 ⟨510075, by decide⟩ :=
  accepted_of_selected 13 289916 ⟨510075, by decide⟩ ⟨13, 2, 0, 510075, 289916, 2309, 16384⟩
    (by decide) selected_cut_19919

theorem selected_cut_19920 : selected 8 ⟨510142, by decide⟩
    (prefixPartial 13 289917) = some ⟨13, 2, 0, 510142, 289917, 3769, 16384⟩ := by
  decide +kernel

theorem context_13_289917_510142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289917 ⟨510142, by decide⟩ :=
  accepted_of_selected 13 289917 ⟨510142, by decide⟩ ⟨13, 2, 0, 510142, 289917, 3769, 16384⟩
    (by decide) selected_cut_19920

theorem selected_cut_19921 : selected 8 ⟨510217, by decide⟩
    (prefixPartial 13 289918) = some ⟨13, 2, 0, 510217, 289918, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_289918_510217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289918 ⟨510217, by decide⟩ :=
  accepted_of_selected 13 289918 ⟨510217, by decide⟩ ⟨13, 2, 0, 510217, 289918, 2877, 16384⟩
    (by decide) selected_cut_19921

theorem selected_cut_19922 : selected 8 ⟨510228, by decide⟩
    (prefixPartial 13 289919) = some ⟨13, 2, 0, 510228, 289919, 945, 16384⟩ := by
  decide +kernel

theorem context_13_289919_510228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289919 ⟨510228, by decide⟩ :=
  accepted_of_selected 13 289919 ⟨510228, by decide⟩ ⟨13, 2, 0, 510228, 289919, 945, 16384⟩
    (by decide) selected_cut_19922

theorem unmarked_context_12_72479_510229 : frontier 9 ⟨510229, by decide⟩
    (prefixCache 12 72479) (prefixPartial 12 72479) = false := by
  decide +kernel

theorem node_context_12_72479_510229 : EJMOriginalGlobalDAGData.nodes 9 ⟨510229, by decide⟩ =
    .split (coordinate 12) (![⟨510075, by decide⟩,⟨510142, by decide⟩,⟨510217, by decide⟩,⟨510228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72479_510229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72479 ⟨510229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72479
    ⟨510229, by decide⟩ (by decide) (![⟨510075, by decide⟩,⟨510142, by decide⟩,⟨510217, by decide⟩,⟨510228, by decide⟩]) unmarked_context_12_72479_510229 node_context_12_72479_510229
  intro a
  fin_cases a
  · exact context_13_289916_510075
  · exact context_13_289917_510142
  · exact context_13_289918_510217
  · exact context_13_289919_510228

theorem unmarked_context_11_18119_510230 : frontier 10 ⟨510230, by decide⟩
    (prefixCache 11 18119) (prefixPartial 11 18119) = false := by
  decide +kernel

theorem node_context_11_18119_510230 : EJMOriginalGlobalDAGData.nodes 10 ⟨510230, by decide⟩ =
    .split (coordinate 11) (![⟨509856, by decide⟩,⟨509938, by decide⟩,⟨510033, by decide⟩,⟨510229, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18119_510230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18119 ⟨510230, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18119
    ⟨510230, by decide⟩ (by decide) (![⟨509856, by decide⟩,⟨509938, by decide⟩,⟨510033, by decide⟩,⟨510229, by decide⟩]) unmarked_context_11_18119_510230 node_context_11_18119_510230
  intro a
  fin_cases a
  · exact context_12_72476_509856
  · exact context_12_72477_509938
  · exact context_12_72478_510033
  · exact context_12_72479_510229

theorem unmarked_context_10_4529_510231 : frontier 11 ⟨510231, by decide⟩
    (prefixCache 10 4529) (prefixPartial 10 4529) = false := by
  decide +kernel

theorem node_context_10_4529_510231 : EJMOriginalGlobalDAGData.nodes 11 ⟨510231, by decide⟩ =
    .split (coordinate 10) (![⟨508769, by decide⟩,⟨509302, by decide⟩,⟨509740, by decide⟩,⟨510230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4529_510231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4529 ⟨510231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4529
    ⟨510231, by decide⟩ (by decide) (![⟨508769, by decide⟩,⟨509302, by decide⟩,⟨509740, by decide⟩,⟨510230, by decide⟩]) unmarked_context_10_4529_510231 node_context_10_4529_510231
  intro a
  fin_cases a
  · exact context_11_18116_508769
  · exact context_11_18117_509302
  · exact context_11_18118_509740
  · exact context_11_18119_510230

theorem selected_cut_19923 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 72480) = some ⟨12, 1, 0, 435790, 72480, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72480_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72480 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 72480 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 72480, 1, 65536⟩
    (by decide) selected_cut_19923

theorem selected_cut_19924 : selected 8 ⟨510255, by decide⟩
    (prefixPartial 13 289924) = some ⟨13, 2, 0, 510255, 289924, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_289924_510255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289924 ⟨510255, by decide⟩ :=
  accepted_of_selected 13 289924 ⟨510255, by decide⟩ ⟨13, 2, 0, 510255, 289924, 1221, 16384⟩
    (by decide) selected_cut_19924

theorem selected_cut_19925 : selected 8 ⟨510283, by decide⟩
    (prefixPartial 13 289925) = some ⟨13, 2, 0, 510283, 289925, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_289925_510283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289925 ⟨510283, by decide⟩ :=
  accepted_of_selected 13 289925 ⟨510283, by decide⟩ ⟨13, 2, 0, 510283, 289925, 2253, 16384⟩
    (by decide) selected_cut_19925

theorem selected_cut_19926 : selected 8 ⟨510307, by decide⟩
    (prefixPartial 13 289926) = some ⟨13, 2, 0, 510307, 289926, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_289926_510307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289926 ⟨510307, by decide⟩ :=
  accepted_of_selected 13 289926 ⟨510307, by decide⟩ ⟨13, 2, 0, 510307, 289926, 1633, 16384⟩
    (by decide) selected_cut_19926

theorem selected_cut_19927 : selected 8 ⟨510316, by decide⟩
    (prefixPartial 13 289927) = some ⟨13, 2, 0, 510316, 289927, 649, 16384⟩ := by
  decide +kernel

theorem context_13_289927_510316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289927 ⟨510316, by decide⟩ :=
  accepted_of_selected 13 289927 ⟨510316, by decide⟩ ⟨13, 2, 0, 510316, 289927, 649, 16384⟩
    (by decide) selected_cut_19927

theorem unmarked_context_12_72481_510317 : frontier 9 ⟨510317, by decide⟩
    (prefixCache 12 72481) (prefixPartial 12 72481) = false := by
  decide +kernel

theorem node_context_12_72481_510317 : EJMOriginalGlobalDAGData.nodes 9 ⟨510317, by decide⟩ =
    .split (coordinate 12) (![⟨510255, by decide⟩,⟨510283, by decide⟩,⟨510307, by decide⟩,⟨510316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72481_510317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72481 ⟨510317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72481
    ⟨510317, by decide⟩ (by decide) (![⟨510255, by decide⟩,⟨510283, by decide⟩,⟨510307, by decide⟩,⟨510316, by decide⟩]) unmarked_context_12_72481_510317 node_context_12_72481_510317
  intro a
  fin_cases a
  · exact context_13_289924_510255
  · exact context_13_289925_510283
  · exact context_13_289926_510307
  · exact context_13_289927_510316

theorem selected_cut_19928 : selected 8 ⟨510338, by decide⟩
    (prefixPartial 13 289928) = some ⟨13, 2, 0, 510338, 289928, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_289928_510338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289928 ⟨510338, by decide⟩ :=
  accepted_of_selected 13 289928 ⟨510338, by decide⟩ ⟨13, 2, 0, 510338, 289928, 1321, 16384⟩
    (by decide) selected_cut_19928

theorem selected_cut_19929 : selected 8 ⟨510377, by decide⟩
    (prefixPartial 13 289929) = some ⟨13, 2, 0, 510377, 289929, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_289929_510377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289929 ⟨510377, by decide⟩ :=
  accepted_of_selected 13 289929 ⟨510377, by decide⟩ ⟨13, 2, 0, 510377, 289929, 2565, 16384⟩
    (by decide) selected_cut_19929

theorem selected_cut_19930 : selected 8 ⟨510400, by decide⟩
    (prefixPartial 13 289930) = some ⟨13, 2, 0, 510400, 289930, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_289930_510400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289930 ⟨510400, by decide⟩ :=
  accepted_of_selected 13 289930 ⟨510400, by decide⟩ ⟨13, 2, 0, 510400, 289930, 1805, 16384⟩
    (by decide) selected_cut_19930

theorem selected_cut_19931 : selected 8 ⟨510406, by decide⟩
    (prefixPartial 13 289931) = some ⟨13, 2, 0, 510406, 289931, 665, 16384⟩ := by
  decide +kernel

theorem context_13_289931_510406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289931 ⟨510406, by decide⟩ :=
  accepted_of_selected 13 289931 ⟨510406, by decide⟩ ⟨13, 2, 0, 510406, 289931, 665, 16384⟩
    (by decide) selected_cut_19931

theorem unmarked_context_12_72482_510407 : frontier 9 ⟨510407, by decide⟩
    (prefixCache 12 72482) (prefixPartial 12 72482) = false := by
  decide +kernel

theorem node_context_12_72482_510407 : EJMOriginalGlobalDAGData.nodes 9 ⟨510407, by decide⟩ =
    .split (coordinate 12) (![⟨510338, by decide⟩,⟨510377, by decide⟩,⟨510400, by decide⟩,⟨510406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72482_510407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72482 ⟨510407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72482
    ⟨510407, by decide⟩ (by decide) (![⟨510338, by decide⟩,⟨510377, by decide⟩,⟨510400, by decide⟩,⟨510406, by decide⟩]) unmarked_context_12_72482_510407 node_context_12_72482_510407
  intro a
  fin_cases a
  · exact context_13_289928_510338
  · exact context_13_289929_510377
  · exact context_13_289930_510400
  · exact context_13_289931_510406

theorem selected_cut_19932 : selected 8 ⟨510428, by decide⟩
    (prefixPartial 13 289932) = some ⟨13, 2, 0, 510428, 289932, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_289932_510428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289932 ⟨510428, by decide⟩ :=
  accepted_of_selected 13 289932 ⟨510428, by decide⟩ ⟨13, 2, 0, 510428, 289932, 1125, 16384⟩
    (by decide) selected_cut_19932

theorem selected_cut_19933 : selected 8 ⟨510458, by decide⟩
    (prefixPartial 13 289933) = some ⟨13, 2, 0, 510458, 289933, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_289933_510458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289933 ⟨510458, by decide⟩ :=
  accepted_of_selected 13 289933 ⟨510458, by decide⟩ ⟨13, 2, 0, 510458, 289933, 2357, 16384⟩
    (by decide) selected_cut_19933

theorem selected_cut_19934 : selected 8 ⟨510479, by decide⟩
    (prefixPartial 13 289934) = some ⟨13, 2, 0, 510479, 289934, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_289934_510479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289934 ⟨510479, by decide⟩ :=
  accepted_of_selected 13 289934 ⟨510479, by decide⟩ ⟨13, 2, 0, 510479, 289934, 1681, 16384⟩
    (by decide) selected_cut_19934

theorem selected_cut_19935 : selected 8 ⟨510486, by decide⟩
    (prefixPartial 13 289935) = some ⟨13, 2, 0, 510486, 289935, 625, 16384⟩ := by
  decide +kernel

theorem context_13_289935_510486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289935 ⟨510486, by decide⟩ :=
  accepted_of_selected 13 289935 ⟨510486, by decide⟩ ⟨13, 2, 0, 510486, 289935, 625, 16384⟩
    (by decide) selected_cut_19935

theorem unmarked_context_12_72483_510487 : frontier 9 ⟨510487, by decide⟩
    (prefixCache 12 72483) (prefixPartial 12 72483) = false := by
  decide +kernel

theorem node_context_12_72483_510487 : EJMOriginalGlobalDAGData.nodes 9 ⟨510487, by decide⟩ =
    .split (coordinate 12) (![⟨510428, by decide⟩,⟨510458, by decide⟩,⟨510479, by decide⟩,⟨510486, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72483_510487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72483 ⟨510487, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72483
    ⟨510487, by decide⟩ (by decide) (![⟨510428, by decide⟩,⟨510458, by decide⟩,⟨510479, by decide⟩,⟨510486, by decide⟩]) unmarked_context_12_72483_510487 node_context_12_72483_510487
  intro a
  fin_cases a
  · exact context_13_289932_510428
  · exact context_13_289933_510458
  · exact context_13_289934_510479
  · exact context_13_289935_510486

theorem unmarked_context_11_18120_510488 : frontier 10 ⟨510488, by decide⟩
    (prefixCache 11 18120) (prefixPartial 11 18120) = false := by
  decide +kernel

theorem node_context_11_18120_510488 : EJMOriginalGlobalDAGData.nodes 10 ⟨510488, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨510317, by decide⟩,⟨510407, by decide⟩,⟨510487, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18120_510488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18120 ⟨510488, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18120
    ⟨510488, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨510317, by decide⟩,⟨510407, by decide⟩,⟨510487, by decide⟩]) unmarked_context_11_18120_510488 node_context_11_18120_510488
  intro a
  fin_cases a
  · exact context_12_72480_435790
  · exact context_12_72481_510317
  · exact context_12_72482_510407
  · exact context_12_72483_510487

theorem selected_cut_19936 : selected 8 ⟨510527, by decide⟩
    (prefixPartial 13 289936) = some ⟨13, 2, 0, 510527, 289936, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_289936_510527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289936 ⟨510527, by decide⟩ :=
  accepted_of_selected 13 289936 ⟨510527, by decide⟩ ⟨13, 2, 0, 510527, 289936, 1841, 16384⟩
    (by decide) selected_cut_19936

theorem selected_cut_19937 : selected 8 ⟨510595, by decide⟩
    (prefixPartial 13 289937) = some ⟨13, 2, 0, 510595, 289937, 3529, 16384⟩ := by
  decide +kernel

theorem context_13_289937_510595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289937 ⟨510595, by decide⟩ :=
  accepted_of_selected 13 289937 ⟨510595, by decide⟩ ⟨13, 2, 0, 510595, 289937, 3529, 16384⟩
    (by decide) selected_cut_19937

theorem selected_cut_19938 : selected 8 ⟨510627, by decide⟩
    (prefixPartial 13 289938) = some ⟨13, 2, 0, 510627, 289938, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_289938_510627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289938 ⟨510627, by decide⟩ :=
  accepted_of_selected 13 289938 ⟨510627, by decide⟩ ⟨13, 2, 0, 510627, 289938, 1973, 16384⟩
    (by decide) selected_cut_19938

theorem selected_cut_19939 : selected 8 ⟨510661, by decide⟩
    (prefixPartial 13 289939) = some ⟨13, 2, 0, 510661, 289939, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_289939_510661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289939 ⟨510661, by decide⟩ :=
  accepted_of_selected 13 289939 ⟨510661, by decide⟩ ⟨13, 2, 0, 510661, 289939, 1145, 16384⟩
    (by decide) selected_cut_19939

theorem unmarked_context_12_72484_510662 : frontier 9 ⟨510662, by decide⟩
    (prefixCache 12 72484) (prefixPartial 12 72484) = false := by
  decide +kernel

theorem node_context_12_72484_510662 : EJMOriginalGlobalDAGData.nodes 9 ⟨510662, by decide⟩ =
    .split (coordinate 12) (![⟨510527, by decide⟩,⟨510595, by decide⟩,⟨510627, by decide⟩,⟨510661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72484_510662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72484 ⟨510662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72484
    ⟨510662, by decide⟩ (by decide) (![⟨510527, by decide⟩,⟨510595, by decide⟩,⟨510627, by decide⟩,⟨510661, by decide⟩]) unmarked_context_12_72484_510662 node_context_12_72484_510662
  intro a
  fin_cases a
  · exact context_13_289936_510527
  · exact context_13_289937_510595
  · exact context_13_289938_510627
  · exact context_13_289939_510661

theorem selected_cut_19940 : selected 8 ⟨510683, by decide⟩
    (prefixPartial 13 289940) = some ⟨13, 2, 0, 510683, 289940, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_289940_510683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289940 ⟨510683, by decide⟩ :=
  accepted_of_selected 13 289940 ⟨510683, by decide⟩ ⟨13, 2, 0, 510683, 289940, 1157, 16384⟩
    (by decide) selected_cut_19940

theorem selected_cut_19941 : selected 8 ⟨510714, by decide⟩
    (prefixPartial 13 289941) = some ⟨13, 2, 0, 510714, 289941, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_289941_510714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289941 ⟨510714, by decide⟩ :=
  accepted_of_selected 13 289941 ⟨510714, by decide⟩ ⟨13, 2, 0, 510714, 289941, 1989, 16384⟩
    (by decide) selected_cut_19941

theorem selected_cut_19942 : selected 8 ⟨510730, by decide⟩
    (prefixPartial 13 289942) = some ⟨13, 2, 0, 510730, 289942, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_289942_510730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289942 ⟨510730, by decide⟩ :=
  accepted_of_selected 13 289942 ⟨510730, by decide⟩ ⟨13, 2, 0, 510730, 289942, 1249, 16384⟩
    (by decide) selected_cut_19942

theorem selected_cut_19943 : selected 8 ⟨510738, by decide⟩
    (prefixPartial 13 289943) = some ⟨13, 2, 0, 510738, 289943, 833, 16384⟩ := by
  decide +kernel

theorem context_13_289943_510738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289943 ⟨510738, by decide⟩ :=
  accepted_of_selected 13 289943 ⟨510738, by decide⟩ ⟨13, 2, 0, 510738, 289943, 833, 16384⟩
    (by decide) selected_cut_19943

theorem unmarked_context_12_72485_510739 : frontier 9 ⟨510739, by decide⟩
    (prefixCache 12 72485) (prefixPartial 12 72485) = false := by
  decide +kernel

theorem node_context_12_72485_510739 : EJMOriginalGlobalDAGData.nodes 9 ⟨510739, by decide⟩ =
    .split (coordinate 12) (![⟨510683, by decide⟩,⟨510714, by decide⟩,⟨510730, by decide⟩,⟨510738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72485_510739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72485 ⟨510739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72485
    ⟨510739, by decide⟩ (by decide) (![⟨510683, by decide⟩,⟨510714, by decide⟩,⟨510730, by decide⟩,⟨510738, by decide⟩]) unmarked_context_12_72485_510739 node_context_12_72485_510739
  intro a
  fin_cases a
  · exact context_13_289940_510683
  · exact context_13_289941_510714
  · exact context_13_289942_510730
  · exact context_13_289943_510738

theorem selected_cut_19944 : selected 8 ⟨510758, by decide⟩
    (prefixPartial 13 289944) = some ⟨13, 2, 0, 510758, 289944, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_289944_510758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289944 ⟨510758, by decide⟩ :=
  accepted_of_selected 13 289944 ⟨510758, by decide⟩ ⟨13, 2, 0, 510758, 289944, 1141, 16384⟩
    (by decide) selected_cut_19944

theorem selected_cut_19945 : selected 8 ⟨510792, by decide⟩
    (prefixPartial 13 289945) = some ⟨13, 2, 0, 510792, 289945, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_289945_510792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289945 ⟨510792, by decide⟩ :=
  accepted_of_selected 13 289945 ⟨510792, by decide⟩ ⟨13, 2, 0, 510792, 289945, 2445, 16384⟩
    (by decide) selected_cut_19945

theorem selected_cut_19946 : selected 8 ⟨510814, by decide⟩
    (prefixPartial 13 289946) = some ⟨13, 2, 0, 510814, 289946, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_289946_510814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289946 ⟨510814, by decide⟩ :=
  accepted_of_selected 13 289946 ⟨510814, by decide⟩ ⟨13, 2, 0, 510814, 289946, 1597, 16384⟩
    (by decide) selected_cut_19946

theorem selected_cut_19947 : selected 8 ⟨510823, by decide⟩
    (prefixPartial 13 289947) = some ⟨13, 2, 0, 510823, 289947, 877, 16384⟩ := by
  decide +kernel

theorem context_13_289947_510823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289947 ⟨510823, by decide⟩ :=
  accepted_of_selected 13 289947 ⟨510823, by decide⟩ ⟨13, 2, 0, 510823, 289947, 877, 16384⟩
    (by decide) selected_cut_19947

theorem unmarked_context_12_72486_510824 : frontier 9 ⟨510824, by decide⟩
    (prefixCache 12 72486) (prefixPartial 12 72486) = false := by
  decide +kernel

theorem node_context_12_72486_510824 : EJMOriginalGlobalDAGData.nodes 9 ⟨510824, by decide⟩ =
    .split (coordinate 12) (![⟨510758, by decide⟩,⟨510792, by decide⟩,⟨510814, by decide⟩,⟨510823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72486_510824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72486 ⟨510824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72486
    ⟨510824, by decide⟩ (by decide) (![⟨510758, by decide⟩,⟨510792, by decide⟩,⟨510814, by decide⟩,⟨510823, by decide⟩]) unmarked_context_12_72486_510824 node_context_12_72486_510824
  intro a
  fin_cases a
  · exact context_13_289944_510758
  · exact context_13_289945_510792
  · exact context_13_289946_510814
  · exact context_13_289947_510823

theorem selected_cut_19948 : selected 8 ⟨510838, by decide⟩
    (prefixPartial 13 289948) = some ⟨13, 2, 0, 510838, 289948, 961, 16384⟩ := by
  decide +kernel

theorem context_13_289948_510838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289948 ⟨510838, by decide⟩ :=
  accepted_of_selected 13 289948 ⟨510838, by decide⟩ ⟨13, 2, 0, 510838, 289948, 961, 16384⟩
    (by decide) selected_cut_19948

theorem selected_cut_19949 : selected 8 ⟨510873, by decide⟩
    (prefixPartial 13 289949) = some ⟨13, 2, 0, 510873, 289949, 2249, 16384⟩ := by
  decide +kernel

theorem context_13_289949_510873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289949 ⟨510873, by decide⟩ :=
  accepted_of_selected 13 289949 ⟨510873, by decide⟩ ⟨13, 2, 0, 510873, 289949, 2249, 16384⟩
    (by decide) selected_cut_19949

theorem selected_cut_19950 : selected 8 ⟨510890, by decide⟩
    (prefixPartial 13 289950) = some ⟨13, 2, 0, 510890, 289950, 1497, 16384⟩ := by
  decide +kernel

theorem context_13_289950_510890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289950 ⟨510890, by decide⟩ :=
  accepted_of_selected 13 289950 ⟨510890, by decide⟩ ⟨13, 2, 0, 510890, 289950, 1497, 16384⟩
    (by decide) selected_cut_19950

theorem selected_cut_19951 : selected 8 ⟨510898, by decide⟩
    (prefixPartial 13 289951) = some ⟨13, 2, 0, 510898, 289951, 793, 16384⟩ := by
  decide +kernel

theorem context_13_289951_510898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289951 ⟨510898, by decide⟩ :=
  accepted_of_selected 13 289951 ⟨510898, by decide⟩ ⟨13, 2, 0, 510898, 289951, 793, 16384⟩
    (by decide) selected_cut_19951

theorem unmarked_context_12_72487_510899 : frontier 9 ⟨510899, by decide⟩
    (prefixCache 12 72487) (prefixPartial 12 72487) = false := by
  decide +kernel

theorem node_context_12_72487_510899 : EJMOriginalGlobalDAGData.nodes 9 ⟨510899, by decide⟩ =
    .split (coordinate 12) (![⟨510838, by decide⟩,⟨510873, by decide⟩,⟨510890, by decide⟩,⟨510898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72487_510899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72487 ⟨510899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72487
    ⟨510899, by decide⟩ (by decide) (![⟨510838, by decide⟩,⟨510873, by decide⟩,⟨510890, by decide⟩,⟨510898, by decide⟩]) unmarked_context_12_72487_510899 node_context_12_72487_510899
  intro a
  fin_cases a
  · exact context_13_289948_510838
  · exact context_13_289949_510873
  · exact context_13_289950_510890
  · exact context_13_289951_510898

theorem unmarked_context_11_18121_510900 : frontier 10 ⟨510900, by decide⟩
    (prefixCache 11 18121) (prefixPartial 11 18121) = false := by
  decide +kernel

theorem node_context_11_18121_510900 : EJMOriginalGlobalDAGData.nodes 10 ⟨510900, by decide⟩ =
    .split (coordinate 11) (![⟨510662, by decide⟩,⟨510739, by decide⟩,⟨510824, by decide⟩,⟨510899, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18121_510900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18121 ⟨510900, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18121
    ⟨510900, by decide⟩ (by decide) (![⟨510662, by decide⟩,⟨510739, by decide⟩,⟨510824, by decide⟩,⟨510899, by decide⟩]) unmarked_context_11_18121_510900 node_context_11_18121_510900
  intro a
  fin_cases a
  · exact context_12_72484_510662
  · exact context_12_72485_510739
  · exact context_12_72486_510824
  · exact context_12_72487_510899

theorem selected_cut_19952 : selected 9 ⟨510901, by decide⟩
    (prefixPartial 12 72488) = some ⟨12, 1, 0, 510901, 72488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72488_510901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72488 ⟨510901, by decide⟩ :=
  accepted_of_selected 12 72488 ⟨510901, by decide⟩ ⟨12, 1, 0, 510901, 72488, 1, 65536⟩
    (by decide) selected_cut_19952

theorem selected_cut_19953 : selected 8 ⟨510922, by decide⟩
    (prefixPartial 13 289956) = some ⟨13, 2, 0, 510922, 289956, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_289956_510922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289956 ⟨510922, by decide⟩ :=
  accepted_of_selected 13 289956 ⟨510922, by decide⟩ ⟨13, 2, 0, 510922, 289956, 1265, 16384⟩
    (by decide) selected_cut_19953

theorem selected_cut_19954 : selected 8 ⟨510961, by decide⟩
    (prefixPartial 13 289957) = some ⟨13, 2, 0, 510961, 289957, 2841, 16384⟩ := by
  decide +kernel

theorem context_13_289957_510961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289957 ⟨510961, by decide⟩ :=
  accepted_of_selected 13 289957 ⟨510961, by decide⟩ ⟨13, 2, 0, 510961, 289957, 2841, 16384⟩
    (by decide) selected_cut_19954

theorem selected_cut_19955 : selected 8 ⟨510991, by decide⟩
    (prefixPartial 13 289958) = some ⟨13, 2, 0, 510991, 289958, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_289958_510991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289958 ⟨510991, by decide⟩ :=
  accepted_of_selected 13 289958 ⟨510991, by decide⟩ ⟨13, 2, 0, 510991, 289958, 2081, 16384⟩
    (by decide) selected_cut_19955

theorem selected_cut_19956 : selected 8 ⟨511005, by decide⟩
    (prefixPartial 13 289959) = some ⟨13, 2, 0, 511005, 289959, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_289959_511005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289959 ⟨511005, by decide⟩ :=
  accepted_of_selected 13 289959 ⟨511005, by decide⟩ ⟨13, 2, 0, 511005, 289959, 1029, 16384⟩
    (by decide) selected_cut_19956

theorem unmarked_context_12_72489_511006 : frontier 9 ⟨511006, by decide⟩
    (prefixCache 12 72489) (prefixPartial 12 72489) = false := by
  decide +kernel

theorem node_context_12_72489_511006 : EJMOriginalGlobalDAGData.nodes 9 ⟨511006, by decide⟩ =
    .split (coordinate 12) (![⟨510922, by decide⟩,⟨510961, by decide⟩,⟨510991, by decide⟩,⟨511005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72489_511006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72489 ⟨511006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72489
    ⟨511006, by decide⟩ (by decide) (![⟨510922, by decide⟩,⟨510961, by decide⟩,⟨510991, by decide⟩,⟨511005, by decide⟩]) unmarked_context_12_72489_511006 node_context_12_72489_511006
  intro a
  fin_cases a
  · exact context_13_289956_510922
  · exact context_13_289957_510961
  · exact context_13_289958_510991
  · exact context_13_289959_511005

theorem selected_cut_19957 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 72490) = some ⟨12, 1, 0, 474208, 72490, 1, 65536⟩ := by
  decide +kernel

theorem context_12_72490_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72490 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 72490 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 72490, 1, 65536⟩
    (by decide) selected_cut_19957

theorem selected_cut_19958 : selected 8 ⟨511025, by decide⟩
    (prefixPartial 13 289964) = some ⟨13, 2, 0, 511025, 289964, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_289964_511025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289964 ⟨511025, by decide⟩ :=
  accepted_of_selected 13 289964 ⟨511025, by decide⟩ ⟨13, 2, 0, 511025, 289964, 1069, 16384⟩
    (by decide) selected_cut_19958

theorem selected_cut_19959 : selected 8 ⟨511064, by decide⟩
    (prefixPartial 13 289965) = some ⟨13, 2, 0, 511064, 289965, 3337, 16384⟩ := by
  decide +kernel

theorem context_13_289965_511064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289965 ⟨511064, by decide⟩ :=
  accepted_of_selected 13 289965 ⟨511064, by decide⟩ ⟨13, 2, 0, 511064, 289965, 3337, 16384⟩
    (by decide) selected_cut_19959

theorem selected_cut_19960 : selected 8 ⟨511093, by decide⟩
    (prefixPartial 13 289966) = some ⟨13, 2, 0, 511093, 289966, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_289966_511093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289966 ⟨511093, by decide⟩ :=
  accepted_of_selected 13 289966 ⟨511093, by decide⟩ ⟨13, 2, 0, 511093, 289966, 2205, 16384⟩
    (by decide) selected_cut_19960

theorem selected_cut_19961 : selected 8 ⟨511101, by decide⟩
    (prefixPartial 13 289967) = some ⟨13, 2, 0, 511101, 289967, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_289967_511101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289967 ⟨511101, by decide⟩ :=
  accepted_of_selected 13 289967 ⟨511101, by decide⟩ ⟨13, 2, 0, 511101, 289967, 1053, 16384⟩
    (by decide) selected_cut_19961

theorem unmarked_context_12_72491_511102 : frontier 9 ⟨511102, by decide⟩
    (prefixCache 12 72491) (prefixPartial 12 72491) = false := by
  decide +kernel

theorem node_context_12_72491_511102 : EJMOriginalGlobalDAGData.nodes 9 ⟨511102, by decide⟩ =
    .split (coordinate 12) (![⟨511025, by decide⟩,⟨511064, by decide⟩,⟨511093, by decide⟩,⟨511101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72491_511102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72491 ⟨511102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72491
    ⟨511102, by decide⟩ (by decide) (![⟨511025, by decide⟩,⟨511064, by decide⟩,⟨511093, by decide⟩,⟨511101, by decide⟩]) unmarked_context_12_72491_511102 node_context_12_72491_511102
  intro a
  fin_cases a
  · exact context_13_289964_511025
  · exact context_13_289965_511064
  · exact context_13_289966_511093
  · exact context_13_289967_511101

theorem unmarked_context_11_18122_511103 : frontier 10 ⟨511103, by decide⟩
    (prefixCache 11 18122) (prefixPartial 11 18122) = false := by
  decide +kernel

theorem node_context_11_18122_511103 : EJMOriginalGlobalDAGData.nodes 10 ⟨511103, by decide⟩ =
    .split (coordinate 11) (![⟨510901, by decide⟩,⟨511006, by decide⟩,⟨474208, by decide⟩,⟨511102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18122_511103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18122 ⟨511103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18122
    ⟨511103, by decide⟩ (by decide) (![⟨510901, by decide⟩,⟨511006, by decide⟩,⟨474208, by decide⟩,⟨511102, by decide⟩]) unmarked_context_11_18122_511103 node_context_11_18122_511103
  intro a
  fin_cases a
  · exact context_12_72488_510901
  · exact context_12_72489_511006
  · exact context_12_72490_474208
  · exact context_12_72491_511102

theorem selected_cut_19962 : selected 8 ⟨511125, by decide⟩
    (prefixPartial 13 289968) = some ⟨13, 2, 0, 511125, 289968, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_289968_511125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289968 ⟨511125, by decide⟩ :=
  accepted_of_selected 13 289968 ⟨511125, by decide⟩ ⟨13, 2, 0, 511125, 289968, 1301, 16384⟩
    (by decide) selected_cut_19962

theorem selected_cut_19963 : selected 8 ⟨511165, by decide⟩
    (prefixPartial 13 289969) = some ⟨13, 2, 0, 511165, 289969, 3261, 16384⟩ := by
  decide +kernel

theorem context_13_289969_511165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289969 ⟨511165, by decide⟩ :=
  accepted_of_selected 13 289969 ⟨511165, by decide⟩ ⟨13, 2, 0, 511165, 289969, 3261, 16384⟩
    (by decide) selected_cut_19963

theorem selected_cut_19964 : selected 8 ⟨511196, by decide⟩
    (prefixPartial 13 289970) = some ⟨13, 2, 0, 511196, 289970, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_289970_511196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289970 ⟨511196, by decide⟩ :=
  accepted_of_selected 13 289970 ⟨511196, by decide⟩ ⟨13, 2, 0, 511196, 289970, 2209, 16384⟩
    (by decide) selected_cut_19964

theorem selected_cut_19965 : selected 8 ⟨511210, by decide⟩
    (prefixPartial 13 289971) = some ⟨13, 2, 0, 511210, 289971, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_289971_511210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289971 ⟨511210, by decide⟩ :=
  accepted_of_selected 13 289971 ⟨511210, by decide⟩ ⟨13, 2, 0, 511210, 289971, 1073, 16384⟩
    (by decide) selected_cut_19965

theorem unmarked_context_12_72492_511211 : frontier 9 ⟨511211, by decide⟩
    (prefixCache 12 72492) (prefixPartial 12 72492) = false := by
  decide +kernel

theorem node_context_12_72492_511211 : EJMOriginalGlobalDAGData.nodes 9 ⟨511211, by decide⟩ =
    .split (coordinate 12) (![⟨511125, by decide⟩,⟨511165, by decide⟩,⟨511196, by decide⟩,⟨511210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72492_511211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72492 ⟨511211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72492
    ⟨511211, by decide⟩ (by decide) (![⟨511125, by decide⟩,⟨511165, by decide⟩,⟨511196, by decide⟩,⟨511210, by decide⟩]) unmarked_context_12_72492_511211 node_context_12_72492_511211
  intro a
  fin_cases a
  · exact context_13_289968_511125
  · exact context_13_289969_511165
  · exact context_13_289970_511196
  · exact context_13_289971_511210

theorem selected_cut_19966 : selected 8 ⟨511224, by decide⟩
    (prefixPartial 13 289972) = some ⟨13, 2, 0, 511224, 289972, 725, 16384⟩ := by
  decide +kernel

theorem context_13_289972_511224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289972 ⟨511224, by decide⟩ :=
  accepted_of_selected 13 289972 ⟨511224, by decide⟩ ⟨13, 2, 0, 511224, 289972, 725, 16384⟩
    (by decide) selected_cut_19966

theorem selected_cut_19967 : selected 8 ⟨511252, by decide⟩
    (prefixPartial 13 289973) = some ⟨13, 2, 0, 511252, 289973, 1965, 16384⟩ := by
  decide +kernel

theorem context_13_289973_511252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289973 ⟨511252, by decide⟩ :=
  accepted_of_selected 13 289973 ⟨511252, by decide⟩ ⟨13, 2, 0, 511252, 289973, 1965, 16384⟩
    (by decide) selected_cut_19967

theorem selected_cut_19968 : selected 8 ⟨511272, by decide⟩
    (prefixPartial 13 289974) = some ⟨13, 2, 0, 511272, 289974, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_289974_511272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289974 ⟨511272, by decide⟩ :=
  accepted_of_selected 13 289974 ⟨511272, by decide⟩ ⟨13, 2, 0, 511272, 289974, 1873, 16384⟩
    (by decide) selected_cut_19968

theorem selected_cut_19969 : selected 8 ⟨511280, by decide⟩
    (prefixPartial 13 289975) = some ⟨13, 2, 0, 511280, 289975, 721, 16384⟩ := by
  decide +kernel

theorem context_13_289975_511280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289975 ⟨511280, by decide⟩ :=
  accepted_of_selected 13 289975 ⟨511280, by decide⟩ ⟨13, 2, 0, 511280, 289975, 721, 16384⟩
    (by decide) selected_cut_19969

theorem unmarked_context_12_72493_511281 : frontier 9 ⟨511281, by decide⟩
    (prefixCache 12 72493) (prefixPartial 12 72493) = false := by
  decide +kernel

theorem node_context_12_72493_511281 : EJMOriginalGlobalDAGData.nodes 9 ⟨511281, by decide⟩ =
    .split (coordinate 12) (![⟨511224, by decide⟩,⟨511252, by decide⟩,⟨511272, by decide⟩,⟨511280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_72493_511281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 72493 ⟨511281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 72493
    ⟨511281, by decide⟩ (by decide) (![⟨511224, by decide⟩,⟨511252, by decide⟩,⟨511272, by decide⟩,⟨511280, by decide⟩]) unmarked_context_12_72493_511281 node_context_12_72493_511281
  intro a
  fin_cases a
  · exact context_13_289972_511224
  · exact context_13_289973_511252
  · exact context_13_289974_511272
  · exact context_13_289975_511280

theorem selected_cut_19970 : selected 8 ⟨511294, by decide⟩
    (prefixPartial 13 289976) = some ⟨13, 2, 0, 511294, 289976, 725, 16384⟩ := by
  decide +kernel

theorem context_13_289976_511294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289976 ⟨511294, by decide⟩ :=
  accepted_of_selected 13 289976 ⟨511294, by decide⟩ ⟨13, 2, 0, 511294, 289976, 725, 16384⟩
    (by decide) selected_cut_19970

theorem selected_cut_19971 : selected 8 ⟨511333, by decide⟩
    (prefixPartial 13 289977) = some ⟨13, 2, 0, 511333, 289977, 2793, 16384⟩ := by
  decide +kernel

theorem context_13_289977_511333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 289977 ⟨511333, by decide⟩ :=
  accepted_of_selected 13 289977 ⟨511333, by decide⟩ ⟨13, 2, 0, 511333, 289977, 2793, 16384⟩
    (by decide) selected_cut_19971

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
