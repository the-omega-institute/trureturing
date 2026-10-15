/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover468
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_22227_1243194 : frontier 11 ⟨1243194, by decide⟩
    (prefixCache 10 22227) (prefixPartial 10 22227) = false := by
  decide +kernel

theorem node_context_10_22227_1243194 : EJMOriginalGlobalDAGData.nodes 11 ⟨1243194, by decide⟩ =
    .split (coordinate 10) (![⟨1242980, by decide⟩,⟨1243045, by decide⟩,⟨1243193, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22227_1243194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22227 ⟨1243194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22227
    ⟨1243194, by decide⟩ (by decide) (![⟨1242980, by decide⟩,⟨1243045, by decide⟩,⟨1243193, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22227_1243194 node_context_10_22227_1243194
  intro a
  fin_cases a
  · exact context_11_88908_1242980
  · exact context_11_88909_1243045
  · exact context_11_88910_1243193
  · exact context_11_88911_977886

theorem unmarked_context_9_5556_1243195 : frontier 12 ⟨1243195, by decide⟩
    (prefixCache 9 5556) (prefixPartial 9 5556) = false := by
  decide +kernel

theorem node_context_9_5556_1243195 : EJMOriginalGlobalDAGData.nodes 12 ⟨1243195, by decide⟩ =
    .split (coordinate 9) (![⟨1241852, by decide⟩,⟨1242298, by decide⟩,⟨1242859, by decide⟩,⟨1243194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5556_1243195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5556 ⟨1243195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5556
    ⟨1243195, by decide⟩ (by decide) (![⟨1241852, by decide⟩,⟨1242298, by decide⟩,⟨1242859, by decide⟩,⟨1243194, by decide⟩]) unmarked_context_9_5556_1243195 node_context_9_5556_1243195
  intro a
  fin_cases a
  · exact context_10_22224_1241852
  · exact context_10_22225_1242298
  · exact context_10_22226_1242859
  · exact context_10_22227_1243194

theorem selected_cut_45028 : selected 10 ⟨1243268, by decide⟩
    (prefixPartial 11 88912) = some ⟨11, 2, 0, 1243268, 88912, 3397, 262144⟩ := by
  decide +kernel

theorem context_11_88912_1243268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88912 ⟨1243268, by decide⟩ :=
  accepted_of_selected 11 88912 ⟨1243268, by decide⟩ ⟨11, 2, 0, 1243268, 88912, 3397, 262144⟩
    (by decide) selected_cut_45028

theorem selected_cut_45029 : selected 10 ⟨1243350, by decide⟩
    (prefixPartial 11 88913) = some ⟨11, 2, 0, 1243350, 88913, 3977, 262144⟩ := by
  decide +kernel

theorem context_11_88913_1243350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88913 ⟨1243350, by decide⟩ :=
  accepted_of_selected 11 88913 ⟨1243350, by decide⟩ ⟨11, 2, 0, 1243350, 88913, 3977, 262144⟩
    (by decide) selected_cut_45029

theorem selected_cut_45030 : selected 10 ⟨1243449, by decide⟩
    (prefixPartial 11 88914) = some ⟨11, 2, 0, 1243449, 88914, 3917, 262144⟩ := by
  decide +kernel

theorem context_11_88914_1243449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88914 ⟨1243449, by decide⟩ :=
  accepted_of_selected 11 88914 ⟨1243449, by decide⟩ ⟨11, 2, 0, 1243449, 88914, 3917, 262144⟩
    (by decide) selected_cut_45030

theorem selected_cut_45031 : selected 10 ⟨1243490, by decide⟩
    (prefixPartial 11 88915) = some ⟨11, 2, 0, 1243490, 88915, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_88915_1243490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88915 ⟨1243490, by decide⟩ :=
  accepted_of_selected 11 88915 ⟨1243490, by decide⟩ ⟨11, 2, 0, 1243490, 88915, 2569, 262144⟩
    (by decide) selected_cut_45031

theorem unmarked_context_10_22228_1243491 : frontier 11 ⟨1243491, by decide⟩
    (prefixCache 10 22228) (prefixPartial 10 22228) = false := by
  decide +kernel

theorem node_context_10_22228_1243491 : EJMOriginalGlobalDAGData.nodes 11 ⟨1243491, by decide⟩ =
    .split (coordinate 10) (![⟨1243268, by decide⟩,⟨1243350, by decide⟩,⟨1243449, by decide⟩,⟨1243490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22228_1243491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22228 ⟨1243491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22228
    ⟨1243491, by decide⟩ (by decide) (![⟨1243268, by decide⟩,⟨1243350, by decide⟩,⟨1243449, by decide⟩,⟨1243490, by decide⟩]) unmarked_context_10_22228_1243491 node_context_10_22228_1243491
  intro a
  fin_cases a
  · exact context_11_88912_1243268
  · exact context_11_88913_1243350
  · exact context_11_88914_1243449
  · exact context_11_88915_1243490

theorem selected_cut_45032 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22229) = some ⟨10, 1, 0, 893098, 22229, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22229_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22229 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22229 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22229, 1, 1048576⟩
    (by decide) selected_cut_45032

theorem selected_cut_45033 : selected 10 ⟨1243571, by decide⟩
    (prefixPartial 11 88920) = some ⟨11, 2, 0, 1243571, 88920, 3461, 262144⟩ := by
  decide +kernel

theorem context_11_88920_1243571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88920 ⟨1243571, by decide⟩ :=
  accepted_of_selected 11 88920 ⟨1243571, by decide⟩ ⟨11, 2, 0, 1243571, 88920, 3461, 262144⟩
    (by decide) selected_cut_45033

theorem selected_cut_45034 : selected 10 ⟨1243626, by decide⟩
    (prefixPartial 11 88921) = some ⟨11, 2, 0, 1243626, 88921, 3293, 262144⟩ := by
  decide +kernel

theorem context_11_88921_1243626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88921 ⟨1243626, by decide⟩ :=
  accepted_of_selected 11 88921 ⟨1243626, by decide⟩ ⟨11, 2, 0, 1243626, 88921, 3293, 262144⟩
    (by decide) selected_cut_45034

theorem selected_cut_45035 : selected 10 ⟨1243669, by decide⟩
    (prefixPartial 11 88922) = some ⟨11, 2, 0, 1243669, 88922, 2437, 262144⟩ := by
  decide +kernel

theorem context_11_88922_1243669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88922 ⟨1243669, by decide⟩ :=
  accepted_of_selected 11 88922 ⟨1243669, by decide⟩ ⟨11, 2, 0, 1243669, 88922, 2437, 262144⟩
    (by decide) selected_cut_45035

theorem selected_cut_45036 : selected 10 ⟨1243704, by decide⟩
    (prefixPartial 11 88923) = some ⟨11, 2, 0, 1243704, 88923, 2209, 262144⟩ := by
  decide +kernel

theorem context_11_88923_1243704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88923 ⟨1243704, by decide⟩ :=
  accepted_of_selected 11 88923 ⟨1243704, by decide⟩ ⟨11, 2, 0, 1243704, 88923, 2209, 262144⟩
    (by decide) selected_cut_45036

theorem unmarked_context_10_22230_1243705 : frontier 11 ⟨1243705, by decide⟩
    (prefixCache 10 22230) (prefixPartial 10 22230) = false := by
  decide +kernel

theorem node_context_10_22230_1243705 : EJMOriginalGlobalDAGData.nodes 11 ⟨1243705, by decide⟩ =
    .split (coordinate 10) (![⟨1243571, by decide⟩,⟨1243626, by decide⟩,⟨1243669, by decide⟩,⟨1243704, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22230_1243705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22230 ⟨1243705, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22230
    ⟨1243705, by decide⟩ (by decide) (![⟨1243571, by decide⟩,⟨1243626, by decide⟩,⟨1243669, by decide⟩,⟨1243704, by decide⟩]) unmarked_context_10_22230_1243705 node_context_10_22230_1243705
  intro a
  fin_cases a
  · exact context_11_88920_1243571
  · exact context_11_88921_1243626
  · exact context_11_88922_1243669
  · exact context_11_88923_1243704

theorem selected_cut_45037 : selected 10 ⟨1243752, by decide⟩
    (prefixPartial 11 88924) = some ⟨11, 2, 0, 1243752, 88924, 2461, 262144⟩ := by
  decide +kernel

theorem context_11_88924_1243752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88924 ⟨1243752, by decide⟩ :=
  accepted_of_selected 11 88924 ⟨1243752, by decide⟩ ⟨11, 2, 0, 1243752, 88924, 2461, 262144⟩
    (by decide) selected_cut_45037

theorem selected_cut_45038 : selected 10 ⟨1243812, by decide⟩
    (prefixPartial 11 88925) = some ⟨11, 2, 0, 1243812, 88925, 2821, 262144⟩ := by
  decide +kernel

theorem context_11_88925_1243812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88925 ⟨1243812, by decide⟩ :=
  accepted_of_selected 11 88925 ⟨1243812, by decide⟩ ⟨11, 2, 0, 1243812, 88925, 2821, 262144⟩
    (by decide) selected_cut_45038

theorem selected_cut_45039 : selected 10 ⟨1243846, by decide⟩
    (prefixPartial 11 88926) = some ⟨11, 2, 0, 1243846, 88926, 2109, 262144⟩ := by
  decide +kernel

theorem context_11_88926_1243846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88926 ⟨1243846, by decide⟩ :=
  accepted_of_selected 11 88926 ⟨1243846, by decide⟩ ⟨11, 2, 0, 1243846, 88926, 2109, 262144⟩
    (by decide) selected_cut_45039

theorem selected_cut_45040 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 88927) = some ⟨11, 1, 0, 977886, 88927, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88927_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88927 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 88927 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 88927, 1, 262144⟩
    (by decide) selected_cut_45040

theorem unmarked_context_10_22231_1243847 : frontier 11 ⟨1243847, by decide⟩
    (prefixCache 10 22231) (prefixPartial 10 22231) = false := by
  decide +kernel

theorem node_context_10_22231_1243847 : EJMOriginalGlobalDAGData.nodes 11 ⟨1243847, by decide⟩ =
    .split (coordinate 10) (![⟨1243752, by decide⟩,⟨1243812, by decide⟩,⟨1243846, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22231_1243847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22231 ⟨1243847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22231
    ⟨1243847, by decide⟩ (by decide) (![⟨1243752, by decide⟩,⟨1243812, by decide⟩,⟨1243846, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22231_1243847 node_context_10_22231_1243847
  intro a
  fin_cases a
  · exact context_11_88924_1243752
  · exact context_11_88925_1243812
  · exact context_11_88926_1243846
  · exact context_11_88927_977886

theorem unmarked_context_9_5557_1243848 : frontier 12 ⟨1243848, by decide⟩
    (prefixCache 9 5557) (prefixPartial 9 5557) = false := by
  decide +kernel

theorem node_context_9_5557_1243848 : EJMOriginalGlobalDAGData.nodes 12 ⟨1243848, by decide⟩ =
    .split (coordinate 9) (![⟨1243491, by decide⟩,⟨893098, by decide⟩,⟨1243705, by decide⟩,⟨1243847, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5557_1243848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5557 ⟨1243848, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5557
    ⟨1243848, by decide⟩ (by decide) (![⟨1243491, by decide⟩,⟨893098, by decide⟩,⟨1243705, by decide⟩,⟨1243847, by decide⟩]) unmarked_context_9_5557_1243848 node_context_9_5557_1243848
  intro a
  fin_cases a
  · exact context_10_22228_1243491
  · exact context_10_22229_893098
  · exact context_10_22230_1243705
  · exact context_10_22231_1243847

theorem selected_cut_45041 : selected 10 ⟨1243913, by decide⟩
    (prefixPartial 11 88928) = some ⟨11, 2, 0, 1243913, 88928, 3653, 262144⟩ := by
  decide +kernel

theorem context_11_88928_1243913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88928 ⟨1243913, by decide⟩ :=
  accepted_of_selected 11 88928 ⟨1243913, by decide⟩ ⟨11, 2, 0, 1243913, 88928, 3653, 262144⟩
    (by decide) selected_cut_45041

theorem selected_cut_45042 : selected 10 ⟨1243957, by decide⟩
    (prefixPartial 11 88929) = some ⟨11, 2, 0, 1243957, 88929, 2449, 262144⟩ := by
  decide +kernel

theorem context_11_88929_1243957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88929 ⟨1243957, by decide⟩ :=
  accepted_of_selected 11 88929 ⟨1243957, by decide⟩ ⟨11, 2, 0, 1243957, 88929, 2449, 262144⟩
    (by decide) selected_cut_45042

theorem selected_cut_45043 : selected 10 ⟨1244041, by decide⟩
    (prefixPartial 11 88930) = some ⟨11, 2, 0, 1244041, 88930, 3905, 262144⟩ := by
  decide +kernel

theorem context_11_88930_1244041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88930 ⟨1244041, by decide⟩ :=
  accepted_of_selected 11 88930 ⟨1244041, by decide⟩ ⟨11, 2, 0, 1244041, 88930, 3905, 262144⟩
    (by decide) selected_cut_45043

theorem selected_cut_45044 : selected 9 ⟨1244058, by decide⟩
    (prefixPartial 12 355724) = some ⟨12, 2, 0, 1244058, 355724, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_355724_1244058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355724 ⟨1244058, by decide⟩ :=
  accepted_of_selected 12 355724 ⟨1244058, by decide⟩ ⟨12, 2, 0, 1244058, 355724, 1009, 65536⟩
    (by decide) selected_cut_45044

theorem selected_cut_45045 : selected 9 ⟨1244075, by decide⟩
    (prefixPartial 12 355725) = some ⟨12, 2, 0, 1244075, 355725, 953, 65536⟩ := by
  decide +kernel

theorem context_12_355725_1244075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355725 ⟨1244075, by decide⟩ :=
  accepted_of_selected 12 355725 ⟨1244075, by decide⟩ ⟨12, 2, 0, 1244075, 355725, 953, 65536⟩
    (by decide) selected_cut_45045

theorem selected_cut_45046 : selected 9 ⟨1244092, by decide⟩
    (prefixPartial 12 355726) = some ⟨12, 2, 0, 1244092, 355726, 1009, 65536⟩ := by
  decide +kernel

theorem context_12_355726_1244092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355726 ⟨1244092, by decide⟩ :=
  accepted_of_selected 12 355726 ⟨1244092, by decide⟩ ⟨12, 2, 0, 1244092, 355726, 1009, 65536⟩
    (by decide) selected_cut_45046

theorem selected_cut_45047 : selected 9 ⟨1244126, by decide⟩
    (prefixPartial 12 355727) = some ⟨12, 2, 0, 1244126, 355727, 1229, 65536⟩ := by
  decide +kernel

theorem context_12_355727_1244126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355727 ⟨1244126, by decide⟩ :=
  accepted_of_selected 12 355727 ⟨1244126, by decide⟩ ⟨12, 2, 0, 1244126, 355727, 1229, 65536⟩
    (by decide) selected_cut_45047

theorem unmarked_context_11_88931_1244127 : frontier 10 ⟨1244127, by decide⟩
    (prefixCache 11 88931) (prefixPartial 11 88931) = false := by
  decide +kernel

theorem node_context_11_88931_1244127 : EJMOriginalGlobalDAGData.nodes 10 ⟨1244127, by decide⟩ =
    .split (coordinate 11) (![⟨1244058, by decide⟩,⟨1244075, by decide⟩,⟨1244092, by decide⟩,⟨1244126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88931_1244127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88931 ⟨1244127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88931
    ⟨1244127, by decide⟩ (by decide) (![⟨1244058, by decide⟩,⟨1244075, by decide⟩,⟨1244092, by decide⟩,⟨1244126, by decide⟩]) unmarked_context_11_88931_1244127 node_context_11_88931_1244127
  intro a
  fin_cases a
  · exact context_12_355724_1244058
  · exact context_12_355725_1244075
  · exact context_12_355726_1244092
  · exact context_12_355727_1244126

theorem unmarked_context_10_22232_1244128 : frontier 11 ⟨1244128, by decide⟩
    (prefixCache 10 22232) (prefixPartial 10 22232) = false := by
  decide +kernel

theorem node_context_10_22232_1244128 : EJMOriginalGlobalDAGData.nodes 11 ⟨1244128, by decide⟩ =
    .split (coordinate 10) (![⟨1243913, by decide⟩,⟨1243957, by decide⟩,⟨1244041, by decide⟩,⟨1244127, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22232_1244128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22232 ⟨1244128, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22232
    ⟨1244128, by decide⟩ (by decide) (![⟨1243913, by decide⟩,⟨1243957, by decide⟩,⟨1244041, by decide⟩,⟨1244127, by decide⟩]) unmarked_context_10_22232_1244128 node_context_10_22232_1244128
  intro a
  fin_cases a
  · exact context_11_88928_1243913
  · exact context_11_88929_1243957
  · exact context_11_88930_1244041
  · exact context_11_88931_1244127

theorem selected_cut_45048 : selected 10 ⟨1244169, by decide⟩
    (prefixPartial 11 88932) = some ⟨11, 2, 0, 1244169, 88932, 2585, 262144⟩ := by
  decide +kernel

theorem context_11_88932_1244169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88932 ⟨1244169, by decide⟩ :=
  accepted_of_selected 11 88932 ⟨1244169, by decide⟩ ⟨11, 2, 0, 1244169, 88932, 2585, 262144⟩
    (by decide) selected_cut_45048

theorem selected_cut_45049 : selected 10 ⟨1244178, by decide⟩
    (prefixPartial 11 88933) = some ⟨11, 2, 0, 1244178, 88933, 741, 262144⟩ := by
  decide +kernel

theorem context_11_88933_1244178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88933 ⟨1244178, by decide⟩ :=
  accepted_of_selected 11 88933 ⟨1244178, by decide⟩ ⟨11, 2, 0, 1244178, 88933, 741, 262144⟩
    (by decide) selected_cut_45049

theorem selected_cut_45050 : selected 10 ⟨1244212, by decide⟩
    (prefixPartial 11 88934) = some ⟨11, 2, 0, 1244212, 88934, 2357, 262144⟩ := by
  decide +kernel

theorem context_11_88934_1244212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88934 ⟨1244212, by decide⟩ :=
  accepted_of_selected 11 88934 ⟨1244212, by decide⟩ ⟨11, 2, 0, 1244212, 88934, 2357, 262144⟩
    (by decide) selected_cut_45050

theorem selected_cut_45051 : selected 10 ⟨1244233, by decide⟩
    (prefixPartial 11 88935) = some ⟨11, 2, 0, 1244233, 88935, 1293, 262144⟩ := by
  decide +kernel

theorem context_11_88935_1244233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88935 ⟨1244233, by decide⟩ :=
  accepted_of_selected 11 88935 ⟨1244233, by decide⟩ ⟨11, 2, 0, 1244233, 88935, 1293, 262144⟩
    (by decide) selected_cut_45051

theorem unmarked_context_10_22233_1244234 : frontier 11 ⟨1244234, by decide⟩
    (prefixCache 10 22233) (prefixPartial 10 22233) = false := by
  decide +kernel

theorem node_context_10_22233_1244234 : EJMOriginalGlobalDAGData.nodes 11 ⟨1244234, by decide⟩ =
    .split (coordinate 10) (![⟨1244169, by decide⟩,⟨1244178, by decide⟩,⟨1244212, by decide⟩,⟨1244233, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22233_1244234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22233 ⟨1244234, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22233
    ⟨1244234, by decide⟩ (by decide) (![⟨1244169, by decide⟩,⟨1244178, by decide⟩,⟨1244212, by decide⟩,⟨1244233, by decide⟩]) unmarked_context_10_22233_1244234 node_context_10_22233_1244234
  intro a
  fin_cases a
  · exact context_11_88932_1244169
  · exact context_11_88933_1244178
  · exact context_11_88934_1244212
  · exact context_11_88935_1244233

theorem selected_cut_45052 : selected 10 ⟨1244276, by decide⟩
    (prefixPartial 11 88936) = some ⟨11, 2, 0, 1244276, 88936, 1825, 262144⟩ := by
  decide +kernel

theorem context_11_88936_1244276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88936 ⟨1244276, by decide⟩ :=
  accepted_of_selected 11 88936 ⟨1244276, by decide⟩ ⟨11, 2, 0, 1244276, 88936, 1825, 262144⟩
    (by decide) selected_cut_45052

theorem selected_cut_45053 : selected 10 ⟨1244305, by decide⟩
    (prefixPartial 11 88937) = some ⟨11, 2, 0, 1244305, 88937, 1409, 262144⟩ := by
  decide +kernel

theorem context_11_88937_1244305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88937 ⟨1244305, by decide⟩ :=
  accepted_of_selected 11 88937 ⟨1244305, by decide⟩ ⟨11, 2, 0, 1244305, 88937, 1409, 262144⟩
    (by decide) selected_cut_45053

theorem selected_cut_45054 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 88938) = some ⟨11, 1, 0, 1109453, 88938, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88938_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88938 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 88938 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 88938, 1, 262144⟩
    (by decide) selected_cut_45054

theorem selected_cut_45055 : selected 10 ⟨1244330, by decide⟩
    (prefixPartial 11 88939) = some ⟨11, 2, 0, 1244330, 88939, 1489, 262144⟩ := by
  decide +kernel

theorem context_11_88939_1244330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88939 ⟨1244330, by decide⟩ :=
  accepted_of_selected 11 88939 ⟨1244330, by decide⟩ ⟨11, 2, 0, 1244330, 88939, 1489, 262144⟩
    (by decide) selected_cut_45055

theorem unmarked_context_10_22234_1244331 : frontier 11 ⟨1244331, by decide⟩
    (prefixCache 10 22234) (prefixPartial 10 22234) = false := by
  decide +kernel

theorem node_context_10_22234_1244331 : EJMOriginalGlobalDAGData.nodes 11 ⟨1244331, by decide⟩ =
    .split (coordinate 10) (![⟨1244276, by decide⟩,⟨1244305, by decide⟩,⟨1109453, by decide⟩,⟨1244330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22234_1244331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22234 ⟨1244331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22234
    ⟨1244331, by decide⟩ (by decide) (![⟨1244276, by decide⟩,⟨1244305, by decide⟩,⟨1109453, by decide⟩,⟨1244330, by decide⟩]) unmarked_context_10_22234_1244331 node_context_10_22234_1244331
  intro a
  fin_cases a
  · exact context_11_88936_1244276
  · exact context_11_88937_1244305
  · exact context_11_88938_1109453
  · exact context_11_88939_1244330

theorem selected_cut_45056 : selected 10 ⟨1244371, by decide⟩
    (prefixPartial 11 88940) = some ⟨11, 2, 0, 1244371, 88940, 2405, 262144⟩ := by
  decide +kernel

theorem context_11_88940_1244371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88940 ⟨1244371, by decide⟩ :=
  accepted_of_selected 11 88940 ⟨1244371, by decide⟩ ⟨11, 2, 0, 1244371, 88940, 2405, 262144⟩
    (by decide) selected_cut_45056

theorem selected_cut_45057 : selected 10 ⟨1244389, by decide⟩
    (prefixPartial 11 88941) = some ⟨11, 2, 0, 1244389, 88941, 1013, 262144⟩ := by
  decide +kernel

theorem context_11_88941_1244389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88941 ⟨1244389, by decide⟩ :=
  accepted_of_selected 11 88941 ⟨1244389, by decide⟩ ⟨11, 2, 0, 1244389, 88941, 1013, 262144⟩
    (by decide) selected_cut_45057

theorem selected_cut_45058 : selected 10 ⟨1244413, by decide⟩
    (prefixPartial 11 88942) = some ⟨11, 2, 0, 1244413, 88942, 1473, 262144⟩ := by
  decide +kernel

theorem context_11_88942_1244413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88942 ⟨1244413, by decide⟩ :=
  accepted_of_selected 11 88942 ⟨1244413, by decide⟩ ⟨11, 2, 0, 1244413, 88942, 1473, 262144⟩
    (by decide) selected_cut_45058

theorem selected_cut_45059 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 88943) = some ⟨11, 1, 0, 977886, 88943, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88943_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88943 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 88943 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 88943, 1, 262144⟩
    (by decide) selected_cut_45059

theorem unmarked_context_10_22235_1244414 : frontier 11 ⟨1244414, by decide⟩
    (prefixCache 10 22235) (prefixPartial 10 22235) = false := by
  decide +kernel

theorem node_context_10_22235_1244414 : EJMOriginalGlobalDAGData.nodes 11 ⟨1244414, by decide⟩ =
    .split (coordinate 10) (![⟨1244371, by decide⟩,⟨1244389, by decide⟩,⟨1244413, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22235_1244414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22235 ⟨1244414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22235
    ⟨1244414, by decide⟩ (by decide) (![⟨1244371, by decide⟩,⟨1244389, by decide⟩,⟨1244413, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22235_1244414 node_context_10_22235_1244414
  intro a
  fin_cases a
  · exact context_11_88940_1244371
  · exact context_11_88941_1244389
  · exact context_11_88942_1244413
  · exact context_11_88943_977886

theorem unmarked_context_9_5558_1244415 : frontier 12 ⟨1244415, by decide⟩
    (prefixCache 9 5558) (prefixPartial 9 5558) = false := by
  decide +kernel

theorem node_context_9_5558_1244415 : EJMOriginalGlobalDAGData.nodes 12 ⟨1244415, by decide⟩ =
    .split (coordinate 9) (![⟨1244128, by decide⟩,⟨1244234, by decide⟩,⟨1244331, by decide⟩,⟨1244414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5558_1244415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5558 ⟨1244415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5558
    ⟨1244415, by decide⟩ (by decide) (![⟨1244128, by decide⟩,⟨1244234, by decide⟩,⟨1244331, by decide⟩,⟨1244414, by decide⟩]) unmarked_context_9_5558_1244415 node_context_9_5558_1244415
  intro a
  fin_cases a
  · exact context_10_22232_1244128
  · exact context_10_22233_1244234
  · exact context_10_22234_1244331
  · exact context_10_22235_1244414

theorem selected_cut_45060 : selected 10 ⟨1244443, by decide⟩
    (prefixPartial 11 88944) = some ⟨11, 2, 0, 1244443, 88944, 1457, 262144⟩ := by
  decide +kernel

theorem context_11_88944_1244443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88944 ⟨1244443, by decide⟩ :=
  accepted_of_selected 11 88944 ⟨1244443, by decide⟩ ⟨11, 2, 0, 1244443, 88944, 1457, 262144⟩
    (by decide) selected_cut_45060

theorem selected_cut_45061 : selected 10 ⟨1244459, by decide⟩
    (prefixPartial 11 88945) = some ⟨11, 2, 0, 1244459, 88945, 817, 262144⟩ := by
  decide +kernel

theorem context_11_88945_1244459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88945 ⟨1244459, by decide⟩ :=
  accepted_of_selected 11 88945 ⟨1244459, by decide⟩ ⟨11, 2, 0, 1244459, 88945, 817, 262144⟩
    (by decide) selected_cut_45061

theorem selected_cut_45062 : selected 10 ⟨1244488, by decide⟩
    (prefixPartial 11 88946) = some ⟨11, 2, 0, 1244488, 88946, 1765, 262144⟩ := by
  decide +kernel

theorem context_11_88946_1244488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88946 ⟨1244488, by decide⟩ :=
  accepted_of_selected 11 88946 ⟨1244488, by decide⟩ ⟨11, 2, 0, 1244488, 88946, 1765, 262144⟩
    (by decide) selected_cut_45062

theorem selected_cut_45063 : selected 10 ⟨1244506, by decide⟩
    (prefixPartial 11 88947) = some ⟨11, 2, 0, 1244506, 88947, 957, 262144⟩ := by
  decide +kernel

theorem context_11_88947_1244506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88947 ⟨1244506, by decide⟩ :=
  accepted_of_selected 11 88947 ⟨1244506, by decide⟩ ⟨11, 2, 0, 1244506, 88947, 957, 262144⟩
    (by decide) selected_cut_45063

theorem unmarked_context_10_22236_1244507 : frontier 11 ⟨1244507, by decide⟩
    (prefixCache 10 22236) (prefixPartial 10 22236) = false := by
  decide +kernel

theorem node_context_10_22236_1244507 : EJMOriginalGlobalDAGData.nodes 11 ⟨1244507, by decide⟩ =
    .split (coordinate 10) (![⟨1244443, by decide⟩,⟨1244459, by decide⟩,⟨1244488, by decide⟩,⟨1244506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22236_1244507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22236 ⟨1244507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22236
    ⟨1244507, by decide⟩ (by decide) (![⟨1244443, by decide⟩,⟨1244459, by decide⟩,⟨1244488, by decide⟩,⟨1244506, by decide⟩]) unmarked_context_10_22236_1244507 node_context_10_22236_1244507
  intro a
  fin_cases a
  · exact context_11_88944_1244443
  · exact context_11_88945_1244459
  · exact context_11_88946_1244488
  · exact context_11_88947_1244506

theorem selected_cut_45064 : selected 11 ⟨1244550, by decide⟩
    (prefixPartial 10 22237) = some ⟨10, 2, 0, 1244550, 22237, 2213, 1048576⟩ := by
  decide +kernel

theorem context_10_22237_1244550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22237 ⟨1244550, by decide⟩ :=
  accepted_of_selected 10 22237 ⟨1244550, by decide⟩ ⟨10, 2, 0, 1244550, 22237, 2213, 1048576⟩
    (by decide) selected_cut_45064

theorem selected_cut_45065 : selected 11 ⟨1244594, by decide⟩
    (prefixPartial 10 22238) = some ⟨10, 2, 0, 1244594, 22238, 1685, 1048576⟩ := by
  decide +kernel

theorem context_10_22238_1244594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22238 ⟨1244594, by decide⟩ :=
  accepted_of_selected 10 22238 ⟨1244594, by decide⟩ ⟨10, 2, 0, 1244594, 22238, 1685, 1048576⟩
    (by decide) selected_cut_45065

theorem selected_cut_45066 : selected 11 ⟨1244602, by decide⟩
    (prefixPartial 10 22239) = some ⟨10, 2, 0, 1244602, 22239, 185, 1048576⟩ := by
  decide +kernel

theorem context_10_22239_1244602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22239 ⟨1244602, by decide⟩ :=
  accepted_of_selected 10 22239 ⟨1244602, by decide⟩ ⟨10, 2, 0, 1244602, 22239, 185, 1048576⟩
    (by decide) selected_cut_45066

theorem unmarked_context_9_5559_1244603 : frontier 12 ⟨1244603, by decide⟩
    (prefixCache 9 5559) (prefixPartial 9 5559) = false := by
  decide +kernel

theorem node_context_9_5559_1244603 : EJMOriginalGlobalDAGData.nodes 12 ⟨1244603, by decide⟩ =
    .split (coordinate 9) (![⟨1244507, by decide⟩,⟨1244550, by decide⟩,⟨1244594, by decide⟩,⟨1244602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5559_1244603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5559 ⟨1244603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5559
    ⟨1244603, by decide⟩ (by decide) (![⟨1244507, by decide⟩,⟨1244550, by decide⟩,⟨1244594, by decide⟩,⟨1244602, by decide⟩]) unmarked_context_9_5559_1244603 node_context_9_5559_1244603
  intro a
  fin_cases a
  · exact context_10_22236_1244507
  · exact context_10_22237_1244550
  · exact context_10_22238_1244594
  · exact context_10_22239_1244602

theorem unmarked_context_8_1389_1244604 : frontier 13 ⟨1244604, by decide⟩
    (prefixCache 8 1389) (prefixPartial 8 1389) = false := by
  decide +kernel

theorem node_context_8_1389_1244604 : EJMOriginalGlobalDAGData.nodes 13 ⟨1244604, by decide⟩ =
    .split (coordinate 8) (![⟨1243195, by decide⟩,⟨1243848, by decide⟩,⟨1244415, by decide⟩,⟨1244603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1389_1244604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1389 ⟨1244604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1389
    ⟨1244604, by decide⟩ (by decide) (![⟨1243195, by decide⟩,⟨1243848, by decide⟩,⟨1244415, by decide⟩,⟨1244603, by decide⟩]) unmarked_context_8_1389_1244604 node_context_8_1389_1244604
  intro a
  fin_cases a
  · exact context_9_5556_1243195
  · exact context_9_5557_1243848
  · exact context_9_5558_1244415
  · exact context_9_5559_1244603

theorem selected_cut_45067 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 88960) = some ⟨11, 1, 0, 434745, 88960, 1, 262144⟩ := by
  decide +kernel

theorem context_11_88960_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88960 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 88960 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 88960, 1, 262144⟩
    (by decide) selected_cut_45067

theorem selected_cut_45068 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355844) = some ⟨12, 1, 0, 448748, 355844, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355844_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355844 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355844 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355844, 1, 65536⟩
    (by decide) selected_cut_45068

theorem selected_cut_45069 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 355845) = some ⟨12, 1, 0, 34034, 355845, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355845_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355845 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 355845 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 355845, 1, 65536⟩
    (by decide) selected_cut_45069

theorem selected_cut_45070 : selected 9 ⟨1244675, by decide⟩
    (prefixPartial 12 355846) = some ⟨12, 2, 0, 1244675, 355846, 3065, 65536⟩ := by
  decide +kernel

theorem context_12_355846_1244675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355846 ⟨1244675, by decide⟩ :=
  accepted_of_selected 12 355846 ⟨1244675, by decide⟩ ⟨12, 2, 0, 1244675, 355846, 3065, 65536⟩
    (by decide) selected_cut_45070

theorem selected_cut_45071 : selected 9 ⟨1244753, by decide⟩
    (prefixPartial 12 355847) = some ⟨12, 2, 0, 1244753, 355847, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_355847_1244753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355847 ⟨1244753, by decide⟩ :=
  accepted_of_selected 12 355847 ⟨1244753, by decide⟩ ⟨12, 2, 0, 1244753, 355847, 3565, 65536⟩
    (by decide) selected_cut_45071

theorem unmarked_context_11_88961_1244754 : frontier 10 ⟨1244754, by decide⟩
    (prefixCache 11 88961) (prefixPartial 11 88961) = false := by
  decide +kernel

theorem node_context_11_88961_1244754 : EJMOriginalGlobalDAGData.nodes 10 ⟨1244754, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1244675, by decide⟩,⟨1244753, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88961_1244754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88961 ⟨1244754, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88961
    ⟨1244754, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1244675, by decide⟩,⟨1244753, by decide⟩]) unmarked_context_11_88961_1244754 node_context_11_88961_1244754
  intro a
  fin_cases a
  · exact context_12_355844_448748
  · exact context_12_355845_34034
  · exact context_12_355846_1244675
  · exact context_12_355847_1244753

theorem selected_cut_45072 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355848) = some ⟨12, 1, 0, 448748, 355848, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355848_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355848 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355848 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355848, 1, 65536⟩
    (by decide) selected_cut_45072

theorem selected_cut_45073 : selected 9 ⟨1244824, by decide⟩
    (prefixPartial 12 355849) = some ⟨12, 2, 0, 1244824, 355849, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_355849_1244824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355849 ⟨1244824, by decide⟩ :=
  accepted_of_selected 12 355849 ⟨1244824, by decide⟩ ⟨12, 2, 0, 1244824, 355849, 3149, 65536⟩
    (by decide) selected_cut_45073

theorem selected_cut_45074 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 355850) = some ⟨12, 1, 0, 893903, 355850, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355850_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355850 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 355850 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 355850, 1, 65536⟩
    (by decide) selected_cut_45074

theorem selected_cut_45075 : selected 9 ⟨1244914, by decide⟩
    (prefixPartial 12 355851) = some ⟨12, 2, 0, 1244914, 355851, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_355851_1244914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355851 ⟨1244914, by decide⟩ :=
  accepted_of_selected 12 355851 ⟨1244914, by decide⟩ ⟨12, 2, 0, 1244914, 355851, 3701, 65536⟩
    (by decide) selected_cut_45075

theorem unmarked_context_11_88962_1244915 : frontier 10 ⟨1244915, by decide⟩
    (prefixCache 11 88962) (prefixPartial 11 88962) = false := by
  decide +kernel

theorem node_context_11_88962_1244915 : EJMOriginalGlobalDAGData.nodes 10 ⟨1244915, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1244824, by decide⟩,⟨893903, by decide⟩,⟨1244914, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88962_1244915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88962 ⟨1244915, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88962
    ⟨1244915, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1244824, by decide⟩,⟨893903, by decide⟩,⟨1244914, by decide⟩]) unmarked_context_11_88962_1244915 node_context_11_88962_1244915
  intro a
  fin_cases a
  · exact context_12_355848_448748
  · exact context_12_355849_1244824
  · exact context_12_355850_893903
  · exact context_12_355851_1244914

theorem selected_cut_45076 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 355852) = some ⟨12, 1, 0, 448748, 355852, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355852_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355852 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 355852 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 355852, 1, 65536⟩
    (by decide) selected_cut_45076

theorem selected_cut_45077 : selected 9 ⟨390434, by decide⟩
    (prefixPartial 12 355853) = some ⟨12, 1, 0, 390434, 355853, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355853_390434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355853 ⟨390434, by decide⟩ :=
  accepted_of_selected 12 355853 ⟨390434, by decide⟩ ⟨12, 1, 0, 390434, 355853, 1, 65536⟩
    (by decide) selected_cut_45077

theorem selected_cut_45078 : selected 9 ⟨1244974, by decide⟩
    (prefixPartial 12 355854) = some ⟨12, 2, 0, 1244974, 355854, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_355854_1244974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355854 ⟨1244974, by decide⟩ :=
  accepted_of_selected 12 355854 ⟨1244974, by decide⟩ ⟨12, 2, 0, 1244974, 355854, 3033, 65536⟩
    (by decide) selected_cut_45078

theorem selected_cut_45079 : selected 9 ⟨1245030, by decide⟩
    (prefixPartial 12 355855) = some ⟨12, 2, 0, 1245030, 355855, 3201, 65536⟩ := by
  decide +kernel

theorem context_12_355855_1245030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355855 ⟨1245030, by decide⟩ :=
  accepted_of_selected 12 355855 ⟨1245030, by decide⟩ ⟨12, 2, 0, 1245030, 355855, 3201, 65536⟩
    (by decide) selected_cut_45079

theorem unmarked_context_11_88963_1245031 : frontier 10 ⟨1245031, by decide⟩
    (prefixCache 11 88963) (prefixPartial 11 88963) = false := by
  decide +kernel

theorem node_context_11_88963_1245031 : EJMOriginalGlobalDAGData.nodes 10 ⟨1245031, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨1244974, by decide⟩,⟨1245030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88963_1245031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88963 ⟨1245031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88963
    ⟨1245031, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨390434, by decide⟩,⟨1244974, by decide⟩,⟨1245030, by decide⟩]) unmarked_context_11_88963_1245031 node_context_11_88963_1245031
  intro a
  fin_cases a
  · exact context_12_355852_448748
  · exact context_12_355853_390434
  · exact context_12_355854_1244974
  · exact context_12_355855_1245030

theorem unmarked_context_10_22240_1245032 : frontier 11 ⟨1245032, by decide⟩
    (prefixCache 10 22240) (prefixPartial 10 22240) = false := by
  decide +kernel

theorem node_context_10_22240_1245032 : EJMOriginalGlobalDAGData.nodes 11 ⟨1245032, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1244754, by decide⟩,⟨1244915, by decide⟩,⟨1245031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22240_1245032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22240 ⟨1245032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22240
    ⟨1245032, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1244754, by decide⟩,⟨1244915, by decide⟩,⟨1245031, by decide⟩]) unmarked_context_10_22240_1245032 node_context_10_22240_1245032
  intro a
  fin_cases a
  · exact context_11_88960_434745
  · exact context_11_88961_1244754
  · exact context_11_88962_1244915
  · exact context_11_88963_1245031

theorem selected_cut_45080 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 355856) = some ⟨12, 1, 0, 435160, 355856, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355856_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355856 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 355856 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 355856, 1, 65536⟩
    (by decide) selected_cut_45080

theorem selected_cut_45081 : selected 9 ⟨1245088, by decide⟩
    (prefixPartial 12 355857) = some ⟨12, 2, 0, 1245088, 355857, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_355857_1245088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355857 ⟨1245088, by decide⟩ :=
  accepted_of_selected 12 355857 ⟨1245088, by decide⟩ ⟨12, 2, 0, 1245088, 355857, 3005, 65536⟩
    (by decide) selected_cut_45081

theorem selected_cut_45082 : selected 9 ⟨1245156, by decide⟩
    (prefixPartial 12 355858) = some ⟨12, 2, 0, 1245156, 355858, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_355858_1245156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355858 ⟨1245156, by decide⟩ :=
  accepted_of_selected 12 355858 ⟨1245156, by decide⟩ ⟨12, 2, 0, 1245156, 355858, 3409, 65536⟩
    (by decide) selected_cut_45082

theorem selected_cut_45083 : selected 9 ⟨1245228, by decide⟩
    (prefixPartial 12 355859) = some ⟨12, 2, 0, 1245228, 355859, 3613, 65536⟩ := by
  decide +kernel

theorem context_12_355859_1245228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355859 ⟨1245228, by decide⟩ :=
  accepted_of_selected 12 355859 ⟨1245228, by decide⟩ ⟨12, 2, 0, 1245228, 355859, 3613, 65536⟩
    (by decide) selected_cut_45083

theorem unmarked_context_11_88964_1245229 : frontier 10 ⟨1245229, by decide⟩
    (prefixCache 11 88964) (prefixPartial 11 88964) = false := by
  decide +kernel

theorem node_context_11_88964_1245229 : EJMOriginalGlobalDAGData.nodes 10 ⟨1245229, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1245088, by decide⟩,⟨1245156, by decide⟩,⟨1245228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88964_1245229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88964 ⟨1245229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88964
    ⟨1245229, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1245088, by decide⟩,⟨1245156, by decide⟩,⟨1245228, by decide⟩]) unmarked_context_11_88964_1245229 node_context_11_88964_1245229
  intro a
  fin_cases a
  · exact context_12_355856_435160
  · exact context_12_355857_1245088
  · exact context_12_355858_1245156
  · exact context_12_355859_1245228

theorem selected_cut_45084 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 355860) = some ⟨12, 1, 0, 435160, 355860, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355860_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355860 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 355860 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 355860, 1, 65536⟩
    (by decide) selected_cut_45084

theorem selected_cut_45085 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 355861) = some ⟨12, 1, 0, 1172003, 355861, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355861_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355861 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 355861 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 355861, 1, 65536⟩
    (by decide) selected_cut_45085

theorem selected_cut_45086 : selected 9 ⟨1245293, by decide⟩
    (prefixPartial 12 355862) = some ⟨12, 2, 0, 1245293, 355862, 3189, 65536⟩ := by
  decide +kernel

theorem context_12_355862_1245293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355862 ⟨1245293, by decide⟩ :=
  accepted_of_selected 12 355862 ⟨1245293, by decide⟩ ⟨12, 2, 0, 1245293, 355862, 3189, 65536⟩
    (by decide) selected_cut_45086

theorem selected_cut_45087 : selected 9 ⟨1245355, by decide⟩
    (prefixPartial 12 355863) = some ⟨12, 2, 0, 1245355, 355863, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_355863_1245355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355863 ⟨1245355, by decide⟩ :=
  accepted_of_selected 12 355863 ⟨1245355, by decide⟩ ⟨12, 2, 0, 1245355, 355863, 3549, 65536⟩
    (by decide) selected_cut_45087

theorem unmarked_context_11_88965_1245356 : frontier 10 ⟨1245356, by decide⟩
    (prefixCache 11 88965) (prefixPartial 11 88965) = false := by
  decide +kernel

theorem node_context_11_88965_1245356 : EJMOriginalGlobalDAGData.nodes 10 ⟨1245356, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1172003, by decide⟩,⟨1245293, by decide⟩,⟨1245355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88965_1245356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88965 ⟨1245356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88965
    ⟨1245356, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1172003, by decide⟩,⟨1245293, by decide⟩,⟨1245355, by decide⟩]) unmarked_context_11_88965_1245356 node_context_11_88965_1245356
  intro a
  fin_cases a
  · exact context_12_355860_435160
  · exact context_12_355861_1172003
  · exact context_12_355862_1245293
  · exact context_12_355863_1245355

theorem selected_cut_45088 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 355864) = some ⟨12, 1, 0, 449505, 355864, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355864_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355864 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 355864 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 355864, 1, 65536⟩
    (by decide) selected_cut_45088

theorem selected_cut_45089 : selected 9 ⟨1245400, by decide⟩
    (prefixPartial 12 355865) = some ⟨12, 2, 0, 1245400, 355865, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_355865_1245400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355865 ⟨1245400, by decide⟩ :=
  accepted_of_selected 12 355865 ⟨1245400, by decide⟩ ⟨12, 2, 0, 1245400, 355865, 2937, 65536⟩
    (by decide) selected_cut_45089

theorem selected_cut_45090 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 355866) = some ⟨12, 1, 0, 893903, 355866, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355866_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355866 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 355866 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 355866, 1, 65536⟩
    (by decide) selected_cut_45090

theorem selected_cut_45091 : selected 9 ⟨1245465, by decide⟩
    (prefixPartial 12 355867) = some ⟨12, 2, 0, 1245465, 355867, 3509, 65536⟩ := by
  decide +kernel

theorem context_12_355867_1245465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355867 ⟨1245465, by decide⟩ :=
  accepted_of_selected 12 355867 ⟨1245465, by decide⟩ ⟨12, 2, 0, 1245465, 355867, 3509, 65536⟩
    (by decide) selected_cut_45091

theorem unmarked_context_11_88966_1245466 : frontier 10 ⟨1245466, by decide⟩
    (prefixCache 11 88966) (prefixPartial 11 88966) = false := by
  decide +kernel

theorem node_context_11_88966_1245466 : EJMOriginalGlobalDAGData.nodes 10 ⟨1245466, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨1245400, by decide⟩,⟨893903, by decide⟩,⟨1245465, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88966_1245466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88966 ⟨1245466, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88966
    ⟨1245466, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨1245400, by decide⟩,⟨893903, by decide⟩,⟨1245465, by decide⟩]) unmarked_context_11_88966_1245466 node_context_11_88966_1245466
  intro a
  fin_cases a
  · exact context_12_355864_449505
  · exact context_12_355865_1245400
  · exact context_12_355866_893903
  · exact context_12_355867_1245465

theorem selected_cut_45092 : selected 9 ⟨1245512, by decide⟩
    (prefixPartial 12 355868) = some ⟨12, 2, 0, 1245512, 355868, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_355868_1245512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355868 ⟨1245512, by decide⟩ :=
  accepted_of_selected 12 355868 ⟨1245512, by decide⟩ ⟨12, 2, 0, 1245512, 355868, 1501, 65536⟩
    (by decide) selected_cut_45092

theorem selected_cut_45093 : selected 9 ⟨1245554, by decide⟩
    (prefixPartial 12 355869) = some ⟨12, 2, 0, 1245554, 355869, 2701, 65536⟩ := by
  decide +kernel

theorem context_12_355869_1245554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355869 ⟨1245554, by decide⟩ :=
  accepted_of_selected 12 355869 ⟨1245554, by decide⟩ ⟨12, 2, 0, 1245554, 355869, 2701, 65536⟩
    (by decide) selected_cut_45093

theorem selected_cut_45094 : selected 9 ⟨1245608, by decide⟩
    (prefixPartial 12 355870) = some ⟨12, 2, 0, 1245608, 355870, 3021, 65536⟩ := by
  decide +kernel

theorem context_12_355870_1245608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355870 ⟨1245608, by decide⟩ :=
  accepted_of_selected 12 355870 ⟨1245608, by decide⟩ ⟨12, 2, 0, 1245608, 355870, 3021, 65536⟩
    (by decide) selected_cut_45094

theorem selected_cut_45095 : selected 9 ⟨1245655, by decide⟩
    (prefixPartial 12 355871) = some ⟨12, 2, 0, 1245655, 355871, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_355871_1245655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355871 ⟨1245655, by decide⟩ :=
  accepted_of_selected 12 355871 ⟨1245655, by decide⟩ ⟨12, 2, 0, 1245655, 355871, 3045, 65536⟩
    (by decide) selected_cut_45095

theorem unmarked_context_11_88967_1245656 : frontier 10 ⟨1245656, by decide⟩
    (prefixCache 11 88967) (prefixPartial 11 88967) = false := by
  decide +kernel

theorem node_context_11_88967_1245656 : EJMOriginalGlobalDAGData.nodes 10 ⟨1245656, by decide⟩ =
    .split (coordinate 11) (![⟨1245512, by decide⟩,⟨1245554, by decide⟩,⟨1245608, by decide⟩,⟨1245655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88967_1245656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88967 ⟨1245656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88967
    ⟨1245656, by decide⟩ (by decide) (![⟨1245512, by decide⟩,⟨1245554, by decide⟩,⟨1245608, by decide⟩,⟨1245655, by decide⟩]) unmarked_context_11_88967_1245656 node_context_11_88967_1245656
  intro a
  fin_cases a
  · exact context_12_355868_1245512
  · exact context_12_355869_1245554
  · exact context_12_355870_1245608
  · exact context_12_355871_1245655

theorem unmarked_context_10_22241_1245657 : frontier 11 ⟨1245657, by decide⟩
    (prefixCache 10 22241) (prefixPartial 10 22241) = false := by
  decide +kernel

theorem node_context_10_22241_1245657 : EJMOriginalGlobalDAGData.nodes 11 ⟨1245657, by decide⟩ =
    .split (coordinate 10) (![⟨1245229, by decide⟩,⟨1245356, by decide⟩,⟨1245466, by decide⟩,⟨1245656, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22241_1245657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22241 ⟨1245657, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22241
    ⟨1245657, by decide⟩ (by decide) (![⟨1245229, by decide⟩,⟨1245356, by decide⟩,⟨1245466, by decide⟩,⟨1245656, by decide⟩]) unmarked_context_10_22241_1245657 node_context_10_22241_1245657
  intro a
  fin_cases a
  · exact context_11_88964_1245229
  · exact context_11_88965_1245356
  · exact context_11_88966_1245466
  · exact context_11_88967_1245656

theorem selected_cut_45096 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 355872) = some ⟨12, 1, 0, 1187656, 355872, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355872_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355872 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 355872 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 355872, 1, 65536⟩
    (by decide) selected_cut_45096

theorem selected_cut_45097 : selected 9 ⟨1245707, by decide⟩
    (prefixPartial 12 355873) = some ⟨12, 2, 0, 1245707, 355873, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_355873_1245707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355873 ⟨1245707, by decide⟩ :=
  accepted_of_selected 12 355873 ⟨1245707, by decide⟩ ⟨12, 2, 0, 1245707, 355873, 2757, 65536⟩
    (by decide) selected_cut_45097

theorem selected_cut_45098 : selected 9 ⟨1245759, by decide⟩
    (prefixPartial 12 355874) = some ⟨12, 2, 0, 1245759, 355874, 2761, 65536⟩ := by
  decide +kernel

theorem context_12_355874_1245759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355874 ⟨1245759, by decide⟩ :=
  accepted_of_selected 12 355874 ⟨1245759, by decide⟩ ⟨12, 2, 0, 1245759, 355874, 2761, 65536⟩
    (by decide) selected_cut_45098

theorem selected_cut_45099 : selected 9 ⟨1245833, by decide⟩
    (prefixPartial 12 355875) = some ⟨12, 2, 0, 1245833, 355875, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_355875_1245833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355875 ⟨1245833, by decide⟩ :=
  accepted_of_selected 12 355875 ⟨1245833, by decide⟩ ⟨12, 2, 0, 1245833, 355875, 3229, 65536⟩
    (by decide) selected_cut_45099

theorem unmarked_context_11_88968_1245834 : frontier 10 ⟨1245834, by decide⟩
    (prefixCache 11 88968) (prefixPartial 11 88968) = false := by
  decide +kernel

theorem node_context_11_88968_1245834 : EJMOriginalGlobalDAGData.nodes 10 ⟨1245834, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1245707, by decide⟩,⟨1245759, by decide⟩,⟨1245833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88968_1245834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88968 ⟨1245834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88968
    ⟨1245834, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1245707, by decide⟩,⟨1245759, by decide⟩,⟨1245833, by decide⟩]) unmarked_context_11_88968_1245834 node_context_11_88968_1245834
  intro a
  fin_cases a
  · exact context_12_355872_1187656
  · exact context_12_355873_1245707
  · exact context_12_355874_1245759
  · exact context_12_355875_1245833

theorem selected_cut_45100 : selected 9 ⟨1245888, by decide⟩
    (prefixPartial 12 355876) = some ⟨12, 2, 0, 1245888, 355876, 2841, 65536⟩ := by
  decide +kernel

theorem context_12_355876_1245888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355876 ⟨1245888, by decide⟩ :=
  accepted_of_selected 12 355876 ⟨1245888, by decide⟩ ⟨12, 2, 0, 1245888, 355876, 2841, 65536⟩
    (by decide) selected_cut_45100

theorem selected_cut_45101 : selected 9 ⟨1245934, by decide⟩
    (prefixPartial 12 355877) = some ⟨12, 2, 0, 1245934, 355877, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_355877_1245934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355877 ⟨1245934, by decide⟩ :=
  accepted_of_selected 12 355877 ⟨1245934, by decide⟩ ⟨12, 2, 0, 1245934, 355877, 2613, 65536⟩
    (by decide) selected_cut_45101

theorem selected_cut_45102 : selected 9 ⟨1245980, by decide⟩
    (prefixPartial 12 355878) = some ⟨12, 2, 0, 1245980, 355878, 2553, 65536⟩ := by
  decide +kernel

theorem context_12_355878_1245980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355878 ⟨1245980, by decide⟩ :=
  accepted_of_selected 12 355878 ⟨1245980, by decide⟩ ⟨12, 2, 0, 1245980, 355878, 2553, 65536⟩
    (by decide) selected_cut_45102

theorem selected_cut_45103 : selected 9 ⟨1246030, by decide⟩
    (prefixPartial 12 355879) = some ⟨12, 2, 0, 1246030, 355879, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_355879_1246030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355879 ⟨1246030, by decide⟩ :=
  accepted_of_selected 12 355879 ⟨1246030, by decide⟩ ⟨12, 2, 0, 1246030, 355879, 3029, 65536⟩
    (by decide) selected_cut_45103

theorem unmarked_context_11_88969_1246031 : frontier 10 ⟨1246031, by decide⟩
    (prefixCache 11 88969) (prefixPartial 11 88969) = false := by
  decide +kernel

theorem node_context_11_88969_1246031 : EJMOriginalGlobalDAGData.nodes 10 ⟨1246031, by decide⟩ =
    .split (coordinate 11) (![⟨1245888, by decide⟩,⟨1245934, by decide⟩,⟨1245980, by decide⟩,⟨1246030, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88969_1246031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88969 ⟨1246031, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88969
    ⟨1246031, by decide⟩ (by decide) (![⟨1245888, by decide⟩,⟨1245934, by decide⟩,⟨1245980, by decide⟩,⟨1246030, by decide⟩]) unmarked_context_11_88969_1246031 node_context_11_88969_1246031
  intro a
  fin_cases a
  · exact context_12_355876_1245888
  · exact context_12_355877_1245934
  · exact context_12_355878_1245980
  · exact context_12_355879_1246030

theorem selected_cut_45104 : selected 9 ⟨1246084, by decide⟩
    (prefixPartial 12 355880) = some ⟨12, 2, 0, 1246084, 355880, 2609, 65536⟩ := by
  decide +kernel

theorem context_12_355880_1246084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355880 ⟨1246084, by decide⟩ :=
  accepted_of_selected 12 355880 ⟨1246084, by decide⟩ ⟨12, 2, 0, 1246084, 355880, 2609, 65536⟩
    (by decide) selected_cut_45104

theorem selected_cut_45105 : selected 9 ⟨1246124, by decide⟩
    (prefixPartial 12 355881) = some ⟨12, 2, 0, 1246124, 355881, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_355881_1246124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355881 ⟨1246124, by decide⟩ :=
  accepted_of_selected 12 355881 ⟨1246124, by decide⟩ ⟨12, 2, 0, 1246124, 355881, 2489, 65536⟩
    (by decide) selected_cut_45105

theorem selected_cut_45106 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 355882) = some ⟨12, 1, 0, 1172910, 355882, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355882_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355882 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 355882 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 355882, 1, 65536⟩
    (by decide) selected_cut_45106

theorem selected_cut_45107 : selected 9 ⟨661672, by decide⟩
    (prefixPartial 12 355883) = some ⟨12, 1, 0, 661672, 355883, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355883_661672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355883 ⟨661672, by decide⟩ :=
  accepted_of_selected 12 355883 ⟨661672, by decide⟩ ⟨12, 1, 0, 661672, 355883, 1, 65536⟩
    (by decide) selected_cut_45107

theorem unmarked_context_11_88970_1246125 : frontier 10 ⟨1246125, by decide⟩
    (prefixCache 11 88970) (prefixPartial 11 88970) = false := by
  decide +kernel

theorem node_context_11_88970_1246125 : EJMOriginalGlobalDAGData.nodes 10 ⟨1246125, by decide⟩ =
    .split (coordinate 11) (![⟨1246084, by decide⟩,⟨1246124, by decide⟩,⟨1172910, by decide⟩,⟨661672, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88970_1246125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88970 ⟨1246125, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88970
    ⟨1246125, by decide⟩ (by decide) (![⟨1246084, by decide⟩,⟨1246124, by decide⟩,⟨1172910, by decide⟩,⟨661672, by decide⟩]) unmarked_context_11_88970_1246125 node_context_11_88970_1246125
  intro a
  fin_cases a
  · exact context_12_355880_1246084
  · exact context_12_355881_1246124
  · exact context_12_355882_1172910
  · exact context_12_355883_661672

theorem selected_cut_45108 : selected 9 ⟨1246166, by decide⟩
    (prefixPartial 12 355884) = some ⟨12, 2, 0, 1246166, 355884, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_355884_1246166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355884 ⟨1246166, by decide⟩ :=
  accepted_of_selected 12 355884 ⟨1246166, by decide⟩ ⟨12, 2, 0, 1246166, 355884, 2445, 65536⟩
    (by decide) selected_cut_45108

theorem selected_cut_45109 : selected 9 ⟨1246207, by decide⟩
    (prefixPartial 12 355885) = some ⟨12, 2, 0, 1246207, 355885, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_355885_1246207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355885 ⟨1246207, by decide⟩ :=
  accepted_of_selected 12 355885 ⟨1246207, by decide⟩ ⟨12, 2, 0, 1246207, 355885, 2353, 65536⟩
    (by decide) selected_cut_45109

theorem selected_cut_45110 : selected 9 ⟨1246253, by decide⟩
    (prefixPartial 12 355886) = some ⟨12, 2, 0, 1246253, 355886, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_355886_1246253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355886 ⟨1246253, by decide⟩ :=
  accepted_of_selected 12 355886 ⟨1246253, by decide⟩ ⟨12, 2, 0, 1246253, 355886, 2421, 65536⟩
    (by decide) selected_cut_45110

theorem selected_cut_45111 : selected 9 ⟨758968, by decide⟩
    (prefixPartial 12 355887) = some ⟨12, 1, 0, 758968, 355887, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355887_758968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355887 ⟨758968, by decide⟩ :=
  accepted_of_selected 12 355887 ⟨758968, by decide⟩ ⟨12, 1, 0, 758968, 355887, 1, 65536⟩
    (by decide) selected_cut_45111

theorem unmarked_context_11_88971_1246254 : frontier 10 ⟨1246254, by decide⟩
    (prefixCache 11 88971) (prefixPartial 11 88971) = false := by
  decide +kernel

theorem node_context_11_88971_1246254 : EJMOriginalGlobalDAGData.nodes 10 ⟨1246254, by decide⟩ =
    .split (coordinate 11) (![⟨1246166, by decide⟩,⟨1246207, by decide⟩,⟨1246253, by decide⟩,⟨758968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88971_1246254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88971 ⟨1246254, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88971
    ⟨1246254, by decide⟩ (by decide) (![⟨1246166, by decide⟩,⟨1246207, by decide⟩,⟨1246253, by decide⟩,⟨758968, by decide⟩]) unmarked_context_11_88971_1246254 node_context_11_88971_1246254
  intro a
  fin_cases a
  · exact context_12_355884_1246166
  · exact context_12_355885_1246207
  · exact context_12_355886_1246253
  · exact context_12_355887_758968

theorem unmarked_context_10_22242_1246255 : frontier 11 ⟨1246255, by decide⟩
    (prefixCache 10 22242) (prefixPartial 10 22242) = false := by
  decide +kernel

theorem node_context_10_22242_1246255 : EJMOriginalGlobalDAGData.nodes 11 ⟨1246255, by decide⟩ =
    .split (coordinate 10) (![⟨1245834, by decide⟩,⟨1246031, by decide⟩,⟨1246125, by decide⟩,⟨1246254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22242_1246255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22242 ⟨1246255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22242
    ⟨1246255, by decide⟩ (by decide) (![⟨1245834, by decide⟩,⟨1246031, by decide⟩,⟨1246125, by decide⟩,⟨1246254, by decide⟩]) unmarked_context_10_22242_1246255 node_context_10_22242_1246255
  intro a
  fin_cases a
  · exact context_11_88968_1245834
  · exact context_11_88969_1246031
  · exact context_11_88970_1246125
  · exact context_11_88971_1246254

theorem selected_cut_45112 : selected 9 ⟨1187656, by decide⟩
    (prefixPartial 12 355888) = some ⟨12, 1, 0, 1187656, 355888, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355888_1187656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355888 ⟨1187656, by decide⟩ :=
  accepted_of_selected 12 355888 ⟨1187656, by decide⟩ ⟨12, 1, 0, 1187656, 355888, 1, 65536⟩
    (by decide) selected_cut_45112

theorem selected_cut_45113 : selected 9 ⟨1246294, by decide⟩
    (prefixPartial 12 355889) = some ⟨12, 2, 0, 1246294, 355889, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_355889_1246294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355889 ⟨1246294, by decide⟩ :=
  accepted_of_selected 12 355889 ⟨1246294, by decide⟩ ⟨12, 2, 0, 1246294, 355889, 2125, 65536⟩
    (by decide) selected_cut_45113

theorem selected_cut_45114 : selected 9 ⟨1246334, by decide⟩
    (prefixPartial 12 355890) = some ⟨12, 2, 0, 1246334, 355890, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_355890_1246334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355890 ⟨1246334, by decide⟩ :=
  accepted_of_selected 12 355890 ⟨1246334, by decide⟩ ⟨12, 2, 0, 1246334, 355890, 2285, 65536⟩
    (by decide) selected_cut_45114

theorem selected_cut_45115 : selected 9 ⟨1246380, by decide⟩
    (prefixPartial 12 355891) = some ⟨12, 2, 0, 1246380, 355891, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_355891_1246380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355891 ⟨1246380, by decide⟩ :=
  accepted_of_selected 12 355891 ⟨1246380, by decide⟩ ⟨12, 2, 0, 1246380, 355891, 2497, 65536⟩
    (by decide) selected_cut_45115

theorem unmarked_context_11_88972_1246381 : frontier 10 ⟨1246381, by decide⟩
    (prefixCache 11 88972) (prefixPartial 11 88972) = false := by
  decide +kernel

theorem node_context_11_88972_1246381 : EJMOriginalGlobalDAGData.nodes 10 ⟨1246381, by decide⟩ =
    .split (coordinate 11) (![⟨1187656, by decide⟩,⟨1246294, by decide⟩,⟨1246334, by decide⟩,⟨1246380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88972_1246381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88972 ⟨1246381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88972
    ⟨1246381, by decide⟩ (by decide) (![⟨1187656, by decide⟩,⟨1246294, by decide⟩,⟨1246334, by decide⟩,⟨1246380, by decide⟩]) unmarked_context_11_88972_1246381 node_context_11_88972_1246381
  intro a
  fin_cases a
  · exact context_12_355888_1187656
  · exact context_12_355889_1246294
  · exact context_12_355890_1246334
  · exact context_12_355891_1246380

theorem selected_cut_45116 : selected 9 ⟨1246417, by decide⟩
    (prefixPartial 12 355892) = some ⟨12, 2, 0, 1246417, 355892, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_355892_1246417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355892 ⟨1246417, by decide⟩ :=
  accepted_of_selected 12 355892 ⟨1246417, by decide⟩ ⟨12, 2, 0, 1246417, 355892, 2209, 65536⟩
    (by decide) selected_cut_45116

theorem selected_cut_45117 : selected 9 ⟨1246447, by decide⟩
    (prefixPartial 12 355893) = some ⟨12, 2, 0, 1246447, 355893, 1945, 65536⟩ := by
  decide +kernel

theorem context_12_355893_1246447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355893 ⟨1246447, by decide⟩ :=
  accepted_of_selected 12 355893 ⟨1246447, by decide⟩ ⟨12, 2, 0, 1246447, 355893, 1945, 65536⟩
    (by decide) selected_cut_45117

theorem selected_cut_45118 : selected 9 ⟨1246476, by decide⟩
    (prefixPartial 12 355894) = some ⟨12, 2, 0, 1246476, 355894, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_355894_1246476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355894 ⟨1246476, by decide⟩ :=
  accepted_of_selected 12 355894 ⟨1246476, by decide⟩ ⟨12, 2, 0, 1246476, 355894, 2017, 65536⟩
    (by decide) selected_cut_45118

theorem selected_cut_45119 : selected 9 ⟨1246509, by decide⟩
    (prefixPartial 12 355895) = some ⟨12, 2, 0, 1246509, 355895, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_355895_1246509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355895 ⟨1246509, by decide⟩ :=
  accepted_of_selected 12 355895 ⟨1246509, by decide⟩ ⟨12, 2, 0, 1246509, 355895, 2181, 65536⟩
    (by decide) selected_cut_45119

theorem unmarked_context_11_88973_1246510 : frontier 10 ⟨1246510, by decide⟩
    (prefixCache 11 88973) (prefixPartial 11 88973) = false := by
  decide +kernel

theorem node_context_11_88973_1246510 : EJMOriginalGlobalDAGData.nodes 10 ⟨1246510, by decide⟩ =
    .split (coordinate 11) (![⟨1246417, by decide⟩,⟨1246447, by decide⟩,⟨1246476, by decide⟩,⟨1246509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88973_1246510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88973 ⟨1246510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88973
    ⟨1246510, by decide⟩ (by decide) (![⟨1246417, by decide⟩,⟨1246447, by decide⟩,⟨1246476, by decide⟩,⟨1246509, by decide⟩]) unmarked_context_11_88973_1246510 node_context_11_88973_1246510
  intro a
  fin_cases a
  · exact context_12_355892_1246417
  · exact context_12_355893_1246447
  · exact context_12_355894_1246476
  · exact context_12_355895_1246509

theorem selected_cut_45120 : selected 9 ⟨1246554, by decide⟩
    (prefixPartial 12 355896) = some ⟨12, 2, 0, 1246554, 355896, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_355896_1246554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355896 ⟨1246554, by decide⟩ :=
  accepted_of_selected 12 355896 ⟨1246554, by decide⟩ ⟨12, 2, 0, 1246554, 355896, 2221, 65536⟩
    (by decide) selected_cut_45120

theorem selected_cut_45121 : selected 9 ⟨1246590, by decide⟩
    (prefixPartial 12 355897) = some ⟨12, 2, 0, 1246590, 355897, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_355897_1246590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355897 ⟨1246590, by decide⟩ :=
  accepted_of_selected 12 355897 ⟨1246590, by decide⟩ ⟨12, 2, 0, 1246590, 355897, 1993, 65536⟩
    (by decide) selected_cut_45121

theorem selected_cut_45122 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 355898) = some ⟨12, 1, 0, 893903, 355898, 1, 65536⟩ := by
  decide +kernel

theorem context_12_355898_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355898 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 355898 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 355898, 1, 65536⟩
    (by decide) selected_cut_45122

theorem selected_cut_45123 : selected 9 ⟨1246633, by decide⟩
    (prefixPartial 12 355899) = some ⟨12, 2, 0, 1246633, 355899, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_355899_1246633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 355899 ⟨1246633, by decide⟩ :=
  accepted_of_selected 12 355899 ⟨1246633, by decide⟩ ⟨12, 2, 0, 1246633, 355899, 2377, 65536⟩
    (by decide) selected_cut_45123

theorem unmarked_context_11_88974_1246634 : frontier 10 ⟨1246634, by decide⟩
    (prefixCache 11 88974) (prefixPartial 11 88974) = false := by
  decide +kernel

theorem node_context_11_88974_1246634 : EJMOriginalGlobalDAGData.nodes 10 ⟨1246634, by decide⟩ =
    .split (coordinate 11) (![⟨1246554, by decide⟩,⟨1246590, by decide⟩,⟨893903, by decide⟩,⟨1246633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_88974_1246634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 88974 ⟨1246634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 88974
    ⟨1246634, by decide⟩ (by decide) (![⟨1246554, by decide⟩,⟨1246590, by decide⟩,⟨893903, by decide⟩,⟨1246633, by decide⟩]) unmarked_context_11_88974_1246634 node_context_11_88974_1246634
  intro a
  fin_cases a
  · exact context_12_355896_1246554
  · exact context_12_355897_1246590
  · exact context_12_355898_893903
  · exact context_12_355899_1246633

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
