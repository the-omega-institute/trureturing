/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover241
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_23235 : selected 8 ⟨588063, by decide⟩
    (prefixPartial 13 305226) = some ⟨13, 2, 0, 588063, 305226, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_305226_588063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305226 ⟨588063, by decide⟩ :=
  accepted_of_selected 13 305226 ⟨588063, by decide⟩ ⟨13, 2, 0, 588063, 305226, 1245, 16384⟩
    (by decide) selected_cut_23235

theorem selected_cut_23236 : selected 8 ⟨588076, by decide⟩
    (prefixPartial 13 305227) = some ⟨13, 2, 0, 588076, 305227, 949, 16384⟩ := by
  decide +kernel

theorem context_13_305227_588076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305227 ⟨588076, by decide⟩ :=
  accepted_of_selected 13 305227 ⟨588076, by decide⟩ ⟨13, 2, 0, 588076, 305227, 949, 16384⟩
    (by decide) selected_cut_23236

theorem unmarked_context_12_76306_588077 : frontier 9 ⟨588077, by decide⟩
    (prefixCache 12 76306) (prefixPartial 12 76306) = false := by
  decide +kernel

theorem node_context_12_76306_588077 : EJMOriginalGlobalDAGData.nodes 9 ⟨588077, by decide⟩ =
    .split (coordinate 12) (![⟨588018, by decide⟩,⟨588042, by decide⟩,⟨588063, by decide⟩,⟨588076, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76306_588077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76306 ⟨588077, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76306
    ⟨588077, by decide⟩ (by decide) (![⟨588018, by decide⟩,⟨588042, by decide⟩,⟨588063, by decide⟩,⟨588076, by decide⟩]) unmarked_context_12_76306_588077 node_context_12_76306_588077
  intro a
  fin_cases a
  · exact context_13_305224_588018
  · exact context_13_305225_588042
  · exact context_13_305226_588063
  · exact context_13_305227_588076

theorem selected_cut_23237 : selected 8 ⟨588137, by decide⟩
    (prefixPartial 13 305228) = some ⟨13, 2, 0, 588137, 305228, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_305228_588137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305228 ⟨588137, by decide⟩ :=
  accepted_of_selected 13 305228 ⟨588137, by decide⟩ ⟨13, 2, 0, 588137, 305228, 2285, 16384⟩
    (by decide) selected_cut_23237

theorem selected_cut_23238 : selected 8 ⟨588170, by decide⟩
    (prefixPartial 13 305229) = some ⟨13, 2, 0, 588170, 305229, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_305229_588170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305229 ⟨588170, by decide⟩ :=
  accepted_of_selected 13 305229 ⟨588170, by decide⟩ ⟨13, 2, 0, 588170, 305229, 2297, 16384⟩
    (by decide) selected_cut_23238

theorem selected_cut_23239 : selected 8 ⟨588191, by decide⟩
    (prefixPartial 13 305230) = some ⟨13, 2, 0, 588191, 305230, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_305230_588191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305230 ⟨588191, by decide⟩ :=
  accepted_of_selected 13 305230 ⟨588191, by decide⟩ ⟨13, 2, 0, 588191, 305230, 1389, 16384⟩
    (by decide) selected_cut_23239

theorem selected_cut_23240 : selected 8 ⟨588209, by decide⟩
    (prefixPartial 13 305231) = some ⟨13, 2, 0, 588209, 305231, 909, 16384⟩ := by
  decide +kernel

theorem context_13_305231_588209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305231 ⟨588209, by decide⟩ :=
  accepted_of_selected 13 305231 ⟨588209, by decide⟩ ⟨13, 2, 0, 588209, 305231, 909, 16384⟩
    (by decide) selected_cut_23240

theorem unmarked_context_12_76307_588210 : frontier 9 ⟨588210, by decide⟩
    (prefixCache 12 76307) (prefixPartial 12 76307) = false := by
  decide +kernel

theorem node_context_12_76307_588210 : EJMOriginalGlobalDAGData.nodes 9 ⟨588210, by decide⟩ =
    .split (coordinate 12) (![⟨588137, by decide⟩,⟨588170, by decide⟩,⟨588191, by decide⟩,⟨588209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76307_588210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76307 ⟨588210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76307
    ⟨588210, by decide⟩ (by decide) (![⟨588137, by decide⟩,⟨588170, by decide⟩,⟨588191, by decide⟩,⟨588209, by decide⟩]) unmarked_context_12_76307_588210 node_context_12_76307_588210
  intro a
  fin_cases a
  · exact context_13_305228_588137
  · exact context_13_305229_588170
  · exact context_13_305230_588191
  · exact context_13_305231_588209

theorem unmarked_context_11_19076_588211 : frontier 10 ⟨588211, by decide⟩
    (prefixCache 11 19076) (prefixPartial 11 19076) = false := by
  decide +kernel

theorem node_context_11_19076_588211 : EJMOriginalGlobalDAGData.nodes 10 ⟨588211, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨587980, by decide⟩,⟨588077, by decide⟩,⟨588210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19076_588211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19076 ⟨588211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19076
    ⟨588211, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨587980, by decide⟩,⟨588077, by decide⟩,⟨588210, by decide⟩]) unmarked_context_11_19076_588211 node_context_11_19076_588211
  intro a
  fin_cases a
  · exact context_12_76304_435160
  · exact context_12_76305_587980
  · exact context_12_76306_588077
  · exact context_12_76307_588210

theorem selected_cut_23241 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 76308) = some ⟨12, 1, 0, 435160, 76308, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76308_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76308 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 76308 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 76308, 1, 65536⟩
    (by decide) selected_cut_23241

theorem selected_cut_23242 : selected 8 ⟨588263, by decide⟩
    (prefixPartial 13 305236) = some ⟨13, 2, 0, 588263, 305236, 2257, 16384⟩ := by
  decide +kernel

theorem context_13_305236_588263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305236 ⟨588263, by decide⟩ :=
  accepted_of_selected 13 305236 ⟨588263, by decide⟩ ⟨13, 2, 0, 588263, 305236, 2257, 16384⟩
    (by decide) selected_cut_23242

theorem selected_cut_23243 : selected 8 ⟨588289, by decide⟩
    (prefixPartial 13 305237) = some ⟨13, 2, 0, 588289, 305237, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_305237_588289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305237 ⟨588289, by decide⟩ :=
  accepted_of_selected 13 305237 ⟨588289, by decide⟩ ⟨13, 2, 0, 588289, 305237, 1889, 16384⟩
    (by decide) selected_cut_23243

theorem selected_cut_23244 : selected 8 ⟨588308, by decide⟩
    (prefixPartial 13 305238) = some ⟨13, 2, 0, 588308, 305238, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_305238_588308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305238 ⟨588308, by decide⟩ :=
  accepted_of_selected 13 305238 ⟨588308, by decide⟩ ⟨13, 2, 0, 588308, 305238, 1361, 16384⟩
    (by decide) selected_cut_23244

theorem selected_cut_23245 : selected 8 ⟨588321, by decide⟩
    (prefixPartial 13 305239) = some ⟨13, 2, 0, 588321, 305239, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_305239_588321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305239 ⟨588321, by decide⟩ :=
  accepted_of_selected 13 305239 ⟨588321, by decide⟩ ⟨13, 2, 0, 588321, 305239, 1057, 16384⟩
    (by decide) selected_cut_23245

theorem unmarked_context_12_76309_588322 : frontier 9 ⟨588322, by decide⟩
    (prefixCache 12 76309) (prefixPartial 12 76309) = false := by
  decide +kernel

theorem node_context_12_76309_588322 : EJMOriginalGlobalDAGData.nodes 9 ⟨588322, by decide⟩ =
    .split (coordinate 12) (![⟨588263, by decide⟩,⟨588289, by decide⟩,⟨588308, by decide⟩,⟨588321, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76309_588322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76309 ⟨588322, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76309
    ⟨588322, by decide⟩ (by decide) (![⟨588263, by decide⟩,⟨588289, by decide⟩,⟨588308, by decide⟩,⟨588321, by decide⟩]) unmarked_context_12_76309_588322 node_context_12_76309_588322
  intro a
  fin_cases a
  · exact context_13_305236_588263
  · exact context_13_305237_588289
  · exact context_13_305238_588308
  · exact context_13_305239_588321

theorem selected_cut_23246 : selected 8 ⟨588358, by decide⟩
    (prefixPartial 13 305240) = some ⟨13, 2, 0, 588358, 305240, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_305240_588358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305240 ⟨588358, by decide⟩ :=
  accepted_of_selected 13 305240 ⟨588358, by decide⟩ ⟨13, 2, 0, 588358, 305240, 1949, 16384⟩
    (by decide) selected_cut_23246

theorem selected_cut_23247 : selected 8 ⟨588383, by decide⟩
    (prefixPartial 13 305241) = some ⟨13, 2, 0, 588383, 305241, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_305241_588383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305241 ⟨588383, by decide⟩ :=
  accepted_of_selected 13 305241 ⟨588383, by decide⟩ ⟨13, 2, 0, 588383, 305241, 1933, 16384⟩
    (by decide) selected_cut_23247

theorem selected_cut_23248 : selected 8 ⟨588401, by decide⟩
    (prefixPartial 13 305242) = some ⟨13, 2, 0, 588401, 305242, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_305242_588401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305242 ⟨588401, by decide⟩ :=
  accepted_of_selected 13 305242 ⟨588401, by decide⟩ ⟨13, 2, 0, 588401, 305242, 1269, 16384⟩
    (by decide) selected_cut_23248

theorem selected_cut_23249 : selected 8 ⟨588420, by decide⟩
    (prefixPartial 13 305243) = some ⟨13, 2, 0, 588420, 305243, 1053, 16384⟩ := by
  decide +kernel

theorem context_13_305243_588420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305243 ⟨588420, by decide⟩ :=
  accepted_of_selected 13 305243 ⟨588420, by decide⟩ ⟨13, 2, 0, 588420, 305243, 1053, 16384⟩
    (by decide) selected_cut_23249

theorem unmarked_context_12_76310_588421 : frontier 9 ⟨588421, by decide⟩
    (prefixCache 12 76310) (prefixPartial 12 76310) = false := by
  decide +kernel

theorem node_context_12_76310_588421 : EJMOriginalGlobalDAGData.nodes 9 ⟨588421, by decide⟩ =
    .split (coordinate 12) (![⟨588358, by decide⟩,⟨588383, by decide⟩,⟨588401, by decide⟩,⟨588420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76310_588421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76310 ⟨588421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76310
    ⟨588421, by decide⟩ (by decide) (![⟨588358, by decide⟩,⟨588383, by decide⟩,⟨588401, by decide⟩,⟨588420, by decide⟩]) unmarked_context_12_76310_588421 node_context_12_76310_588421
  intro a
  fin_cases a
  · exact context_13_305240_588358
  · exact context_13_305241_588383
  · exact context_13_305242_588401
  · exact context_13_305243_588420

theorem selected_cut_23250 : selected 8 ⟨588495, by decide⟩
    (prefixPartial 13 305244) = some ⟨13, 2, 0, 588495, 305244, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_305244_588495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305244 ⟨588495, by decide⟩ :=
  accepted_of_selected 13 305244 ⟨588495, by decide⟩ ⟨13, 2, 0, 588495, 305244, 2493, 16384⟩
    (by decide) selected_cut_23250

theorem selected_cut_23251 : selected 8 ⟨588526, by decide⟩
    (prefixPartial 13 305245) = some ⟨13, 2, 0, 588526, 305245, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_305245_588526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305245 ⟨588526, by decide⟩ :=
  accepted_of_selected 13 305245 ⟨588526, by decide⟩ ⟨13, 2, 0, 588526, 305245, 2253, 16384⟩
    (by decide) selected_cut_23251

theorem selected_cut_23252 : selected 8 ⟨588545, by decide⟩
    (prefixPartial 13 305246) = some ⟨13, 2, 0, 588545, 305246, 1449, 16384⟩ := by
  decide +kernel

theorem context_13_305246_588545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305246 ⟨588545, by decide⟩ :=
  accepted_of_selected 13 305246 ⟨588545, by decide⟩ ⟨13, 2, 0, 588545, 305246, 1449, 16384⟩
    (by decide) selected_cut_23252

theorem selected_cut_23253 : selected 8 ⟨588557, by decide⟩
    (prefixPartial 13 305247) = some ⟨13, 2, 0, 588557, 305247, 981, 16384⟩ := by
  decide +kernel

theorem context_13_305247_588557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305247 ⟨588557, by decide⟩ :=
  accepted_of_selected 13 305247 ⟨588557, by decide⟩ ⟨13, 2, 0, 588557, 305247, 981, 16384⟩
    (by decide) selected_cut_23253

theorem unmarked_context_12_76311_588558 : frontier 9 ⟨588558, by decide⟩
    (prefixCache 12 76311) (prefixPartial 12 76311) = false := by
  decide +kernel

theorem node_context_12_76311_588558 : EJMOriginalGlobalDAGData.nodes 9 ⟨588558, by decide⟩ =
    .split (coordinate 12) (![⟨588495, by decide⟩,⟨588526, by decide⟩,⟨588545, by decide⟩,⟨588557, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76311_588558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76311 ⟨588558, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76311
    ⟨588558, by decide⟩ (by decide) (![⟨588495, by decide⟩,⟨588526, by decide⟩,⟨588545, by decide⟩,⟨588557, by decide⟩]) unmarked_context_12_76311_588558 node_context_12_76311_588558
  intro a
  fin_cases a
  · exact context_13_305244_588495
  · exact context_13_305245_588526
  · exact context_13_305246_588545
  · exact context_13_305247_588557

theorem unmarked_context_11_19077_588559 : frontier 10 ⟨588559, by decide⟩
    (prefixCache 11 19077) (prefixPartial 11 19077) = false := by
  decide +kernel

theorem node_context_11_19077_588559 : EJMOriginalGlobalDAGData.nodes 10 ⟨588559, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨588322, by decide⟩,⟨588421, by decide⟩,⟨588558, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19077_588559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19077 ⟨588559, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19077
    ⟨588559, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨588322, by decide⟩,⟨588421, by decide⟩,⟨588558, by decide⟩]) unmarked_context_11_19077_588559 node_context_11_19077_588559
  intro a
  fin_cases a
  · exact context_12_76308_435160
  · exact context_12_76309_588322
  · exact context_12_76310_588421
  · exact context_12_76311_588558

theorem selected_cut_23254 : selected 8 ⟨588607, by decide⟩
    (prefixPartial 13 305248) = some ⟨13, 2, 0, 588607, 305248, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_305248_588607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305248 ⟨588607, by decide⟩ :=
  accepted_of_selected 13 305248 ⟨588607, by decide⟩ ⟨13, 2, 0, 588607, 305248, 1101, 16384⟩
    (by decide) selected_cut_23254

theorem selected_cut_23255 : selected 8 ⟨588655, by decide⟩
    (prefixPartial 13 305249) = some ⟨13, 2, 0, 588655, 305249, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_305249_588655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305249 ⟨588655, by decide⟩ :=
  accepted_of_selected 13 305249 ⟨588655, by decide⟩ ⟨13, 2, 0, 588655, 305249, 1753, 16384⟩
    (by decide) selected_cut_23255

theorem selected_cut_23256 : selected 8 ⟨588682, by decide⟩
    (prefixPartial 13 305250) = some ⟨13, 2, 0, 588682, 305250, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_305250_588682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305250 ⟨588682, by decide⟩ :=
  accepted_of_selected 13 305250 ⟨588682, by decide⟩ ⟨13, 2, 0, 588682, 305250, 1093, 16384⟩
    (by decide) selected_cut_23256

theorem selected_cut_23257 : selected 8 ⟨588726, by decide⟩
    (prefixPartial 13 305251) = some ⟨13, 2, 0, 588726, 305251, 801, 16384⟩ := by
  decide +kernel

theorem context_13_305251_588726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305251 ⟨588726, by decide⟩ :=
  accepted_of_selected 13 305251 ⟨588726, by decide⟩ ⟨13, 2, 0, 588726, 305251, 801, 16384⟩
    (by decide) selected_cut_23257

theorem unmarked_context_12_76312_588727 : frontier 9 ⟨588727, by decide⟩
    (prefixCache 12 76312) (prefixPartial 12 76312) = false := by
  decide +kernel

theorem node_context_12_76312_588727 : EJMOriginalGlobalDAGData.nodes 9 ⟨588727, by decide⟩ =
    .split (coordinate 12) (![⟨588607, by decide⟩,⟨588655, by decide⟩,⟨588682, by decide⟩,⟨588726, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76312_588727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76312 ⟨588727, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76312
    ⟨588727, by decide⟩ (by decide) (![⟨588607, by decide⟩,⟨588655, by decide⟩,⟨588682, by decide⟩,⟨588726, by decide⟩]) unmarked_context_12_76312_588727 node_context_12_76312_588727
  intro a
  fin_cases a
  · exact context_13_305248_588607
  · exact context_13_305249_588655
  · exact context_13_305250_588682
  · exact context_13_305251_588726

theorem selected_cut_23258 : selected 8 ⟨588781, by decide⟩
    (prefixPartial 13 305252) = some ⟨13, 2, 0, 588781, 305252, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_305252_588781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305252 ⟨588781, by decide⟩ :=
  accepted_of_selected 13 305252 ⟨588781, by decide⟩ ⟨13, 2, 0, 588781, 305252, 1789, 16384⟩
    (by decide) selected_cut_23258

theorem selected_cut_23259 : selected 8 ⟨588809, by decide⟩
    (prefixPartial 13 305253) = some ⟨13, 2, 0, 588809, 305253, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_305253_588809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305253 ⟨588809, by decide⟩ :=
  accepted_of_selected 13 305253 ⟨588809, by decide⟩ ⟨13, 2, 0, 588809, 305253, 1617, 16384⟩
    (by decide) selected_cut_23259

theorem selected_cut_23260 : selected 8 ⟨588828, by decide⟩
    (prefixPartial 13 305254) = some ⟨13, 2, 0, 588828, 305254, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_305254_588828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305254 ⟨588828, by decide⟩ :=
  accepted_of_selected 13 305254 ⟨588828, by decide⟩ ⟨13, 2, 0, 588828, 305254, 1329, 16384⟩
    (by decide) selected_cut_23260

theorem selected_cut_23261 : selected 8 ⟨588846, by decide⟩
    (prefixPartial 13 305255) = some ⟨13, 2, 0, 588846, 305255, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_305255_588846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305255 ⟨588846, by decide⟩ :=
  accepted_of_selected 13 305255 ⟨588846, by decide⟩ ⟨13, 2, 0, 588846, 305255, 1033, 16384⟩
    (by decide) selected_cut_23261

theorem unmarked_context_12_76313_588847 : frontier 9 ⟨588847, by decide⟩
    (prefixCache 12 76313) (prefixPartial 12 76313) = false := by
  decide +kernel

theorem node_context_12_76313_588847 : EJMOriginalGlobalDAGData.nodes 9 ⟨588847, by decide⟩ =
    .split (coordinate 12) (![⟨588781, by decide⟩,⟨588809, by decide⟩,⟨588828, by decide⟩,⟨588846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76313_588847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76313 ⟨588847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76313
    ⟨588847, by decide⟩ (by decide) (![⟨588781, by decide⟩,⟨588809, by decide⟩,⟨588828, by decide⟩,⟨588846, by decide⟩]) unmarked_context_12_76313_588847 node_context_12_76313_588847
  intro a
  fin_cases a
  · exact context_13_305252_588781
  · exact context_13_305253_588809
  · exact context_13_305254_588828
  · exact context_13_305255_588846

theorem selected_cut_23262 : selected 8 ⟨588953, by decide⟩
    (prefixPartial 13 305256) = some ⟨13, 2, 0, 588953, 305256, 2137, 16384⟩ := by
  decide +kernel

theorem context_13_305256_588953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305256 ⟨588953, by decide⟩ :=
  accepted_of_selected 13 305256 ⟨588953, by decide⟩ ⟨13, 2, 0, 588953, 305256, 2137, 16384⟩
    (by decide) selected_cut_23262

theorem selected_cut_23263 : selected 8 ⟨589011, by decide⟩
    (prefixPartial 13 305257) = some ⟨13, 2, 0, 589011, 305257, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_305257_589011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305257 ⟨589011, by decide⟩ :=
  accepted_of_selected 13 305257 ⟨589011, by decide⟩ ⟨13, 2, 0, 589011, 305257, 2193, 16384⟩
    (by decide) selected_cut_23263

theorem selected_cut_23264 : selected 8 ⟨589045, by decide⟩
    (prefixPartial 13 305258) = some ⟨13, 2, 0, 589045, 305258, 945, 16384⟩ := by
  decide +kernel

theorem context_13_305258_589045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305258 ⟨589045, by decide⟩ :=
  accepted_of_selected 13 305258 ⟨589045, by decide⟩ ⟨13, 2, 0, 589045, 305258, 945, 16384⟩
    (by decide) selected_cut_23264

theorem selected_cut_23265 : selected 8 ⟨589063, by decide⟩
    (prefixPartial 13 305259) = some ⟨13, 2, 0, 589063, 305259, 293, 16384⟩ := by
  decide +kernel

theorem context_13_305259_589063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305259 ⟨589063, by decide⟩ :=
  accepted_of_selected 13 305259 ⟨589063, by decide⟩ ⟨13, 2, 0, 589063, 305259, 293, 16384⟩
    (by decide) selected_cut_23265

theorem unmarked_context_12_76314_589064 : frontier 9 ⟨589064, by decide⟩
    (prefixCache 12 76314) (prefixPartial 12 76314) = false := by
  decide +kernel

theorem node_context_12_76314_589064 : EJMOriginalGlobalDAGData.nodes 9 ⟨589064, by decide⟩ =
    .split (coordinate 12) (![⟨588953, by decide⟩,⟨589011, by decide⟩,⟨589045, by decide⟩,⟨589063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76314_589064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76314 ⟨589064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76314
    ⟨589064, by decide⟩ (by decide) (![⟨588953, by decide⟩,⟨589011, by decide⟩,⟨589045, by decide⟩,⟨589063, by decide⟩]) unmarked_context_12_76314_589064 node_context_12_76314_589064
  intro a
  fin_cases a
  · exact context_13_305256_588953
  · exact context_13_305257_589011
  · exact context_13_305258_589045
  · exact context_13_305259_589063

theorem selected_cut_23266 : selected 8 ⟨589113, by decide⟩
    (prefixPartial 13 305260) = some ⟨13, 2, 0, 589113, 305260, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_305260_589113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305260 ⟨589113, by decide⟩ :=
  accepted_of_selected 13 305260 ⟨589113, by decide⟩ ⟨13, 2, 0, 589113, 305260, 1557, 16384⟩
    (by decide) selected_cut_23266

theorem selected_cut_23267 : selected 8 ⟨589150, by decide⟩
    (prefixPartial 13 305261) = some ⟨13, 2, 0, 589150, 305261, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_305261_589150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305261 ⟨589150, by decide⟩ :=
  accepted_of_selected 13 305261 ⟨589150, by decide⟩ ⟨13, 2, 0, 589150, 305261, 2025, 16384⟩
    (by decide) selected_cut_23267

theorem selected_cut_23268 : selected 8 ⟨589166, by decide⟩
    (prefixPartial 13 305262) = some ⟨13, 2, 0, 589166, 305262, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_305262_589166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305262 ⟨589166, by decide⟩ :=
  accepted_of_selected 13 305262 ⟨589166, by decide⟩ ⟨13, 2, 0, 589166, 305262, 1145, 16384⟩
    (by decide) selected_cut_23268

theorem selected_cut_23269 : selected 8 ⟨589173, by decide⟩
    (prefixPartial 13 305263) = some ⟨13, 2, 0, 589173, 305263, 789, 16384⟩ := by
  decide +kernel

theorem context_13_305263_589173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305263 ⟨589173, by decide⟩ :=
  accepted_of_selected 13 305263 ⟨589173, by decide⟩ ⟨13, 2, 0, 589173, 305263, 789, 16384⟩
    (by decide) selected_cut_23269

theorem unmarked_context_12_76315_589174 : frontier 9 ⟨589174, by decide⟩
    (prefixCache 12 76315) (prefixPartial 12 76315) = false := by
  decide +kernel

theorem node_context_12_76315_589174 : EJMOriginalGlobalDAGData.nodes 9 ⟨589174, by decide⟩ =
    .split (coordinate 12) (![⟨589113, by decide⟩,⟨589150, by decide⟩,⟨589166, by decide⟩,⟨589173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76315_589174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76315 ⟨589174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76315
    ⟨589174, by decide⟩ (by decide) (![⟨589113, by decide⟩,⟨589150, by decide⟩,⟨589166, by decide⟩,⟨589173, by decide⟩]) unmarked_context_12_76315_589174 node_context_12_76315_589174
  intro a
  fin_cases a
  · exact context_13_305260_589113
  · exact context_13_305261_589150
  · exact context_13_305262_589166
  · exact context_13_305263_589173

theorem unmarked_context_11_19078_589175 : frontier 10 ⟨589175, by decide⟩
    (prefixCache 11 19078) (prefixPartial 11 19078) = false := by
  decide +kernel

theorem node_context_11_19078_589175 : EJMOriginalGlobalDAGData.nodes 10 ⟨589175, by decide⟩ =
    .split (coordinate 11) (![⟨588727, by decide⟩,⟨588847, by decide⟩,⟨589064, by decide⟩,⟨589174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19078_589175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19078 ⟨589175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19078
    ⟨589175, by decide⟩ (by decide) (![⟨588727, by decide⟩,⟨588847, by decide⟩,⟨589064, by decide⟩,⟨589174, by decide⟩]) unmarked_context_11_19078_589175 node_context_11_19078_589175
  intro a
  fin_cases a
  · exact context_12_76312_588727
  · exact context_12_76313_588847
  · exact context_12_76314_589064
  · exact context_12_76315_589174

theorem selected_cut_23270 : selected 8 ⟨589233, by decide⟩
    (prefixPartial 13 305264) = some ⟨13, 2, 0, 589233, 305264, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_305264_589233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305264 ⟨589233, by decide⟩ :=
  accepted_of_selected 13 305264 ⟨589233, by decide⟩ ⟨13, 2, 0, 589233, 305264, 2105, 16384⟩
    (by decide) selected_cut_23270

theorem selected_cut_23271 : selected 8 ⟨589292, by decide⟩
    (prefixPartial 13 305265) = some ⟨13, 2, 0, 589292, 305265, 3277, 16384⟩ := by
  decide +kernel

theorem context_13_305265_589292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305265 ⟨589292, by decide⟩ :=
  accepted_of_selected 13 305265 ⟨589292, by decide⟩ ⟨13, 2, 0, 589292, 305265, 3277, 16384⟩
    (by decide) selected_cut_23271

theorem selected_cut_23272 : selected 8 ⟨589318, by decide⟩
    (prefixPartial 13 305266) = some ⟨13, 2, 0, 589318, 305266, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_305266_589318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305266 ⟨589318, by decide⟩ :=
  accepted_of_selected 13 305266 ⟨589318, by decide⟩ ⟨13, 2, 0, 589318, 305266, 1957, 16384⟩
    (by decide) selected_cut_23272

theorem selected_cut_23273 : selected 8 ⟨589354, by decide⟩
    (prefixPartial 13 305267) = some ⟨13, 2, 0, 589354, 305267, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_305267_589354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305267 ⟨589354, by decide⟩ :=
  accepted_of_selected 13 305267 ⟨589354, by decide⟩ ⟨13, 2, 0, 589354, 305267, 1261, 16384⟩
    (by decide) selected_cut_23273

theorem unmarked_context_12_76316_589355 : frontier 9 ⟨589355, by decide⟩
    (prefixCache 12 76316) (prefixPartial 12 76316) = false := by
  decide +kernel

theorem node_context_12_76316_589355 : EJMOriginalGlobalDAGData.nodes 9 ⟨589355, by decide⟩ =
    .split (coordinate 12) (![⟨589233, by decide⟩,⟨589292, by decide⟩,⟨589318, by decide⟩,⟨589354, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76316_589355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76316 ⟨589355, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76316
    ⟨589355, by decide⟩ (by decide) (![⟨589233, by decide⟩,⟨589292, by decide⟩,⟨589318, by decide⟩,⟨589354, by decide⟩]) unmarked_context_12_76316_589355 node_context_12_76316_589355
  intro a
  fin_cases a
  · exact context_13_305264_589233
  · exact context_13_305265_589292
  · exact context_13_305266_589318
  · exact context_13_305267_589354

theorem selected_cut_23274 : selected 8 ⟨589387, by decide⟩
    (prefixPartial 13 305268) = some ⟨13, 2, 0, 589387, 305268, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_305268_589387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305268 ⟨589387, by decide⟩ :=
  accepted_of_selected 13 305268 ⟨589387, by decide⟩ ⟨13, 2, 0, 589387, 305268, 1641, 16384⟩
    (by decide) selected_cut_23274

theorem selected_cut_23275 : selected 8 ⟨589421, by decide⟩
    (prefixPartial 13 305269) = some ⟨13, 2, 0, 589421, 305269, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_305269_589421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305269 ⟨589421, by decide⟩ :=
  accepted_of_selected 13 305269 ⟨589421, by decide⟩ ⟨13, 2, 0, 589421, 305269, 2269, 16384⟩
    (by decide) selected_cut_23275

theorem selected_cut_23276 : selected 8 ⟨589439, by decide⟩
    (prefixPartial 13 305270) = some ⟨13, 2, 0, 589439, 305270, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_305270_589439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305270 ⟨589439, by decide⟩ :=
  accepted_of_selected 13 305270 ⟨589439, by decide⟩ ⟨13, 2, 0, 589439, 305270, 1405, 16384⟩
    (by decide) selected_cut_23276

theorem selected_cut_23277 : selected 8 ⟨589452, by decide⟩
    (prefixPartial 13 305271) = some ⟨13, 2, 0, 589452, 305271, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_305271_589452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305271 ⟨589452, by decide⟩ :=
  accepted_of_selected 13 305271 ⟨589452, by decide⟩ ⟨13, 2, 0, 589452, 305271, 1065, 16384⟩
    (by decide) selected_cut_23277

theorem unmarked_context_12_76317_589453 : frontier 9 ⟨589453, by decide⟩
    (prefixCache 12 76317) (prefixPartial 12 76317) = false := by
  decide +kernel

theorem node_context_12_76317_589453 : EJMOriginalGlobalDAGData.nodes 9 ⟨589453, by decide⟩ =
    .split (coordinate 12) (![⟨589387, by decide⟩,⟨589421, by decide⟩,⟨589439, by decide⟩,⟨589452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76317_589453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76317 ⟨589453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76317
    ⟨589453, by decide⟩ (by decide) (![⟨589387, by decide⟩,⟨589421, by decide⟩,⟨589439, by decide⟩,⟨589452, by decide⟩]) unmarked_context_12_76317_589453 node_context_12_76317_589453
  intro a
  fin_cases a
  · exact context_13_305268_589387
  · exact context_13_305269_589421
  · exact context_13_305270_589439
  · exact context_13_305271_589452

theorem selected_cut_23278 : selected 8 ⟨589483, by decide⟩
    (prefixPartial 13 305272) = some ⟨13, 2, 0, 589483, 305272, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_305272_589483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305272 ⟨589483, by decide⟩ :=
  accepted_of_selected 13 305272 ⟨589483, by decide⟩ ⟨13, 2, 0, 589483, 305272, 1301, 16384⟩
    (by decide) selected_cut_23278

theorem selected_cut_23279 : selected 8 ⟨589515, by decide⟩
    (prefixPartial 13 305273) = some ⟨13, 2, 0, 589515, 305273, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_305273_589515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305273 ⟨589515, by decide⟩ :=
  accepted_of_selected 13 305273 ⟨589515, by decide⟩ ⟨13, 2, 0, 589515, 305273, 2189, 16384⟩
    (by decide) selected_cut_23279

theorem selected_cut_23280 : selected 8 ⟨589533, by decide⟩
    (prefixPartial 13 305274) = some ⟨13, 2, 0, 589533, 305274, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_305274_589533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305274 ⟨589533, by decide⟩ :=
  accepted_of_selected 13 305274 ⟨589533, by decide⟩ ⟨13, 2, 0, 589533, 305274, 1245, 16384⟩
    (by decide) selected_cut_23280

theorem selected_cut_23281 : selected 8 ⟨589543, by decide⟩
    (prefixPartial 13 305275) = some ⟨13, 2, 0, 589543, 305275, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_305275_589543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305275 ⟨589543, by decide⟩ :=
  accepted_of_selected 13 305275 ⟨589543, by decide⟩ ⟨13, 2, 0, 589543, 305275, 1001, 16384⟩
    (by decide) selected_cut_23281

theorem unmarked_context_12_76318_589544 : frontier 9 ⟨589544, by decide⟩
    (prefixCache 12 76318) (prefixPartial 12 76318) = false := by
  decide +kernel

theorem node_context_12_76318_589544 : EJMOriginalGlobalDAGData.nodes 9 ⟨589544, by decide⟩ =
    .split (coordinate 12) (![⟨589483, by decide⟩,⟨589515, by decide⟩,⟨589533, by decide⟩,⟨589543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76318_589544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76318 ⟨589544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76318
    ⟨589544, by decide⟩ (by decide) (![⟨589483, by decide⟩,⟨589515, by decide⟩,⟨589533, by decide⟩,⟨589543, by decide⟩]) unmarked_context_12_76318_589544 node_context_12_76318_589544
  intro a
  fin_cases a
  · exact context_13_305272_589483
  · exact context_13_305273_589515
  · exact context_13_305274_589533
  · exact context_13_305275_589543

theorem selected_cut_23282 : selected 8 ⟨589581, by decide⟩
    (prefixPartial 13 305276) = some ⟨13, 2, 0, 589581, 305276, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_305276_589581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305276 ⟨589581, by decide⟩ :=
  accepted_of_selected 13 305276 ⟨589581, by decide⟩ ⟨13, 2, 0, 589581, 305276, 1401, 16384⟩
    (by decide) selected_cut_23282

theorem selected_cut_23283 : selected 8 ⟨589618, by decide⟩
    (prefixPartial 13 305277) = some ⟨13, 2, 0, 589618, 305277, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_305277_589618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305277 ⟨589618, by decide⟩ :=
  accepted_of_selected 13 305277 ⟨589618, by decide⟩ ⟨13, 2, 0, 589618, 305277, 2497, 16384⟩
    (by decide) selected_cut_23283

theorem selected_cut_23284 : selected 8 ⟨589636, by decide⟩
    (prefixPartial 13 305278) = some ⟨13, 2, 0, 589636, 305278, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_305278_589636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305278 ⟨589636, by decide⟩ :=
  accepted_of_selected 13 305278 ⟨589636, by decide⟩ ⟨13, 2, 0, 589636, 305278, 1429, 16384⟩
    (by decide) selected_cut_23284

theorem selected_cut_23285 : selected 8 ⟨589647, by decide⟩
    (prefixPartial 13 305279) = some ⟨13, 2, 0, 589647, 305279, 965, 16384⟩ := by
  decide +kernel

theorem context_13_305279_589647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305279 ⟨589647, by decide⟩ :=
  accepted_of_selected 13 305279 ⟨589647, by decide⟩ ⟨13, 2, 0, 589647, 305279, 965, 16384⟩
    (by decide) selected_cut_23285

theorem unmarked_context_12_76319_589648 : frontier 9 ⟨589648, by decide⟩
    (prefixCache 12 76319) (prefixPartial 12 76319) = false := by
  decide +kernel

theorem node_context_12_76319_589648 : EJMOriginalGlobalDAGData.nodes 9 ⟨589648, by decide⟩ =
    .split (coordinate 12) (![⟨589581, by decide⟩,⟨589618, by decide⟩,⟨589636, by decide⟩,⟨589647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76319_589648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76319 ⟨589648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76319
    ⟨589648, by decide⟩ (by decide) (![⟨589581, by decide⟩,⟨589618, by decide⟩,⟨589636, by decide⟩,⟨589647, by decide⟩]) unmarked_context_12_76319_589648 node_context_12_76319_589648
  intro a
  fin_cases a
  · exact context_13_305276_589581
  · exact context_13_305277_589618
  · exact context_13_305278_589636
  · exact context_13_305279_589647

theorem unmarked_context_11_19079_589649 : frontier 10 ⟨589649, by decide⟩
    (prefixCache 11 19079) (prefixPartial 11 19079) = false := by
  decide +kernel

theorem node_context_11_19079_589649 : EJMOriginalGlobalDAGData.nodes 10 ⟨589649, by decide⟩ =
    .split (coordinate 11) (![⟨589355, by decide⟩,⟨589453, by decide⟩,⟨589544, by decide⟩,⟨589648, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19079_589649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19079 ⟨589649, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19079
    ⟨589649, by decide⟩ (by decide) (![⟨589355, by decide⟩,⟨589453, by decide⟩,⟨589544, by decide⟩,⟨589648, by decide⟩]) unmarked_context_11_19079_589649 node_context_11_19079_589649
  intro a
  fin_cases a
  · exact context_12_76316_589355
  · exact context_12_76317_589453
  · exact context_12_76318_589544
  · exact context_12_76319_589648

theorem unmarked_context_10_4769_589650 : frontier 11 ⟨589650, by decide⟩
    (prefixCache 10 4769) (prefixPartial 10 4769) = false := by
  decide +kernel

theorem node_context_10_4769_589650 : EJMOriginalGlobalDAGData.nodes 11 ⟨589650, by decide⟩ =
    .split (coordinate 10) (![⟨588211, by decide⟩,⟨588559, by decide⟩,⟨589175, by decide⟩,⟨589649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4769_589650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4769 ⟨589650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4769
    ⟨589650, by decide⟩ (by decide) (![⟨588211, by decide⟩,⟨588559, by decide⟩,⟨589175, by decide⟩,⟨589649, by decide⟩]) unmarked_context_10_4769_589650 node_context_10_4769_589650
  intro a
  fin_cases a
  · exact context_11_19076_588211
  · exact context_11_19077_588559
  · exact context_11_19078_589175
  · exact context_11_19079_589649

theorem selected_cut_23286 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 76320) = some ⟨12, 1, 0, 435790, 76320, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76320_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76320 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 76320 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 76320, 1, 65536⟩
    (by decide) selected_cut_23286

theorem selected_cut_23287 : selected 8 ⟨589666, by decide⟩
    (prefixPartial 13 305284) = some ⟨13, 2, 0, 589666, 305284, 957, 16384⟩ := by
  decide +kernel

theorem context_13_305284_589666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305284 ⟨589666, by decide⟩ :=
  accepted_of_selected 13 305284 ⟨589666, by decide⟩ ⟨13, 2, 0, 589666, 305284, 957, 16384⟩
    (by decide) selected_cut_23287

theorem selected_cut_23288 : selected 8 ⟨589689, by decide⟩
    (prefixPartial 13 305285) = some ⟨13, 2, 0, 589689, 305285, 1701, 16384⟩ := by
  decide +kernel

theorem context_13_305285_589689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305285 ⟨589689, by decide⟩ :=
  accepted_of_selected 13 305285 ⟨589689, by decide⟩ ⟨13, 2, 0, 589689, 305285, 1701, 16384⟩
    (by decide) selected_cut_23288

theorem selected_cut_23289 : selected 8 ⟨589704, by decide⟩
    (prefixPartial 13 305286) = some ⟨13, 2, 0, 589704, 305286, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_305286_589704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305286 ⟨589704, by decide⟩ :=
  accepted_of_selected 13 305286 ⟨589704, by decide⟩ ⟨13, 2, 0, 589704, 305286, 1221, 16384⟩
    (by decide) selected_cut_23289

theorem selected_cut_23290 : selected 8 ⟨589714, by decide⟩
    (prefixPartial 13 305287) = some ⟨13, 2, 0, 589714, 305287, 857, 16384⟩ := by
  decide +kernel

theorem context_13_305287_589714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305287 ⟨589714, by decide⟩ :=
  accepted_of_selected 13 305287 ⟨589714, by decide⟩ ⟨13, 2, 0, 589714, 305287, 857, 16384⟩
    (by decide) selected_cut_23290

theorem unmarked_context_12_76321_589715 : frontier 9 ⟨589715, by decide⟩
    (prefixCache 12 76321) (prefixPartial 12 76321) = false := by
  decide +kernel

theorem node_context_12_76321_589715 : EJMOriginalGlobalDAGData.nodes 9 ⟨589715, by decide⟩ =
    .split (coordinate 12) (![⟨589666, by decide⟩,⟨589689, by decide⟩,⟨589704, by decide⟩,⟨589714, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76321_589715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76321 ⟨589715, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76321
    ⟨589715, by decide⟩ (by decide) (![⟨589666, by decide⟩,⟨589689, by decide⟩,⟨589704, by decide⟩,⟨589714, by decide⟩]) unmarked_context_12_76321_589715 node_context_12_76321_589715
  intro a
  fin_cases a
  · exact context_13_305284_589666
  · exact context_13_305285_589689
  · exact context_13_305286_589704
  · exact context_13_305287_589714

theorem selected_cut_23291 : selected 9 ⟨589775, by decide⟩
    (prefixPartial 12 76322) = some ⟨12, 2, 0, 589775, 76322, 3537, 65536⟩ := by
  decide +kernel

theorem context_12_76322_589775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76322 ⟨589775, by decide⟩ :=
  accepted_of_selected 12 76322 ⟨589775, by decide⟩ ⟨12, 2, 0, 589775, 76322, 3537, 65536⟩
    (by decide) selected_cut_23291

theorem selected_cut_23292 : selected 8 ⟨589799, by decide⟩
    (prefixPartial 13 305292) = some ⟨13, 2, 0, 589799, 305292, 969, 16384⟩ := by
  decide +kernel

theorem context_13_305292_589799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305292 ⟨589799, by decide⟩ :=
  accepted_of_selected 13 305292 ⟨589799, by decide⟩ ⟨13, 2, 0, 589799, 305292, 969, 16384⟩
    (by decide) selected_cut_23292

theorem selected_cut_23293 : selected 8 ⟨589823, by decide⟩
    (prefixPartial 13 305293) = some ⟨13, 2, 0, 589823, 305293, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_305293_589823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305293 ⟨589823, by decide⟩ :=
  accepted_of_selected 13 305293 ⟨589823, by decide⟩ ⟨13, 2, 0, 589823, 305293, 1913, 16384⟩
    (by decide) selected_cut_23293

theorem selected_cut_23294 : selected 8 ⟨589842, by decide⟩
    (prefixPartial 13 305294) = some ⟨13, 2, 0, 589842, 305294, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_305294_589842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305294 ⟨589842, by decide⟩ :=
  accepted_of_selected 13 305294 ⟨589842, by decide⟩ ⟨13, 2, 0, 589842, 305294, 1277, 16384⟩
    (by decide) selected_cut_23294

theorem selected_cut_23295 : selected 8 ⟨589849, by decide⟩
    (prefixPartial 13 305295) = some ⟨13, 2, 0, 589849, 305295, 777, 16384⟩ := by
  decide +kernel

theorem context_13_305295_589849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305295 ⟨589849, by decide⟩ :=
  accepted_of_selected 13 305295 ⟨589849, by decide⟩ ⟨13, 2, 0, 589849, 305295, 777, 16384⟩
    (by decide) selected_cut_23295

theorem unmarked_context_12_76323_589850 : frontier 9 ⟨589850, by decide⟩
    (prefixCache 12 76323) (prefixPartial 12 76323) = false := by
  decide +kernel

theorem node_context_12_76323_589850 : EJMOriginalGlobalDAGData.nodes 9 ⟨589850, by decide⟩ =
    .split (coordinate 12) (![⟨589799, by decide⟩,⟨589823, by decide⟩,⟨589842, by decide⟩,⟨589849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76323_589850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76323 ⟨589850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76323
    ⟨589850, by decide⟩ (by decide) (![⟨589799, by decide⟩,⟨589823, by decide⟩,⟨589842, by decide⟩,⟨589849, by decide⟩]) unmarked_context_12_76323_589850 node_context_12_76323_589850
  intro a
  fin_cases a
  · exact context_13_305292_589799
  · exact context_13_305293_589823
  · exact context_13_305294_589842
  · exact context_13_305295_589849

theorem unmarked_context_11_19080_589851 : frontier 10 ⟨589851, by decide⟩
    (prefixCache 11 19080) (prefixPartial 11 19080) = false := by
  decide +kernel

theorem node_context_11_19080_589851 : EJMOriginalGlobalDAGData.nodes 10 ⟨589851, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨589715, by decide⟩,⟨589775, by decide⟩,⟨589850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19080_589851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19080 ⟨589851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19080
    ⟨589851, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨589715, by decide⟩,⟨589775, by decide⟩,⟨589850, by decide⟩]) unmarked_context_11_19080_589851 node_context_11_19080_589851
  intro a
  fin_cases a
  · exact context_12_76320_435790
  · exact context_12_76321_589715
  · exact context_12_76322_589775
  · exact context_12_76323_589850

theorem selected_cut_23296 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 76324) = some ⟨12, 1, 0, 450498, 76324, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76324_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76324 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 76324 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 76324, 1, 65536⟩
    (by decide) selected_cut_23296

theorem selected_cut_23297 : selected 8 ⟨589871, by decide⟩
    (prefixPartial 13 305300) = some ⟨13, 2, 0, 589871, 305300, 1085, 16384⟩ := by
  decide +kernel

theorem context_13_305300_589871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305300 ⟨589871, by decide⟩ :=
  accepted_of_selected 13 305300 ⟨589871, by decide⟩ ⟨13, 2, 0, 589871, 305300, 1085, 16384⟩
    (by decide) selected_cut_23297

theorem selected_cut_23298 : selected 8 ⟨589891, by decide⟩
    (prefixPartial 13 305301) = some ⟨13, 2, 0, 589891, 305301, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_305301_589891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305301 ⟨589891, by decide⟩ :=
  accepted_of_selected 13 305301 ⟨589891, by decide⟩ ⟨13, 2, 0, 589891, 305301, 1517, 16384⟩
    (by decide) selected_cut_23298

theorem selected_cut_23299 : selected 8 ⟨589909, by decide⟩
    (prefixPartial 13 305302) = some ⟨13, 2, 0, 589909, 305302, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_305302_589909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305302 ⟨589909, by decide⟩ :=
  accepted_of_selected 13 305302 ⟨589909, by decide⟩ ⟨13, 2, 0, 589909, 305302, 1229, 16384⟩
    (by decide) selected_cut_23299

theorem selected_cut_23300 : selected 8 ⟨589916, by decide⟩
    (prefixPartial 13 305303) = some ⟨13, 2, 0, 589916, 305303, 917, 16384⟩ := by
  decide +kernel

theorem context_13_305303_589916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305303 ⟨589916, by decide⟩ :=
  accepted_of_selected 13 305303 ⟨589916, by decide⟩ ⟨13, 2, 0, 589916, 305303, 917, 16384⟩
    (by decide) selected_cut_23300

theorem unmarked_context_12_76325_589917 : frontier 9 ⟨589917, by decide⟩
    (prefixCache 12 76325) (prefixPartial 12 76325) = false := by
  decide +kernel

theorem node_context_12_76325_589917 : EJMOriginalGlobalDAGData.nodes 9 ⟨589917, by decide⟩ =
    .split (coordinate 12) (![⟨589871, by decide⟩,⟨589891, by decide⟩,⟨589909, by decide⟩,⟨589916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76325_589917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76325 ⟨589917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76325
    ⟨589917, by decide⟩ (by decide) (![⟨589871, by decide⟩,⟨589891, by decide⟩,⟨589909, by decide⟩,⟨589916, by decide⟩]) unmarked_context_12_76325_589917 node_context_12_76325_589917
  intro a
  fin_cases a
  · exact context_13_305300_589871
  · exact context_13_305301_589891
  · exact context_13_305302_589909
  · exact context_13_305303_589916

theorem selected_cut_23301 : selected 8 ⟨589935, by decide⟩
    (prefixPartial 13 305304) = some ⟨13, 2, 0, 589935, 305304, 901, 16384⟩ := by
  decide +kernel

theorem context_13_305304_589935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305304 ⟨589935, by decide⟩ :=
  accepted_of_selected 13 305304 ⟨589935, by decide⟩ ⟨13, 2, 0, 589935, 305304, 901, 16384⟩
    (by decide) selected_cut_23301

theorem selected_cut_23302 : selected 8 ⟨589955, by decide⟩
    (prefixPartial 13 305305) = some ⟨13, 2, 0, 589955, 305305, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_305305_589955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305305 ⟨589955, by decide⟩ :=
  accepted_of_selected 13 305305 ⟨589955, by decide⟩ ⟨13, 2, 0, 589955, 305305, 1373, 16384⟩
    (by decide) selected_cut_23302

theorem selected_cut_23303 : selected 8 ⟨589971, by decide⟩
    (prefixPartial 13 305306) = some ⟨13, 2, 0, 589971, 305306, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_305306_589971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305306 ⟨589971, by decide⟩ :=
  accepted_of_selected 13 305306 ⟨589971, by decide⟩ ⟨13, 2, 0, 589971, 305306, 1025, 16384⟩
    (by decide) selected_cut_23303

theorem selected_cut_23304 : selected 8 ⟨589980, by decide⟩
    (prefixPartial 13 305307) = some ⟨13, 2, 0, 589980, 305307, 825, 16384⟩ := by
  decide +kernel

theorem context_13_305307_589980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305307 ⟨589980, by decide⟩ :=
  accepted_of_selected 13 305307 ⟨589980, by decide⟩ ⟨13, 2, 0, 589980, 305307, 825, 16384⟩
    (by decide) selected_cut_23304

theorem unmarked_context_12_76326_589981 : frontier 9 ⟨589981, by decide⟩
    (prefixCache 12 76326) (prefixPartial 12 76326) = false := by
  decide +kernel

theorem node_context_12_76326_589981 : EJMOriginalGlobalDAGData.nodes 9 ⟨589981, by decide⟩ =
    .split (coordinate 12) (![⟨589935, by decide⟩,⟨589955, by decide⟩,⟨589971, by decide⟩,⟨589980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76326_589981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76326 ⟨589981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76326
    ⟨589981, by decide⟩ (by decide) (![⟨589935, by decide⟩,⟨589955, by decide⟩,⟨589971, by decide⟩,⟨589980, by decide⟩]) unmarked_context_12_76326_589981 node_context_12_76326_589981
  intro a
  fin_cases a
  · exact context_13_305304_589935
  · exact context_13_305305_589955
  · exact context_13_305306_589971
  · exact context_13_305307_589980

theorem selected_cut_23305 : selected 8 ⟨590012, by decide⟩
    (prefixPartial 13 305308) = some ⟨13, 2, 0, 590012, 305308, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_305308_590012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305308 ⟨590012, by decide⟩ :=
  accepted_of_selected 13 305308 ⟨590012, by decide⟩ ⟨13, 2, 0, 590012, 305308, 1113, 16384⟩
    (by decide) selected_cut_23305

theorem selected_cut_23306 : selected 8 ⟨590037, by decide⟩
    (prefixPartial 13 305309) = some ⟨13, 2, 0, 590037, 305309, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_305309_590037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305309 ⟨590037, by decide⟩ :=
  accepted_of_selected 13 305309 ⟨590037, by decide⟩ ⟨13, 2, 0, 590037, 305309, 1761, 16384⟩
    (by decide) selected_cut_23306

theorem selected_cut_23307 : selected 8 ⟨590058, by decide⟩
    (prefixPartial 13 305310) = some ⟨13, 2, 0, 590058, 305310, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_305310_590058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305310 ⟨590058, by decide⟩ :=
  accepted_of_selected 13 305310 ⟨590058, by decide⟩ ⟨13, 2, 0, 590058, 305310, 1413, 16384⟩
    (by decide) selected_cut_23307

theorem selected_cut_23308 : selected 8 ⟨590066, by decide⟩
    (prefixPartial 13 305311) = some ⟨13, 2, 0, 590066, 305311, 929, 16384⟩ := by
  decide +kernel

theorem context_13_305311_590066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305311 ⟨590066, by decide⟩ :=
  accepted_of_selected 13 305311 ⟨590066, by decide⟩ ⟨13, 2, 0, 590066, 305311, 929, 16384⟩
    (by decide) selected_cut_23308

theorem unmarked_context_12_76327_590067 : frontier 9 ⟨590067, by decide⟩
    (prefixCache 12 76327) (prefixPartial 12 76327) = false := by
  decide +kernel

theorem node_context_12_76327_590067 : EJMOriginalGlobalDAGData.nodes 9 ⟨590067, by decide⟩ =
    .split (coordinate 12) (![⟨590012, by decide⟩,⟨590037, by decide⟩,⟨590058, by decide⟩,⟨590066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76327_590067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76327 ⟨590067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76327
    ⟨590067, by decide⟩ (by decide) (![⟨590012, by decide⟩,⟨590037, by decide⟩,⟨590058, by decide⟩,⟨590066, by decide⟩]) unmarked_context_12_76327_590067 node_context_12_76327_590067
  intro a
  fin_cases a
  · exact context_13_305308_590012
  · exact context_13_305309_590037
  · exact context_13_305310_590058
  · exact context_13_305311_590066

theorem unmarked_context_11_19081_590068 : frontier 10 ⟨590068, by decide⟩
    (prefixCache 11 19081) (prefixPartial 11 19081) = false := by
  decide +kernel

theorem node_context_11_19081_590068 : EJMOriginalGlobalDAGData.nodes 10 ⟨590068, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨589917, by decide⟩,⟨589981, by decide⟩,⟨590067, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19081_590068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19081 ⟨590068, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19081
    ⟨590068, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨589917, by decide⟩,⟨589981, by decide⟩,⟨590067, by decide⟩]) unmarked_context_11_19081_590068 node_context_11_19081_590068
  intro a
  fin_cases a
  · exact context_12_76324_450498
  · exact context_12_76325_589917
  · exact context_12_76326_589981
  · exact context_12_76327_590067

theorem selected_cut_23309 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 76328) = some ⟨12, 1, 0, 435790, 76328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76328_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76328 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 76328 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 76328, 1, 65536⟩
    (by decide) selected_cut_23309

theorem selected_cut_23310 : selected 9 ⟨590213, by decide⟩
    (prefixPartial 12 76329) = some ⟨12, 2, 0, 590213, 76329, 3649, 65536⟩ := by
  decide +kernel

theorem context_12_76329_590213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76329 ⟨590213, by decide⟩ :=
  accepted_of_selected 12 76329 ⟨590213, by decide⟩ ⟨12, 2, 0, 590213, 76329, 3649, 65536⟩
    (by decide) selected_cut_23310

theorem selected_cut_23311 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 76330) = some ⟨12, 1, 0, 474208, 76330, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76330_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76330 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 76330 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 76330, 1, 65536⟩
    (by decide) selected_cut_23311

theorem selected_cut_23312 : selected 9 ⟨590385, by decide⟩
    (prefixPartial 12 76331) = some ⟨12, 2, 0, 590385, 76331, 3429, 65536⟩ := by
  decide +kernel

theorem context_12_76331_590385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76331 ⟨590385, by decide⟩ :=
  accepted_of_selected 12 76331 ⟨590385, by decide⟩ ⟨12, 2, 0, 590385, 76331, 3429, 65536⟩
    (by decide) selected_cut_23312

theorem unmarked_context_11_19082_590386 : frontier 10 ⟨590386, by decide⟩
    (prefixCache 11 19082) (prefixPartial 11 19082) = false := by
  decide +kernel

theorem node_context_11_19082_590386 : EJMOriginalGlobalDAGData.nodes 10 ⟨590386, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨590213, by decide⟩,⟨474208, by decide⟩,⟨590385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19082_590386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19082 ⟨590386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19082
    ⟨590386, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨590213, by decide⟩,⟨474208, by decide⟩,⟨590385, by decide⟩]) unmarked_context_11_19082_590386 node_context_11_19082_590386
  intro a
  fin_cases a
  · exact context_12_76328_435790
  · exact context_12_76329_590213
  · exact context_12_76330_474208
  · exact context_12_76331_590385

theorem selected_cut_23313 : selected 9 ⟨540189, by decide⟩
    (prefixPartial 12 76332) = some ⟨12, 1, 0, 540189, 76332, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76332_540189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76332 ⟨540189, by decide⟩ :=
  accepted_of_selected 12 76332 ⟨540189, by decide⟩ ⟨12, 1, 0, 540189, 76332, 1, 65536⟩
    (by decide) selected_cut_23313

theorem selected_cut_23314 : selected 8 ⟨590405, by decide⟩
    (prefixPartial 13 305332) = some ⟨13, 2, 0, 590405, 305332, 837, 16384⟩ := by
  decide +kernel

theorem context_13_305332_590405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305332 ⟨590405, by decide⟩ :=
  accepted_of_selected 13 305332 ⟨590405, by decide⟩ ⟨13, 2, 0, 590405, 305332, 837, 16384⟩
    (by decide) selected_cut_23314

theorem selected_cut_23315 : selected 8 ⟨590431, by decide⟩
    (prefixPartial 13 305333) = some ⟨13, 2, 0, 590431, 305333, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_305333_590431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305333 ⟨590431, by decide⟩ :=
  accepted_of_selected 13 305333 ⟨590431, by decide⟩ ⟨13, 2, 0, 590431, 305333, 2013, 16384⟩
    (by decide) selected_cut_23315

theorem selected_cut_23316 : selected 8 ⟨590448, by decide⟩
    (prefixPartial 13 305334) = some ⟨13, 2, 0, 590448, 305334, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_305334_590448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305334 ⟨590448, by decide⟩ :=
  accepted_of_selected 13 305334 ⟨590448, by decide⟩ ⟨13, 2, 0, 590448, 305334, 1389, 16384⟩
    (by decide) selected_cut_23316

theorem selected_cut_23317 : selected 8 ⟨590454, by decide⟩
    (prefixPartial 13 305335) = some ⟨13, 2, 0, 590454, 305335, 857, 16384⟩ := by
  decide +kernel

theorem context_13_305335_590454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305335 ⟨590454, by decide⟩ :=
  accepted_of_selected 13 305335 ⟨590454, by decide⟩ ⟨13, 2, 0, 590454, 305335, 857, 16384⟩
    (by decide) selected_cut_23317

theorem unmarked_context_12_76333_590455 : frontier 9 ⟨590455, by decide⟩
    (prefixCache 12 76333) (prefixPartial 12 76333) = false := by
  decide +kernel

theorem node_context_12_76333_590455 : EJMOriginalGlobalDAGData.nodes 9 ⟨590455, by decide⟩ =
    .split (coordinate 12) (![⟨590405, by decide⟩,⟨590431, by decide⟩,⟨590448, by decide⟩,⟨590454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76333_590455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76333 ⟨590455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76333
    ⟨590455, by decide⟩ (by decide) (![⟨590405, by decide⟩,⟨590431, by decide⟩,⟨590448, by decide⟩,⟨590454, by decide⟩]) unmarked_context_12_76333_590455 node_context_12_76333_590455
  intro a
  fin_cases a
  · exact context_13_305332_590405
  · exact context_13_305333_590431
  · exact context_13_305334_590448
  · exact context_13_305335_590454

theorem selected_cut_23318 : selected 8 ⟨590465, by decide⟩
    (prefixPartial 13 305336) = some ⟨13, 2, 0, 590465, 305336, 569, 16384⟩ := by
  decide +kernel

theorem context_13_305336_590465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305336 ⟨590465, by decide⟩ :=
  accepted_of_selected 13 305336 ⟨590465, by decide⟩ ⟨13, 2, 0, 590465, 305336, 569, 16384⟩
    (by decide) selected_cut_23318

theorem selected_cut_23319 : selected 8 ⟨590488, by decide⟩
    (prefixPartial 13 305337) = some ⟨13, 2, 0, 590488, 305337, 1769, 16384⟩ := by
  decide +kernel

theorem context_13_305337_590488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305337 ⟨590488, by decide⟩ :=
  accepted_of_selected 13 305337 ⟨590488, by decide⟩ ⟨13, 2, 0, 590488, 305337, 1769, 16384⟩
    (by decide) selected_cut_23319

theorem selected_cut_23320 : selected 8 ⟨590503, by decide⟩
    (prefixPartial 13 305338) = some ⟨13, 2, 0, 590503, 305338, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_305338_590503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305338 ⟨590503, by decide⟩ :=
  accepted_of_selected 13 305338 ⟨590503, by decide⟩ ⟨13, 2, 0, 590503, 305338, 1101, 16384⟩
    (by decide) selected_cut_23320

theorem selected_cut_23321 : selected 8 ⟨590510, by decide⟩
    (prefixPartial 13 305339) = some ⟨13, 2, 0, 590510, 305339, 741, 16384⟩ := by
  decide +kernel

theorem context_13_305339_590510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305339 ⟨590510, by decide⟩ :=
  accepted_of_selected 13 305339 ⟨590510, by decide⟩ ⟨13, 2, 0, 590510, 305339, 741, 16384⟩
    (by decide) selected_cut_23321

theorem unmarked_context_12_76334_590511 : frontier 9 ⟨590511, by decide⟩
    (prefixCache 12 76334) (prefixPartial 12 76334) = false := by
  decide +kernel

theorem node_context_12_76334_590511 : EJMOriginalGlobalDAGData.nodes 9 ⟨590511, by decide⟩ =
    .split (coordinate 12) (![⟨590465, by decide⟩,⟨590488, by decide⟩,⟨590503, by decide⟩,⟨590510, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76334_590511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76334 ⟨590511, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76334
    ⟨590511, by decide⟩ (by decide) (![⟨590465, by decide⟩,⟨590488, by decide⟩,⟨590503, by decide⟩,⟨590510, by decide⟩]) unmarked_context_12_76334_590511 node_context_12_76334_590511
  intro a
  fin_cases a
  · exact context_13_305336_590465
  · exact context_13_305337_590488
  · exact context_13_305338_590503
  · exact context_13_305339_590510

theorem selected_cut_23322 : selected 8 ⟨590528, by decide⟩
    (prefixPartial 13 305340) = some ⟨13, 2, 0, 590528, 305340, 737, 16384⟩ := by
  decide +kernel

theorem context_13_305340_590528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305340 ⟨590528, by decide⟩ :=
  accepted_of_selected 13 305340 ⟨590528, by decide⟩ ⟨13, 2, 0, 590528, 305340, 737, 16384⟩
    (by decide) selected_cut_23322

theorem selected_cut_23323 : selected 8 ⟨590556, by decide⟩
    (prefixPartial 13 305341) = some ⟨13, 2, 0, 590556, 305341, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_305341_590556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305341 ⟨590556, by decide⟩ :=
  accepted_of_selected 13 305341 ⟨590556, by decide⟩ ⟨13, 2, 0, 590556, 305341, 2157, 16384⟩
    (by decide) selected_cut_23323

theorem selected_cut_23324 : selected 8 ⟨590574, by decide⟩
    (prefixPartial 13 305342) = some ⟨13, 2, 0, 590574, 305342, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_305342_590574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305342 ⟨590574, by decide⟩ :=
  accepted_of_selected 13 305342 ⟨590574, by decide⟩ ⟨13, 2, 0, 590574, 305342, 1461, 16384⟩
    (by decide) selected_cut_23324

theorem selected_cut_23325 : selected 8 ⟨590582, by decide⟩
    (prefixPartial 13 305343) = some ⟨13, 2, 0, 590582, 305343, 849, 16384⟩ := by
  decide +kernel

theorem context_13_305343_590582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305343 ⟨590582, by decide⟩ :=
  accepted_of_selected 13 305343 ⟨590582, by decide⟩ ⟨13, 2, 0, 590582, 305343, 849, 16384⟩
    (by decide) selected_cut_23325

theorem unmarked_context_12_76335_590583 : frontier 9 ⟨590583, by decide⟩
    (prefixCache 12 76335) (prefixPartial 12 76335) = false := by
  decide +kernel

theorem node_context_12_76335_590583 : EJMOriginalGlobalDAGData.nodes 9 ⟨590583, by decide⟩ =
    .split (coordinate 12) (![⟨590528, by decide⟩,⟨590556, by decide⟩,⟨590574, by decide⟩,⟨590582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76335_590583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76335 ⟨590583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76335
    ⟨590583, by decide⟩ (by decide) (![⟨590528, by decide⟩,⟨590556, by decide⟩,⟨590574, by decide⟩,⟨590582, by decide⟩]) unmarked_context_12_76335_590583 node_context_12_76335_590583
  intro a
  fin_cases a
  · exact context_13_305340_590528
  · exact context_13_305341_590556
  · exact context_13_305342_590574
  · exact context_13_305343_590582

theorem unmarked_context_11_19083_590584 : frontier 10 ⟨590584, by decide⟩
    (prefixCache 11 19083) (prefixPartial 11 19083) = false := by
  decide +kernel

theorem node_context_11_19083_590584 : EJMOriginalGlobalDAGData.nodes 10 ⟨590584, by decide⟩ =
    .split (coordinate 11) (![⟨540189, by decide⟩,⟨590455, by decide⟩,⟨590511, by decide⟩,⟨590583, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19083_590584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19083 ⟨590584, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19083
    ⟨590584, by decide⟩ (by decide) (![⟨540189, by decide⟩,⟨590455, by decide⟩,⟨590511, by decide⟩,⟨590583, by decide⟩]) unmarked_context_11_19083_590584 node_context_11_19083_590584
  intro a
  fin_cases a
  · exact context_12_76332_540189
  · exact context_12_76333_590455
  · exact context_12_76334_590511
  · exact context_12_76335_590583

theorem unmarked_context_10_4770_590585 : frontier 11 ⟨590585, by decide⟩
    (prefixCache 10 4770) (prefixPartial 10 4770) = false := by
  decide +kernel

theorem node_context_10_4770_590585 : EJMOriginalGlobalDAGData.nodes 11 ⟨590585, by decide⟩ =
    .split (coordinate 10) (![⟨589851, by decide⟩,⟨590068, by decide⟩,⟨590386, by decide⟩,⟨590584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4770_590585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4770 ⟨590585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4770
    ⟨590585, by decide⟩ (by decide) (![⟨589851, by decide⟩,⟨590068, by decide⟩,⟨590386, by decide⟩,⟨590584, by decide⟩]) unmarked_context_10_4770_590585 node_context_10_4770_590585
  intro a
  fin_cases a
  · exact context_11_19080_589851
  · exact context_11_19081_590068
  · exact context_11_19082_590386
  · exact context_11_19083_590584

theorem selected_cut_23326 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 76336) = some ⟨12, 1, 0, 445562, 76336, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76336_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76336 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 76336 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 76336, 1, 65536⟩
    (by decide) selected_cut_23326

theorem selected_cut_23327 : selected 8 ⟨590606, by decide⟩
    (prefixPartial 13 305348) = some ⟨13, 2, 0, 590606, 305348, 753, 16384⟩ := by
  decide +kernel

theorem context_13_305348_590606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305348 ⟨590606, by decide⟩ :=
  accepted_of_selected 13 305348 ⟨590606, by decide⟩ ⟨13, 2, 0, 590606, 305348, 753, 16384⟩
    (by decide) selected_cut_23327

theorem selected_cut_23328 : selected 8 ⟨590638, by decide⟩
    (prefixPartial 13 305349) = some ⟨13, 2, 0, 590638, 305349, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_305349_590638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305349 ⟨590638, by decide⟩ :=
  accepted_of_selected 13 305349 ⟨590638, by decide⟩ ⟨13, 2, 0, 590638, 305349, 2293, 16384⟩
    (by decide) selected_cut_23328

theorem selected_cut_23329 : selected 8 ⟨590655, by decide⟩
    (prefixPartial 13 305350) = some ⟨13, 2, 0, 590655, 305350, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_305350_590655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305350 ⟨590655, by decide⟩ :=
  accepted_of_selected 13 305350 ⟨590655, by decide⟩ ⟨13, 2, 0, 590655, 305350, 1313, 16384⟩
    (by decide) selected_cut_23329

theorem selected_cut_23330 : selected 8 ⟨590667, by decide⟩
    (prefixPartial 13 305351) = some ⟨13, 2, 0, 590667, 305351, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_305351_590667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305351 ⟨590667, by decide⟩ :=
  accepted_of_selected 13 305351 ⟨590667, by decide⟩ ⟨13, 2, 0, 590667, 305351, 1033, 16384⟩
    (by decide) selected_cut_23330

theorem unmarked_context_12_76337_590668 : frontier 9 ⟨590668, by decide⟩
    (prefixCache 12 76337) (prefixPartial 12 76337) = false := by
  decide +kernel

theorem node_context_12_76337_590668 : EJMOriginalGlobalDAGData.nodes 9 ⟨590668, by decide⟩ =
    .split (coordinate 12) (![⟨590606, by decide⟩,⟨590638, by decide⟩,⟨590655, by decide⟩,⟨590667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76337_590668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76337 ⟨590668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76337
    ⟨590668, by decide⟩ (by decide) (![⟨590606, by decide⟩,⟨590638, by decide⟩,⟨590655, by decide⟩,⟨590667, by decide⟩]) unmarked_context_12_76337_590668 node_context_12_76337_590668
  intro a
  fin_cases a
  · exact context_13_305348_590606
  · exact context_13_305349_590638
  · exact context_13_305350_590655
  · exact context_13_305351_590667

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
