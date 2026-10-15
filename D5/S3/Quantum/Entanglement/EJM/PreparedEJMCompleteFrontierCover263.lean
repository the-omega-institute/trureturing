/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover262
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_19425_638387 : frontier 10 ⟨638387, by decide⟩
    (prefixCache 11 19425) (prefixPartial 11 19425) = false := by
  decide +kernel

theorem node_context_11_19425_638387 : EJMOriginalGlobalDAGData.nodes 10 ⟨638387, by decide⟩ =
    .split (coordinate 11) (![⟨638276, by decide⟩,⟨638313, by decide⟩,⟨638337, by decide⟩,⟨638386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19425_638387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19425 ⟨638387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19425
    ⟨638387, by decide⟩ (by decide) (![⟨638276, by decide⟩,⟨638313, by decide⟩,⟨638337, by decide⟩,⟨638386, by decide⟩]) unmarked_context_11_19425_638387 node_context_11_19425_638387
  intro a
  fin_cases a
  · exact context_12_77700_638276
  · exact context_12_77701_638313
  · exact context_12_77702_638337
  · exact context_12_77703_638386

theorem selected_cut_25252 : selected 9 ⟨638422, by decide⟩
    (prefixPartial 12 77704) = some ⟨12, 2, 0, 638422, 77704, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_77704_638422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77704 ⟨638422, by decide⟩ :=
  accepted_of_selected 12 77704 ⟨638422, by decide⟩ ⟨12, 2, 0, 638422, 77704, 2457, 65536⟩
    (by decide) selected_cut_25252

theorem selected_cut_25253 : selected 9 ⟨638472, by decide⟩
    (prefixPartial 12 77705) = some ⟨12, 2, 0, 638472, 77705, 2669, 65536⟩ := by
  decide +kernel

theorem context_12_77705_638472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77705 ⟨638472, by decide⟩ :=
  accepted_of_selected 12 77705 ⟨638472, by decide⟩ ⟨12, 2, 0, 638472, 77705, 2669, 65536⟩
    (by decide) selected_cut_25253

theorem selected_cut_25254 : selected 9 ⟨638500, by decide⟩
    (prefixPartial 12 77706) = some ⟨12, 2, 0, 638500, 77706, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_77706_638500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77706 ⟨638500, by decide⟩ :=
  accepted_of_selected 12 77706 ⟨638500, by decide⟩ ⟨12, 2, 0, 638500, 77706, 2297, 65536⟩
    (by decide) selected_cut_25254

theorem selected_cut_25255 : selected 9 ⟨638532, by decide⟩
    (prefixPartial 12 77707) = some ⟨12, 2, 0, 638532, 77707, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_77707_638532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77707 ⟨638532, by decide⟩ :=
  accepted_of_selected 12 77707 ⟨638532, by decide⟩ ⟨12, 2, 0, 638532, 77707, 2481, 65536⟩
    (by decide) selected_cut_25255

theorem unmarked_context_11_19426_638533 : frontier 10 ⟨638533, by decide⟩
    (prefixCache 11 19426) (prefixPartial 11 19426) = false := by
  decide +kernel

theorem node_context_11_19426_638533 : EJMOriginalGlobalDAGData.nodes 10 ⟨638533, by decide⟩ =
    .split (coordinate 11) (![⟨638422, by decide⟩,⟨638472, by decide⟩,⟨638500, by decide⟩,⟨638532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19426_638533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19426 ⟨638533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19426
    ⟨638533, by decide⟩ (by decide) (![⟨638422, by decide⟩,⟨638472, by decide⟩,⟨638500, by decide⟩,⟨638532, by decide⟩]) unmarked_context_11_19426_638533 node_context_11_19426_638533
  intro a
  fin_cases a
  · exact context_12_77704_638422
  · exact context_12_77705_638472
  · exact context_12_77706_638500
  · exact context_12_77707_638532

theorem selected_cut_25256 : selected 9 ⟨638559, by decide⟩
    (prefixPartial 12 77708) = some ⟨12, 2, 0, 638559, 77708, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_77708_638559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77708 ⟨638559, by decide⟩ :=
  accepted_of_selected 12 77708 ⟨638559, by decide⟩ ⟨12, 2, 0, 638559, 77708, 1853, 65536⟩
    (by decide) selected_cut_25256

theorem selected_cut_25257 : selected 9 ⟨638584, by decide⟩
    (prefixPartial 12 77709) = some ⟨12, 2, 0, 638584, 77709, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_77709_638584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77709 ⟨638584, by decide⟩ :=
  accepted_of_selected 12 77709 ⟨638584, by decide⟩ ⟨12, 2, 0, 638584, 77709, 2045, 65536⟩
    (by decide) selected_cut_25257

theorem selected_cut_25258 : selected 9 ⟨638611, by decide⟩
    (prefixPartial 12 77710) = some ⟨12, 2, 0, 638611, 77710, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_77710_638611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77710 ⟨638611, by decide⟩ :=
  accepted_of_selected 12 77710 ⟨638611, by decide⟩ ⟨12, 2, 0, 638611, 77710, 1821, 65536⟩
    (by decide) selected_cut_25258

theorem selected_cut_25259 : selected 9 ⟨638612, by decide⟩
    (prefixPartial 12 77711) = some ⟨12, 1, 0, 638612, 77711, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77711_638612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77711 ⟨638612, by decide⟩ :=
  accepted_of_selected 12 77711 ⟨638612, by decide⟩ ⟨12, 1, 0, 638612, 77711, 1, 65536⟩
    (by decide) selected_cut_25259

theorem unmarked_context_11_19427_638613 : frontier 10 ⟨638613, by decide⟩
    (prefixCache 11 19427) (prefixPartial 11 19427) = false := by
  decide +kernel

theorem node_context_11_19427_638613 : EJMOriginalGlobalDAGData.nodes 10 ⟨638613, by decide⟩ =
    .split (coordinate 11) (![⟨638559, by decide⟩,⟨638584, by decide⟩,⟨638611, by decide⟩,⟨638612, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19427_638613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19427 ⟨638613, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19427
    ⟨638613, by decide⟩ (by decide) (![⟨638559, by decide⟩,⟨638584, by decide⟩,⟨638611, by decide⟩,⟨638612, by decide⟩]) unmarked_context_11_19427_638613 node_context_11_19427_638613
  intro a
  fin_cases a
  · exact context_12_77708_638559
  · exact context_12_77709_638584
  · exact context_12_77710_638611
  · exact context_12_77711_638612

theorem unmarked_context_10_4856_638614 : frontier 11 ⟨638614, by decide⟩
    (prefixCache 10 4856) (prefixPartial 10 4856) = false := by
  decide +kernel

theorem node_context_10_4856_638614 : EJMOriginalGlobalDAGData.nodes 11 ⟨638614, by decide⟩ =
    .split (coordinate 10) (![⟨638245, by decide⟩,⟨638387, by decide⟩,⟨638533, by decide⟩,⟨638613, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4856_638614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4856 ⟨638614, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4856
    ⟨638614, by decide⟩ (by decide) (![⟨638245, by decide⟩,⟨638387, by decide⟩,⟨638533, by decide⟩,⟨638613, by decide⟩]) unmarked_context_10_4856_638614 node_context_10_4856_638614
  intro a
  fin_cases a
  · exact context_11_19424_638245
  · exact context_11_19425_638387
  · exact context_11_19426_638533
  · exact context_11_19427_638613

theorem selected_cut_25260 : selected 9 ⟨638650, by decide⟩
    (prefixPartial 12 77712) = some ⟨12, 2, 0, 638650, 77712, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_77712_638650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77712 ⟨638650, by decide⟩ :=
  accepted_of_selected 12 77712 ⟨638650, by decide⟩ ⟨12, 2, 0, 638650, 77712, 2293, 65536⟩
    (by decide) selected_cut_25260

theorem selected_cut_25261 : selected 9 ⟨638694, by decide⟩
    (prefixPartial 12 77713) = some ⟨12, 2, 0, 638694, 77713, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_77713_638694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77713 ⟨638694, by decide⟩ :=
  accepted_of_selected 12 77713 ⟨638694, by decide⟩ ⟨12, 2, 0, 638694, 77713, 2437, 65536⟩
    (by decide) selected_cut_25261

theorem selected_cut_25262 : selected 9 ⟨638729, by decide⟩
    (prefixPartial 12 77714) = some ⟨12, 2, 0, 638729, 77714, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_77714_638729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77714 ⟨638729, by decide⟩ :=
  accepted_of_selected 12 77714 ⟨638729, by decide⟩ ⟨12, 2, 0, 638729, 77714, 2325, 65536⟩
    (by decide) selected_cut_25262

theorem selected_cut_25263 : selected 9 ⟨638751, by decide⟩
    (prefixPartial 12 77715) = some ⟨12, 2, 0, 638751, 77715, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_77715_638751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77715 ⟨638751, by decide⟩ :=
  accepted_of_selected 12 77715 ⟨638751, by decide⟩ ⟨12, 2, 0, 638751, 77715, 2273, 65536⟩
    (by decide) selected_cut_25263

theorem unmarked_context_11_19428_638752 : frontier 10 ⟨638752, by decide⟩
    (prefixCache 11 19428) (prefixPartial 11 19428) = false := by
  decide +kernel

theorem node_context_11_19428_638752 : EJMOriginalGlobalDAGData.nodes 10 ⟨638752, by decide⟩ =
    .split (coordinate 11) (![⟨638650, by decide⟩,⟨638694, by decide⟩,⟨638729, by decide⟩,⟨638751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19428_638752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19428 ⟨638752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19428
    ⟨638752, by decide⟩ (by decide) (![⟨638650, by decide⟩,⟨638694, by decide⟩,⟨638729, by decide⟩,⟨638751, by decide⟩]) unmarked_context_11_19428_638752 node_context_11_19428_638752
  intro a
  fin_cases a
  · exact context_12_77712_638650
  · exact context_12_77713_638694
  · exact context_12_77714_638729
  · exact context_12_77715_638751

theorem selected_cut_25264 : selected 9 ⟨638781, by decide⟩
    (prefixPartial 12 77716) = some ⟨12, 2, 0, 638781, 77716, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_77716_638781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77716 ⟨638781, by decide⟩ :=
  accepted_of_selected 12 77716 ⟨638781, by decide⟩ ⟨12, 2, 0, 638781, 77716, 2297, 65536⟩
    (by decide) selected_cut_25264

theorem selected_cut_25265 : selected 9 ⟨638809, by decide⟩
    (prefixPartial 12 77717) = some ⟨12, 2, 0, 638809, 77717, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_77717_638809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77717 ⟨638809, by decide⟩ :=
  accepted_of_selected 12 77717 ⟨638809, by decide⟩ ⟨12, 2, 0, 638809, 77717, 2193, 65536⟩
    (by decide) selected_cut_25265

theorem selected_cut_25266 : selected 9 ⟨638838, by decide⟩
    (prefixPartial 12 77718) = some ⟨12, 2, 0, 638838, 77718, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_77718_638838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77718 ⟨638838, by decide⟩ :=
  accepted_of_selected 12 77718 ⟨638838, by decide⟩ ⟨12, 2, 0, 638838, 77718, 2249, 65536⟩
    (by decide) selected_cut_25266

theorem selected_cut_25267 : selected 9 ⟨638884, by decide⟩
    (prefixPartial 12 77719) = some ⟨12, 2, 0, 638884, 77719, 2325, 65536⟩ := by
  decide +kernel

theorem context_12_77719_638884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77719 ⟨638884, by decide⟩ :=
  accepted_of_selected 12 77719 ⟨638884, by decide⟩ ⟨12, 2, 0, 638884, 77719, 2325, 65536⟩
    (by decide) selected_cut_25267

theorem unmarked_context_11_19429_638885 : frontier 10 ⟨638885, by decide⟩
    (prefixCache 11 19429) (prefixPartial 11 19429) = false := by
  decide +kernel

theorem node_context_11_19429_638885 : EJMOriginalGlobalDAGData.nodes 10 ⟨638885, by decide⟩ =
    .split (coordinate 11) (![⟨638781, by decide⟩,⟨638809, by decide⟩,⟨638838, by decide⟩,⟨638884, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19429_638885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19429 ⟨638885, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19429
    ⟨638885, by decide⟩ (by decide) (![⟨638781, by decide⟩,⟨638809, by decide⟩,⟨638838, by decide⟩,⟨638884, by decide⟩]) unmarked_context_11_19429_638885 node_context_11_19429_638885
  intro a
  fin_cases a
  · exact context_12_77716_638781
  · exact context_12_77717_638809
  · exact context_12_77718_638838
  · exact context_12_77719_638884

theorem selected_cut_25268 : selected 9 ⟨638930, by decide⟩
    (prefixPartial 12 77720) = some ⟨12, 2, 0, 638930, 77720, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_77720_638930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77720 ⟨638930, by decide⟩ :=
  accepted_of_selected 12 77720 ⟨638930, by decide⟩ ⟨12, 2, 0, 638930, 77720, 2297, 65536⟩
    (by decide) selected_cut_25268

theorem selected_cut_25269 : selected 9 ⟨638993, by decide⟩
    (prefixPartial 12 77721) = some ⟨12, 2, 0, 638993, 77721, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_77721_638993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77721 ⟨638993, by decide⟩ :=
  accepted_of_selected 12 77721 ⟨638993, by decide⟩ ⟨12, 2, 0, 638993, 77721, 2433, 65536⟩
    (by decide) selected_cut_25269

theorem selected_cut_25270 : selected 9 ⟨639026, by decide⟩
    (prefixPartial 12 77722) = some ⟨12, 2, 0, 639026, 77722, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_77722_639026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77722 ⟨639026, by decide⟩ :=
  accepted_of_selected 12 77722 ⟨639026, by decide⟩ ⟨12, 2, 0, 639026, 77722, 2169, 65536⟩
    (by decide) selected_cut_25270

theorem selected_cut_25271 : selected 9 ⟨639062, by decide⟩
    (prefixPartial 12 77723) = some ⟨12, 2, 0, 639062, 77723, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_77723_639062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77723 ⟨639062, by decide⟩ :=
  accepted_of_selected 12 77723 ⟨639062, by decide⟩ ⟨12, 2, 0, 639062, 77723, 2113, 65536⟩
    (by decide) selected_cut_25271

theorem unmarked_context_11_19430_639063 : frontier 10 ⟨639063, by decide⟩
    (prefixCache 11 19430) (prefixPartial 11 19430) = false := by
  decide +kernel

theorem node_context_11_19430_639063 : EJMOriginalGlobalDAGData.nodes 10 ⟨639063, by decide⟩ =
    .split (coordinate 11) (![⟨638930, by decide⟩,⟨638993, by decide⟩,⟨639026, by decide⟩,⟨639062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19430_639063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19430 ⟨639063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19430
    ⟨639063, by decide⟩ (by decide) (![⟨638930, by decide⟩,⟨638993, by decide⟩,⟨639026, by decide⟩,⟨639062, by decide⟩]) unmarked_context_11_19430_639063 node_context_11_19430_639063
  intro a
  fin_cases a
  · exact context_12_77720_638930
  · exact context_12_77721_638993
  · exact context_12_77722_639026
  · exact context_12_77723_639062

theorem selected_cut_25272 : selected 9 ⟨639082, by decide⟩
    (prefixPartial 12 77724) = some ⟨12, 2, 0, 639082, 77724, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_77724_639082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77724 ⟨639082, by decide⟩ :=
  accepted_of_selected 12 77724 ⟨639082, by decide⟩ ⟨12, 2, 0, 639082, 77724, 1681, 65536⟩
    (by decide) selected_cut_25272

theorem selected_cut_25273 : selected 9 ⟨639102, by decide⟩
    (prefixPartial 12 77725) = some ⟨12, 2, 0, 639102, 77725, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_77725_639102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77725 ⟨639102, by decide⟩ :=
  accepted_of_selected 12 77725 ⟨639102, by decide⟩ ⟨12, 2, 0, 639102, 77725, 1825, 65536⟩
    (by decide) selected_cut_25273

theorem selected_cut_25274 : selected 9 ⟨639121, by decide⟩
    (prefixPartial 12 77726) = some ⟨12, 2, 0, 639121, 77726, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_77726_639121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77726 ⟨639121, by decide⟩ :=
  accepted_of_selected 12 77726 ⟨639121, by decide⟩ ⟨12, 2, 0, 639121, 77726, 1745, 65536⟩
    (by decide) selected_cut_25274

theorem selected_cut_25275 : selected 9 ⟨639193, by decide⟩
    (prefixPartial 12 77727) = some ⟨12, 2, 0, 639193, 77727, 713, 65536⟩ := by
  decide +kernel

theorem context_12_77727_639193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77727 ⟨639193, by decide⟩ :=
  accepted_of_selected 12 77727 ⟨639193, by decide⟩ ⟨12, 2, 0, 639193, 77727, 713, 65536⟩
    (by decide) selected_cut_25275

theorem unmarked_context_11_19431_639194 : frontier 10 ⟨639194, by decide⟩
    (prefixCache 11 19431) (prefixPartial 11 19431) = false := by
  decide +kernel

theorem node_context_11_19431_639194 : EJMOriginalGlobalDAGData.nodes 10 ⟨639194, by decide⟩ =
    .split (coordinate 11) (![⟨639082, by decide⟩,⟨639102, by decide⟩,⟨639121, by decide⟩,⟨639193, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19431_639194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19431 ⟨639194, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19431
    ⟨639194, by decide⟩ (by decide) (![⟨639082, by decide⟩,⟨639102, by decide⟩,⟨639121, by decide⟩,⟨639193, by decide⟩]) unmarked_context_11_19431_639194 node_context_11_19431_639194
  intro a
  fin_cases a
  · exact context_12_77724_639082
  · exact context_12_77725_639102
  · exact context_12_77726_639121
  · exact context_12_77727_639193

theorem unmarked_context_10_4857_639195 : frontier 11 ⟨639195, by decide⟩
    (prefixCache 10 4857) (prefixPartial 10 4857) = false := by
  decide +kernel

theorem node_context_10_4857_639195 : EJMOriginalGlobalDAGData.nodes 11 ⟨639195, by decide⟩ =
    .split (coordinate 10) (![⟨638752, by decide⟩,⟨638885, by decide⟩,⟨639063, by decide⟩,⟨639194, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4857_639195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4857 ⟨639195, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4857
    ⟨639195, by decide⟩ (by decide) (![⟨638752, by decide⟩,⟨638885, by decide⟩,⟨639063, by decide⟩,⟨639194, by decide⟩]) unmarked_context_10_4857_639195 node_context_10_4857_639195
  intro a
  fin_cases a
  · exact context_11_19428_638752
  · exact context_11_19429_638885
  · exact context_11_19430_639063
  · exact context_11_19431_639194

theorem selected_cut_25276 : selected 9 ⟨639214, by decide⟩
    (prefixPartial 12 77728) = some ⟨12, 2, 0, 639214, 77728, 1481, 65536⟩ := by
  decide +kernel

theorem context_12_77728_639214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77728 ⟨639214, by decide⟩ :=
  accepted_of_selected 12 77728 ⟨639214, by decide⟩ ⟨12, 2, 0, 639214, 77728, 1481, 65536⟩
    (by decide) selected_cut_25276

theorem selected_cut_25277 : selected 9 ⟨639240, by decide⟩
    (prefixPartial 12 77729) = some ⟨12, 2, 0, 639240, 77729, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_77729_639240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77729 ⟨639240, by decide⟩ :=
  accepted_of_selected 12 77729 ⟨639240, by decide⟩ ⟨12, 2, 0, 639240, 77729, 1509, 65536⟩
    (by decide) selected_cut_25277

theorem selected_cut_25278 : selected 9 ⟨639268, by decide⟩
    (prefixPartial 12 77730) = some ⟨12, 2, 0, 639268, 77730, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_77730_639268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77730 ⟨639268, by decide⟩ :=
  accepted_of_selected 12 77730 ⟨639268, by decide⟩ ⟨12, 2, 0, 639268, 77730, 1533, 65536⟩
    (by decide) selected_cut_25278

theorem selected_cut_25279 : selected 9 ⟨639288, by decide⟩
    (prefixPartial 12 77731) = some ⟨12, 2, 0, 639288, 77731, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_77731_639288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77731 ⟨639288, by decide⟩ :=
  accepted_of_selected 12 77731 ⟨639288, by decide⟩ ⟨12, 2, 0, 639288, 77731, 1589, 65536⟩
    (by decide) selected_cut_25279

theorem unmarked_context_11_19432_639289 : frontier 10 ⟨639289, by decide⟩
    (prefixCache 11 19432) (prefixPartial 11 19432) = false := by
  decide +kernel

theorem node_context_11_19432_639289 : EJMOriginalGlobalDAGData.nodes 10 ⟨639289, by decide⟩ =
    .split (coordinate 11) (![⟨639214, by decide⟩,⟨639240, by decide⟩,⟨639268, by decide⟩,⟨639288, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19432_639289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19432 ⟨639289, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19432
    ⟨639289, by decide⟩ (by decide) (![⟨639214, by decide⟩,⟨639240, by decide⟩,⟨639268, by decide⟩,⟨639288, by decide⟩]) unmarked_context_11_19432_639289 node_context_11_19432_639289
  intro a
  fin_cases a
  · exact context_12_77728_639214
  · exact context_12_77729_639240
  · exact context_12_77730_639268
  · exact context_12_77731_639288

theorem selected_cut_25280 : selected 9 ⟨639306, by decide⟩
    (prefixPartial 12 77732) = some ⟨12, 2, 0, 639306, 77732, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_77732_639306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77732 ⟨639306, by decide⟩ :=
  accepted_of_selected 12 77732 ⟨639306, by decide⟩ ⟨12, 2, 0, 639306, 77732, 1633, 65536⟩
    (by decide) selected_cut_25280

theorem selected_cut_25281 : selected 9 ⟨639331, by decide⟩
    (prefixPartial 12 77733) = some ⟨12, 2, 0, 639331, 77733, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_77733_639331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77733 ⟨639331, by decide⟩ :=
  accepted_of_selected 12 77733 ⟨639331, by decide⟩ ⟨12, 2, 0, 639331, 77733, 1549, 65536⟩
    (by decide) selected_cut_25281

theorem selected_cut_25282 : selected 9 ⟨639357, by decide⟩
    (prefixPartial 12 77734) = some ⟨12, 2, 0, 639357, 77734, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_77734_639357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77734 ⟨639357, by decide⟩ :=
  accepted_of_selected 12 77734 ⟨639357, by decide⟩ ⟨12, 2, 0, 639357, 77734, 1669, 65536⟩
    (by decide) selected_cut_25282

theorem selected_cut_25283 : selected 9 ⟨639381, by decide⟩
    (prefixPartial 12 77735) = some ⟨12, 2, 0, 639381, 77735, 1685, 65536⟩ := by
  decide +kernel

theorem context_12_77735_639381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77735 ⟨639381, by decide⟩ :=
  accepted_of_selected 12 77735 ⟨639381, by decide⟩ ⟨12, 2, 0, 639381, 77735, 1685, 65536⟩
    (by decide) selected_cut_25283

theorem unmarked_context_11_19433_639382 : frontier 10 ⟨639382, by decide⟩
    (prefixCache 11 19433) (prefixPartial 11 19433) = false := by
  decide +kernel

theorem node_context_11_19433_639382 : EJMOriginalGlobalDAGData.nodes 10 ⟨639382, by decide⟩ =
    .split (coordinate 11) (![⟨639306, by decide⟩,⟨639331, by decide⟩,⟨639357, by decide⟩,⟨639381, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19433_639382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19433 ⟨639382, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19433
    ⟨639382, by decide⟩ (by decide) (![⟨639306, by decide⟩,⟨639331, by decide⟩,⟨639357, by decide⟩,⟨639381, by decide⟩]) unmarked_context_11_19433_639382 node_context_11_19433_639382
  intro a
  fin_cases a
  · exact context_12_77732_639306
  · exact context_12_77733_639331
  · exact context_12_77734_639357
  · exact context_12_77735_639381

theorem selected_cut_25284 : selected 9 ⟨639401, by decide⟩
    (prefixPartial 12 77736) = some ⟨12, 2, 0, 639401, 77736, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_77736_639401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77736 ⟨639401, by decide⟩ :=
  accepted_of_selected 12 77736 ⟨639401, by decide⟩ ⟨12, 2, 0, 639401, 77736, 1493, 65536⟩
    (by decide) selected_cut_25284

theorem selected_cut_25285 : selected 9 ⟨639425, by decide⟩
    (prefixPartial 12 77737) = some ⟨12, 2, 0, 639425, 77737, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_77737_639425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77737 ⟨639425, by decide⟩ :=
  accepted_of_selected 12 77737 ⟨639425, by decide⟩ ⟨12, 2, 0, 639425, 77737, 1509, 65536⟩
    (by decide) selected_cut_25285

theorem selected_cut_25286 : selected 9 ⟨639445, by decide⟩
    (prefixPartial 12 77738) = some ⟨12, 2, 0, 639445, 77738, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_77738_639445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77738 ⟨639445, by decide⟩ :=
  accepted_of_selected 12 77738 ⟨639445, by decide⟩ ⟨12, 2, 0, 639445, 77738, 1449, 65536⟩
    (by decide) selected_cut_25286

theorem selected_cut_25287 : selected 9 ⟨639474, by decide⟩
    (prefixPartial 12 77739) = some ⟨12, 2, 0, 639474, 77739, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_77739_639474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77739 ⟨639474, by decide⟩ :=
  accepted_of_selected 12 77739 ⟨639474, by decide⟩ ⟨12, 2, 0, 639474, 77739, 1477, 65536⟩
    (by decide) selected_cut_25287

theorem unmarked_context_11_19434_639475 : frontier 10 ⟨639475, by decide⟩
    (prefixCache 11 19434) (prefixPartial 11 19434) = false := by
  decide +kernel

theorem node_context_11_19434_639475 : EJMOriginalGlobalDAGData.nodes 10 ⟨639475, by decide⟩ =
    .split (coordinate 11) (![⟨639401, by decide⟩,⟨639425, by decide⟩,⟨639445, by decide⟩,⟨639474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19434_639475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19434 ⟨639475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19434
    ⟨639475, by decide⟩ (by decide) (![⟨639401, by decide⟩,⟨639425, by decide⟩,⟨639445, by decide⟩,⟨639474, by decide⟩]) unmarked_context_11_19434_639475 node_context_11_19434_639475
  intro a
  fin_cases a
  · exact context_12_77736_639401
  · exact context_12_77737_639425
  · exact context_12_77738_639445
  · exact context_12_77739_639474

theorem selected_cut_25288 : selected 10 ⟨639525, by decide⟩
    (prefixPartial 11 19435) = some ⟨11, 2, 0, 639525, 19435, 3357, 262144⟩ := by
  decide +kernel

theorem context_11_19435_639525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19435 ⟨639525, by decide⟩ :=
  accepted_of_selected 11 19435 ⟨639525, by decide⟩ ⟨11, 2, 0, 639525, 19435, 3357, 262144⟩
    (by decide) selected_cut_25288

theorem unmarked_context_10_4858_639526 : frontier 11 ⟨639526, by decide⟩
    (prefixCache 10 4858) (prefixPartial 10 4858) = false := by
  decide +kernel

theorem node_context_10_4858_639526 : EJMOriginalGlobalDAGData.nodes 11 ⟨639526, by decide⟩ =
    .split (coordinate 10) (![⟨639289, by decide⟩,⟨639382, by decide⟩,⟨639475, by decide⟩,⟨639525, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4858_639526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4858 ⟨639526, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4858
    ⟨639526, by decide⟩ (by decide) (![⟨639289, by decide⟩,⟨639382, by decide⟩,⟨639475, by decide⟩,⟨639525, by decide⟩]) unmarked_context_10_4858_639526 node_context_10_4858_639526
  intro a
  fin_cases a
  · exact context_11_19432_639289
  · exact context_11_19433_639382
  · exact context_11_19434_639475
  · exact context_11_19435_639525

theorem selected_cut_25289 : selected 9 ⟨639542, by decide⟩
    (prefixPartial 12 77744) = some ⟨12, 2, 0, 639542, 77744, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_77744_639542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77744 ⟨639542, by decide⟩ :=
  accepted_of_selected 12 77744 ⟨639542, by decide⟩ ⟨12, 2, 0, 639542, 77744, 1301, 65536⟩
    (by decide) selected_cut_25289

theorem selected_cut_25290 : selected 9 ⟨639557, by decide⟩
    (prefixPartial 12 77745) = some ⟨12, 2, 0, 639557, 77745, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_77745_639557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77745 ⟨639557, by decide⟩ :=
  accepted_of_selected 12 77745 ⟨639557, by decide⟩ ⟨12, 2, 0, 639557, 77745, 1305, 65536⟩
    (by decide) selected_cut_25290

theorem selected_cut_25291 : selected 9 ⟨639578, by decide⟩
    (prefixPartial 12 77746) = some ⟨12, 2, 0, 639578, 77746, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_77746_639578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77746 ⟨639578, by decide⟩ :=
  accepted_of_selected 12 77746 ⟨639578, by decide⟩ ⟨12, 2, 0, 639578, 77746, 1293, 65536⟩
    (by decide) selected_cut_25291

theorem selected_cut_25292 : selected 9 ⟨639590, by decide⟩
    (prefixPartial 12 77747) = some ⟨12, 2, 0, 639590, 77747, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_77747_639590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77747 ⟨639590, by decide⟩ :=
  accepted_of_selected 12 77747 ⟨639590, by decide⟩ ⟨12, 2, 0, 639590, 77747, 1137, 65536⟩
    (by decide) selected_cut_25292

theorem unmarked_context_11_19436_639591 : frontier 10 ⟨639591, by decide⟩
    (prefixCache 11 19436) (prefixPartial 11 19436) = false := by
  decide +kernel

theorem node_context_11_19436_639591 : EJMOriginalGlobalDAGData.nodes 10 ⟨639591, by decide⟩ =
    .split (coordinate 11) (![⟨639542, by decide⟩,⟨639557, by decide⟩,⟨639578, by decide⟩,⟨639590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19436_639591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19436 ⟨639591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19436
    ⟨639591, by decide⟩ (by decide) (![⟨639542, by decide⟩,⟨639557, by decide⟩,⟨639578, by decide⟩,⟨639590, by decide⟩]) unmarked_context_11_19436_639591 node_context_11_19436_639591
  intro a
  fin_cases a
  · exact context_12_77744_639542
  · exact context_12_77745_639557
  · exact context_12_77746_639578
  · exact context_12_77747_639590

theorem selected_cut_25293 : selected 9 ⟨639612, by decide⟩
    (prefixPartial 12 77748) = some ⟨12, 2, 0, 639612, 77748, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_77748_639612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77748 ⟨639612, by decide⟩ :=
  accepted_of_selected 12 77748 ⟨639612, by decide⟩ ⟨12, 2, 0, 639612, 77748, 1233, 65536⟩
    (by decide) selected_cut_25293

theorem selected_cut_25294 : selected 9 ⟨639629, by decide⟩
    (prefixPartial 12 77749) = some ⟨12, 2, 0, 639629, 77749, 1205, 65536⟩ := by
  decide +kernel

theorem context_12_77749_639629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77749 ⟨639629, by decide⟩ :=
  accepted_of_selected 12 77749 ⟨639629, by decide⟩ ⟨12, 2, 0, 639629, 77749, 1205, 65536⟩
    (by decide) selected_cut_25294

theorem selected_cut_25295 : selected 9 ⟨639639, by decide⟩
    (prefixPartial 12 77750) = some ⟨12, 2, 0, 639639, 77750, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_77750_639639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77750 ⟨639639, by decide⟩ :=
  accepted_of_selected 12 77750 ⟨639639, by decide⟩ ⟨12, 2, 0, 639639, 77750, 1217, 65536⟩
    (by decide) selected_cut_25295

theorem selected_cut_25296 : selected 9 ⟨639652, by decide⟩
    (prefixPartial 12 77751) = some ⟨12, 2, 0, 639652, 77751, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_77751_639652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77751 ⟨639652, by decide⟩ :=
  accepted_of_selected 12 77751 ⟨639652, by decide⟩ ⟨12, 2, 0, 639652, 77751, 1101, 65536⟩
    (by decide) selected_cut_25296

theorem unmarked_context_11_19437_639653 : frontier 10 ⟨639653, by decide⟩
    (prefixCache 11 19437) (prefixPartial 11 19437) = false := by
  decide +kernel

theorem node_context_11_19437_639653 : EJMOriginalGlobalDAGData.nodes 10 ⟨639653, by decide⟩ =
    .split (coordinate 11) (![⟨639612, by decide⟩,⟨639629, by decide⟩,⟨639639, by decide⟩,⟨639652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19437_639653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19437 ⟨639653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19437
    ⟨639653, by decide⟩ (by decide) (![⟨639612, by decide⟩,⟨639629, by decide⟩,⟨639639, by decide⟩,⟨639652, by decide⟩]) unmarked_context_11_19437_639653 node_context_11_19437_639653
  intro a
  fin_cases a
  · exact context_12_77748_639612
  · exact context_12_77749_639629
  · exact context_12_77750_639639
  · exact context_12_77751_639652

theorem selected_cut_25297 : selected 9 ⟨639668, by decide⟩
    (prefixPartial 12 77752) = some ⟨12, 2, 0, 639668, 77752, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_77752_639668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77752 ⟨639668, by decide⟩ :=
  accepted_of_selected 12 77752 ⟨639668, by decide⟩ ⟨12, 2, 0, 639668, 77752, 1133, 65536⟩
    (by decide) selected_cut_25297

theorem selected_cut_25298 : selected 9 ⟨639685, by decide⟩
    (prefixPartial 12 77753) = some ⟨12, 2, 0, 639685, 77753, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_77753_639685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77753 ⟨639685, by decide⟩ :=
  accepted_of_selected 12 77753 ⟨639685, by decide⟩ ⟨12, 2, 0, 639685, 77753, 1233, 65536⟩
    (by decide) selected_cut_25298

theorem selected_cut_25299 : selected 9 ⟨639697, by decide⟩
    (prefixPartial 12 77754) = some ⟨12, 2, 0, 639697, 77754, 1101, 65536⟩ := by
  decide +kernel

theorem context_12_77754_639697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77754 ⟨639697, by decide⟩ :=
  accepted_of_selected 12 77754 ⟨639697, by decide⟩ ⟨12, 2, 0, 639697, 77754, 1101, 65536⟩
    (by decide) selected_cut_25299

theorem selected_cut_25300 : selected 9 ⟨639710, by decide⟩
    (prefixPartial 12 77755) = some ⟨12, 2, 0, 639710, 77755, 1021, 65536⟩ := by
  decide +kernel

theorem context_12_77755_639710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77755 ⟨639710, by decide⟩ :=
  accepted_of_selected 12 77755 ⟨639710, by decide⟩ ⟨12, 2, 0, 639710, 77755, 1021, 65536⟩
    (by decide) selected_cut_25300

theorem unmarked_context_11_19438_639711 : frontier 10 ⟨639711, by decide⟩
    (prefixCache 11 19438) (prefixPartial 11 19438) = false := by
  decide +kernel

theorem node_context_11_19438_639711 : EJMOriginalGlobalDAGData.nodes 10 ⟨639711, by decide⟩ =
    .split (coordinate 11) (![⟨639668, by decide⟩,⟨639685, by decide⟩,⟨639697, by decide⟩,⟨639710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19438_639711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19438 ⟨639711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19438
    ⟨639711, by decide⟩ (by decide) (![⟨639668, by decide⟩,⟨639685, by decide⟩,⟨639697, by decide⟩,⟨639710, by decide⟩]) unmarked_context_11_19438_639711 node_context_11_19438_639711
  intro a
  fin_cases a
  · exact context_12_77752_639668
  · exact context_12_77753_639685
  · exact context_12_77754_639697
  · exact context_12_77755_639710

theorem selected_cut_25301 : selected 10 ⟨639724, by decide⟩
    (prefixPartial 11 19439) = some ⟨11, 2, 0, 639724, 19439, 233, 262144⟩ := by
  decide +kernel

theorem context_11_19439_639724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19439 ⟨639724, by decide⟩ :=
  accepted_of_selected 11 19439 ⟨639724, by decide⟩ ⟨11, 2, 0, 639724, 19439, 233, 262144⟩
    (by decide) selected_cut_25301

theorem unmarked_context_10_4859_639725 : frontier 11 ⟨639725, by decide⟩
    (prefixCache 10 4859) (prefixPartial 10 4859) = false := by
  decide +kernel

theorem node_context_10_4859_639725 : EJMOriginalGlobalDAGData.nodes 11 ⟨639725, by decide⟩ =
    .split (coordinate 10) (![⟨639591, by decide⟩,⟨639653, by decide⟩,⟨639711, by decide⟩,⟨639724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4859_639725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4859 ⟨639725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4859
    ⟨639725, by decide⟩ (by decide) (![⟨639591, by decide⟩,⟨639653, by decide⟩,⟨639711, by decide⟩,⟨639724, by decide⟩]) unmarked_context_10_4859_639725 node_context_10_4859_639725
  intro a
  fin_cases a
  · exact context_11_19436_639591
  · exact context_11_19437_639653
  · exact context_11_19438_639711
  · exact context_11_19439_639724

theorem unmarked_context_9_1214_639726 : frontier 12 ⟨639726, by decide⟩
    (prefixCache 9 1214) (prefixPartial 9 1214) = false := by
  decide +kernel

theorem node_context_9_1214_639726 : EJMOriginalGlobalDAGData.nodes 12 ⟨639726, by decide⟩ =
    .split (coordinate 9) (![⟨638614, by decide⟩,⟨639195, by decide⟩,⟨639526, by decide⟩,⟨639725, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1214_639726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1214 ⟨639726, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1214
    ⟨639726, by decide⟩ (by decide) (![⟨638614, by decide⟩,⟨639195, by decide⟩,⟨639526, by decide⟩,⟨639725, by decide⟩]) unmarked_context_9_1214_639726 node_context_9_1214_639726
  intro a
  fin_cases a
  · exact context_10_4856_638614
  · exact context_10_4857_639195
  · exact context_10_4858_639526
  · exact context_10_4859_639725

theorem selected_cut_25302 : selected 10 ⟨639752, by decide⟩
    (prefixPartial 11 19440) = some ⟨11, 2, 0, 639752, 19440, 2413, 262144⟩ := by
  decide +kernel

theorem context_11_19440_639752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19440 ⟨639752, by decide⟩ :=
  accepted_of_selected 11 19440 ⟨639752, by decide⟩ ⟨11, 2, 0, 639752, 19440, 2413, 262144⟩
    (by decide) selected_cut_25302

theorem selected_cut_25303 : selected 10 ⟨639781, by decide⟩
    (prefixPartial 11 19441) = some ⟨11, 2, 0, 639781, 19441, 2369, 262144⟩ := by
  decide +kernel

theorem context_11_19441_639781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19441 ⟨639781, by decide⟩ :=
  accepted_of_selected 11 19441 ⟨639781, by decide⟩ ⟨11, 2, 0, 639781, 19441, 2369, 262144⟩
    (by decide) selected_cut_25303

theorem selected_cut_25304 : selected 10 ⟨639812, by decide⟩
    (prefixPartial 11 19442) = some ⟨11, 2, 0, 639812, 19442, 2305, 262144⟩ := by
  decide +kernel

theorem context_11_19442_639812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19442 ⟨639812, by decide⟩ :=
  accepted_of_selected 11 19442 ⟨639812, by decide⟩ ⟨11, 2, 0, 639812, 19442, 2305, 262144⟩
    (by decide) selected_cut_25304

theorem selected_cut_25305 : selected 10 ⟨639837, by decide⟩
    (prefixPartial 11 19443) = some ⟨11, 2, 0, 639837, 19443, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_19443_639837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19443 ⟨639837, by decide⟩ :=
  accepted_of_selected 11 19443 ⟨639837, by decide⟩ ⟨11, 2, 0, 639837, 19443, 1313, 262144⟩
    (by decide) selected_cut_25305

theorem unmarked_context_10_4860_639838 : frontier 11 ⟨639838, by decide⟩
    (prefixCache 10 4860) (prefixPartial 10 4860) = false := by
  decide +kernel

theorem node_context_10_4860_639838 : EJMOriginalGlobalDAGData.nodes 11 ⟨639838, by decide⟩ =
    .split (coordinate 10) (![⟨639752, by decide⟩,⟨639781, by decide⟩,⟨639812, by decide⟩,⟨639837, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4860_639838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4860 ⟨639838, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4860
    ⟨639838, by decide⟩ (by decide) (![⟨639752, by decide⟩,⟨639781, by decide⟩,⟨639812, by decide⟩,⟨639837, by decide⟩]) unmarked_context_10_4860_639838 node_context_10_4860_639838
  intro a
  fin_cases a
  · exact context_11_19440_639752
  · exact context_11_19441_639781
  · exact context_11_19442_639812
  · exact context_11_19443_639837

theorem selected_cut_25306 : selected 10 ⟨639861, by decide⟩
    (prefixPartial 11 19444) = some ⟨11, 2, 0, 639861, 19444, 2205, 262144⟩ := by
  decide +kernel

theorem context_11_19444_639861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19444 ⟨639861, by decide⟩ :=
  accepted_of_selected 11 19444 ⟨639861, by decide⟩ ⟨11, 2, 0, 639861, 19444, 2205, 262144⟩
    (by decide) selected_cut_25306

theorem selected_cut_25307 : selected 10 ⟨639884, by decide⟩
    (prefixPartial 11 19445) = some ⟨11, 2, 0, 639884, 19445, 2077, 262144⟩ := by
  decide +kernel

theorem context_11_19445_639884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19445 ⟨639884, by decide⟩ :=
  accepted_of_selected 11 19445 ⟨639884, by decide⟩ ⟨11, 2, 0, 639884, 19445, 2077, 262144⟩
    (by decide) selected_cut_25307

theorem selected_cut_25308 : selected 10 ⟨639908, by decide⟩
    (prefixPartial 11 19446) = some ⟨11, 2, 0, 639908, 19446, 1913, 262144⟩ := by
  decide +kernel

theorem context_11_19446_639908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19446 ⟨639908, by decide⟩ :=
  accepted_of_selected 11 19446 ⟨639908, by decide⟩ ⟨11, 2, 0, 639908, 19446, 1913, 262144⟩
    (by decide) selected_cut_25308

theorem selected_cut_25309 : selected 10 ⟨639927, by decide⟩
    (prefixPartial 11 19447) = some ⟨11, 2, 0, 639927, 19447, 1125, 262144⟩ := by
  decide +kernel

theorem context_11_19447_639927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19447 ⟨639927, by decide⟩ :=
  accepted_of_selected 11 19447 ⟨639927, by decide⟩ ⟨11, 2, 0, 639927, 19447, 1125, 262144⟩
    (by decide) selected_cut_25309

theorem unmarked_context_10_4861_639928 : frontier 11 ⟨639928, by decide⟩
    (prefixCache 10 4861) (prefixPartial 10 4861) = false := by
  decide +kernel

theorem node_context_10_4861_639928 : EJMOriginalGlobalDAGData.nodes 11 ⟨639928, by decide⟩ =
    .split (coordinate 10) (![⟨639861, by decide⟩,⟨639884, by decide⟩,⟨639908, by decide⟩,⟨639927, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4861_639928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4861 ⟨639928, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4861
    ⟨639928, by decide⟩ (by decide) (![⟨639861, by decide⟩,⟨639884, by decide⟩,⟨639908, by decide⟩,⟨639927, by decide⟩]) unmarked_context_10_4861_639928 node_context_10_4861_639928
  intro a
  fin_cases a
  · exact context_11_19444_639861
  · exact context_11_19445_639884
  · exact context_11_19446_639908
  · exact context_11_19447_639927

theorem selected_cut_25310 : selected 11 ⟨639986, by decide⟩
    (prefixPartial 10 4862) = some ⟨10, 2, 0, 639986, 4862, 3889, 1048576⟩ := by
  decide +kernel

theorem context_10_4862_639986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4862 ⟨639986, by decide⟩ :=
  accepted_of_selected 10 4862 ⟨639986, by decide⟩ ⟨10, 2, 0, 639986, 4862, 3889, 1048576⟩
    (by decide) selected_cut_25310

theorem selected_cut_25311 : selected 11 ⟨640021, by decide⟩
    (prefixPartial 10 4863) = some ⟨10, 2, 0, 640021, 4863, 985, 1048576⟩ := by
  decide +kernel

theorem context_10_4863_640021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4863 ⟨640021, by decide⟩ :=
  accepted_of_selected 10 4863 ⟨640021, by decide⟩ ⟨10, 2, 0, 640021, 4863, 985, 1048576⟩
    (by decide) selected_cut_25311

theorem unmarked_context_9_1215_640022 : frontier 12 ⟨640022, by decide⟩
    (prefixCache 9 1215) (prefixPartial 9 1215) = false := by
  decide +kernel

theorem node_context_9_1215_640022 : EJMOriginalGlobalDAGData.nodes 12 ⟨640022, by decide⟩ =
    .split (coordinate 9) (![⟨639838, by decide⟩,⟨639928, by decide⟩,⟨639986, by decide⟩,⟨640021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1215_640022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1215 ⟨640022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1215
    ⟨640022, by decide⟩ (by decide) (![⟨639838, by decide⟩,⟨639928, by decide⟩,⟨639986, by decide⟩,⟨640021, by decide⟩]) unmarked_context_9_1215_640022 node_context_9_1215_640022
  intro a
  fin_cases a
  · exact context_10_4860_639838
  · exact context_10_4861_639928
  · exact context_10_4862_639986
  · exact context_10_4863_640021

theorem unmarked_context_8_303_640023 : frontier 13 ⟨640023, by decide⟩
    (prefixCache 8 303) (prefixPartial 8 303) = false := by
  decide +kernel

theorem node_context_8_303_640023 : EJMOriginalGlobalDAGData.nodes 13 ⟨640023, by decide⟩ =
    .split (coordinate 8) (![⟨634749, by decide⟩,⟨638112, by decide⟩,⟨639726, by decide⟩,⟨640022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_303_640023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 303 ⟨640023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 303
    ⟨640023, by decide⟩ (by decide) (![⟨634749, by decide⟩,⟨638112, by decide⟩,⟨639726, by decide⟩,⟨640022, by decide⟩]) unmarked_context_8_303_640023 node_context_8_303_640023
  intro a
  fin_cases a
  · exact context_9_1212_634749
  · exact context_9_1213_638112
  · exact context_9_1214_639726
  · exact context_9_1215_640022

theorem unmarked_context_7_75_640024 : frontier 14 ⟨640024, by decide⟩
    (prefixCache 7 75) (prefixPartial 7 75) = false := by
  decide +kernel

theorem node_context_7_75_640024 : EJMOriginalGlobalDAGData.nodes 14 ⟨640024, by decide⟩ =
    .split (coordinate 7) (![⟨612964, by decide⟩,⟨621665, by decide⟩,⟨630624, by decide⟩,⟨640023, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_75_640024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 75 ⟨640024, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 75
    ⟨640024, by decide⟩ (by decide) (![⟨612964, by decide⟩,⟨621665, by decide⟩,⟨630624, by decide⟩,⟨640023, by decide⟩]) unmarked_context_7_75_640024 node_context_7_75_640024
  intro a
  fin_cases a
  · exact context_8_300_612964
  · exact context_8_301_621665
  · exact context_8_302_630624
  · exact context_8_303_640023

theorem unmarked_context_6_18_640025 : frontier 15 ⟨640025, by decide⟩
    (prefixCache 6 18) (prefixPartial 6 18) = false := by
  decide +kernel

theorem node_context_6_18_640025 : EJMOriginalGlobalDAGData.nodes 15 ⟨640025, by decide⟩ =
    .split (coordinate 6) (![⟨537598, by decide⟩,⟨573351, by decide⟩,⟨603601, by decide⟩,⟨640024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_18_640025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 18 ⟨640025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 18
    ⟨640025, by decide⟩ (by decide) (![⟨537598, by decide⟩,⟨573351, by decide⟩,⟨603601, by decide⟩,⟨640024, by decide⟩]) unmarked_context_6_18_640025 node_context_6_18_640025
  intro a
  fin_cases a
  · exact context_7_72_537598
  · exact context_7_73_573351
  · exact context_7_74_603601
  · exact context_7_75_640024

theorem selected_cut_25312 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 19) = some ⟨6, 1, 0, 116314, 19, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_19_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 19 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 19 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 19, 1, 268435456⟩
    (by decide) selected_cut_25312

theorem unmarked_context_5_4_640026 : frontier 16 ⟨640026, by decide⟩
    (prefixCache 5 4) (prefixPartial 5 4) = false := by
  decide +kernel

theorem node_context_5_4_640026 : EJMOriginalGlobalDAGData.nodes 16 ⟨640026, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨517765, by decide⟩,⟨640025, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_4_640026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 4 ⟨640026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 4
    ⟨640026, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨517765, by decide⟩,⟨640025, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_4_640026 node_context_5_4_640026
  intro a
  fin_cases a
  · exact context_6_16_434744
  · exact context_6_17_517765
  · exact context_6_18_640025
  · exact context_6_19_116314

theorem selected_cut_25313 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 20) = some ⟨6, 1, 0, 434744, 20, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_20_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 20 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 20 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 20, 1, 268435456⟩
    (by decide) selected_cut_25313

theorem selected_cut_25314 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 84) = some ⟨7, 1, 0, 116316, 84, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_84_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 84 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 84 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 84, 1, 67108864⟩
    (by decide) selected_cut_25314

theorem selected_cut_25315 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 21760) = some ⟨11, 1, 0, 434745, 21760, 1, 262144⟩ := by
  decide +kernel

theorem context_11_21760_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21760 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 21760 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 21760, 1, 262144⟩
    (by decide) selected_cut_25315

theorem selected_cut_25316 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87044) = some ⟨12, 1, 0, 895, 87044, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87044_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87044 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87044 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87044, 1, 65536⟩
    (by decide) selected_cut_25316

theorem selected_cut_25317 : selected 9 ⟨640114, by decide⟩
    (prefixPartial 12 87045) = some ⟨12, 2, 0, 640114, 87045, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_87045_640114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87045 ⟨640114, by decide⟩ :=
  accepted_of_selected 12 87045 ⟨640114, by decide⟩ ⟨12, 2, 0, 640114, 87045, 2317, 65536⟩
    (by decide) selected_cut_25317

theorem selected_cut_25318 : selected 8 ⟨640176, by decide⟩
    (prefixPartial 13 348184) = some ⟨13, 2, 0, 640176, 348184, 2997, 16384⟩ := by
  decide +kernel

theorem context_13_348184_640176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348184 ⟨640176, by decide⟩ :=
  accepted_of_selected 13 348184 ⟨640176, by decide⟩ ⟨13, 2, 0, 640176, 348184, 2997, 16384⟩
    (by decide) selected_cut_25318

theorem selected_cut_25319 : selected 8 ⟨640219, by decide⟩
    (prefixPartial 13 348185) = some ⟨13, 2, 0, 640219, 348185, 2641, 16384⟩ := by
  decide +kernel

theorem context_13_348185_640219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348185 ⟨640219, by decide⟩ :=
  accepted_of_selected 13 348185 ⟨640219, by decide⟩ ⟨13, 2, 0, 640219, 348185, 2641, 16384⟩
    (by decide) selected_cut_25319

theorem selected_cut_25320 : selected 8 ⟨640242, by decide⟩
    (prefixPartial 13 348186) = some ⟨13, 2, 0, 640242, 348186, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_348186_640242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348186 ⟨640242, by decide⟩ :=
  accepted_of_selected 13 348186 ⟨640242, by decide⟩ ⟨13, 2, 0, 640242, 348186, 1789, 16384⟩
    (by decide) selected_cut_25320

theorem selected_cut_25321 : selected 8 ⟨640247, by decide⟩
    (prefixPartial 13 348187) = some ⟨13, 2, 0, 640247, 348187, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_348187_640247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348187 ⟨640247, by decide⟩ :=
  accepted_of_selected 13 348187 ⟨640247, by decide⟩ ⟨13, 2, 0, 640247, 348187, 1089, 16384⟩
    (by decide) selected_cut_25321

theorem unmarked_context_12_87046_640248 : frontier 9 ⟨640248, by decide⟩
    (prefixCache 12 87046) (prefixPartial 12 87046) = false := by
  decide +kernel

theorem node_context_12_87046_640248 : EJMOriginalGlobalDAGData.nodes 9 ⟨640248, by decide⟩ =
    .split (coordinate 12) (![⟨640176, by decide⟩,⟨640219, by decide⟩,⟨640242, by decide⟩,⟨640247, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87046_640248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87046 ⟨640248, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87046
    ⟨640248, by decide⟩ (by decide) (![⟨640176, by decide⟩,⟨640219, by decide⟩,⟨640242, by decide⟩,⟨640247, by decide⟩]) unmarked_context_12_87046_640248 node_context_12_87046_640248
  intro a
  fin_cases a
  · exact context_13_348184_640176
  · exact context_13_348185_640219
  · exact context_13_348186_640242
  · exact context_13_348187_640247

theorem selected_cut_25322 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 87047) = some ⟨12, 1, 0, 893, 87047, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87047_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87047 ⟨893, by decide⟩ :=
  accepted_of_selected 12 87047 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 87047, 1, 65536⟩
    (by decide) selected_cut_25322

theorem unmarked_context_11_21761_640249 : frontier 10 ⟨640249, by decide⟩
    (prefixCache 11 21761) (prefixPartial 11 21761) = false := by
  decide +kernel

theorem node_context_11_21761_640249 : EJMOriginalGlobalDAGData.nodes 10 ⟨640249, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨640114, by decide⟩,⟨640248, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21761_640249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21761 ⟨640249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21761
    ⟨640249, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨640114, by decide⟩,⟨640248, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_21761_640249 node_context_11_21761_640249
  intro a
  fin_cases a
  · exact context_12_87044_895
  · exact context_12_87045_640114
  · exact context_12_87046_640248
  · exact context_12_87047_893

theorem selected_cut_25323 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87048) = some ⟨12, 1, 0, 895, 87048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87048_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87048 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87048 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87048, 1, 65536⟩
    (by decide) selected_cut_25323

theorem selected_cut_25324 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 87049) = some ⟨12, 1, 0, 895, 87049, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87049_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87049 ⟨895, by decide⟩ :=
  accepted_of_selected 12 87049 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 87049, 1, 65536⟩
    (by decide) selected_cut_25324

theorem selected_cut_25325 : selected 8 ⟨640333, by decide⟩
    (prefixPartial 13 348200) = some ⟨13, 2, 0, 640333, 348200, 2589, 16384⟩ := by
  decide +kernel

theorem context_13_348200_640333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348200 ⟨640333, by decide⟩ :=
  accepted_of_selected 13 348200 ⟨640333, by decide⟩ ⟨13, 2, 0, 640333, 348200, 2589, 16384⟩
    (by decide) selected_cut_25325

theorem selected_cut_25326 : selected 8 ⟨640381, by decide⟩
    (prefixPartial 13 348201) = some ⟨13, 2, 0, 640381, 348201, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_348201_640381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348201 ⟨640381, by decide⟩ :=
  accepted_of_selected 13 348201 ⟨640381, by decide⟩ ⟨13, 2, 0, 640381, 348201, 1717, 16384⟩
    (by decide) selected_cut_25326

theorem selected_cut_25327 : selected 8 ⟨640394, by decide⟩
    (prefixPartial 13 348202) = some ⟨13, 2, 0, 640394, 348202, 565, 16384⟩ := by
  decide +kernel

theorem context_13_348202_640394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348202 ⟨640394, by decide⟩ :=
  accepted_of_selected 13 348202 ⟨640394, by decide⟩ ⟨13, 2, 0, 640394, 348202, 565, 16384⟩
    (by decide) selected_cut_25327

theorem selected_cut_25328 : selected 8 ⟨640396, by decide⟩
    (prefixPartial 13 348203) = some ⟨13, 2, 0, 640396, 348203, 145, 16384⟩ := by
  decide +kernel

theorem context_13_348203_640396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348203 ⟨640396, by decide⟩ :=
  accepted_of_selected 13 348203 ⟨640396, by decide⟩ ⟨13, 2, 0, 640396, 348203, 145, 16384⟩
    (by decide) selected_cut_25328

theorem unmarked_context_12_87050_640397 : frontier 9 ⟨640397, by decide⟩
    (prefixCache 12 87050) (prefixPartial 12 87050) = false := by
  decide +kernel

theorem node_context_12_87050_640397 : EJMOriginalGlobalDAGData.nodes 9 ⟨640397, by decide⟩ =
    .split (coordinate 12) (![⟨640333, by decide⟩,⟨640381, by decide⟩,⟨640394, by decide⟩,⟨640396, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87050_640397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87050 ⟨640397, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87050
    ⟨640397, by decide⟩ (by decide) (![⟨640333, by decide⟩,⟨640381, by decide⟩,⟨640394, by decide⟩,⟨640396, by decide⟩]) unmarked_context_12_87050_640397 node_context_12_87050_640397
  intro a
  fin_cases a
  · exact context_13_348200_640333
  · exact context_13_348201_640381
  · exact context_13_348202_640394
  · exact context_13_348203_640396

theorem selected_cut_25329 : selected 8 ⟨640483, by decide⟩
    (prefixPartial 13 348204) = some ⟨13, 2, 0, 640483, 348204, 2933, 16384⟩ := by
  decide +kernel

theorem context_13_348204_640483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348204 ⟨640483, by decide⟩ :=
  accepted_of_selected 13 348204 ⟨640483, by decide⟩ ⟨13, 2, 0, 640483, 348204, 2933, 16384⟩
    (by decide) selected_cut_25329

theorem selected_cut_25330 : selected 8 ⟨640526, by decide⟩
    (prefixPartial 13 348205) = some ⟨13, 2, 0, 640526, 348205, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_348205_640526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348205 ⟨640526, by decide⟩ :=
  accepted_of_selected 13 348205 ⟨640526, by decide⟩ ⟨13, 2, 0, 640526, 348205, 1785, 16384⟩
    (by decide) selected_cut_25330

theorem selected_cut_25331 : selected 8 ⟨640540, by decide⟩
    (prefixPartial 13 348206) = some ⟨13, 2, 0, 640540, 348206, 601, 16384⟩ := by
  decide +kernel

theorem context_13_348206_640540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348206 ⟨640540, by decide⟩ :=
  accepted_of_selected 13 348206 ⟨640540, by decide⟩ ⟨13, 2, 0, 640540, 348206, 601, 16384⟩
    (by decide) selected_cut_25331

theorem selected_cut_25332 : selected 8 ⟨640543, by decide⟩
    (prefixPartial 13 348207) = some ⟨13, 2, 0, 640543, 348207, 117, 16384⟩ := by
  decide +kernel

theorem context_13_348207_640543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348207 ⟨640543, by decide⟩ :=
  accepted_of_selected 13 348207 ⟨640543, by decide⟩ ⟨13, 2, 0, 640543, 348207, 117, 16384⟩
    (by decide) selected_cut_25332

theorem unmarked_context_12_87051_640544 : frontier 9 ⟨640544, by decide⟩
    (prefixCache 12 87051) (prefixPartial 12 87051) = false := by
  decide +kernel

theorem node_context_12_87051_640544 : EJMOriginalGlobalDAGData.nodes 9 ⟨640544, by decide⟩ =
    .split (coordinate 12) (![⟨640483, by decide⟩,⟨640526, by decide⟩,⟨640540, by decide⟩,⟨640543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87051_640544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87051 ⟨640544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87051
    ⟨640544, by decide⟩ (by decide) (![⟨640483, by decide⟩,⟨640526, by decide⟩,⟨640540, by decide⟩,⟨640543, by decide⟩]) unmarked_context_12_87051_640544 node_context_12_87051_640544
  intro a
  fin_cases a
  · exact context_13_348204_640483
  · exact context_13_348205_640526
  · exact context_13_348206_640540
  · exact context_13_348207_640543

theorem unmarked_context_11_21762_640545 : frontier 10 ⟨640545, by decide⟩
    (prefixCache 11 21762) (prefixPartial 11 21762) = false := by
  decide +kernel

theorem node_context_11_21762_640545 : EJMOriginalGlobalDAGData.nodes 10 ⟨640545, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨640397, by decide⟩,⟨640544, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21762_640545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21762 ⟨640545, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21762
    ⟨640545, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨640397, by decide⟩,⟨640544, by decide⟩]) unmarked_context_11_21762_640545 node_context_11_21762_640545
  intro a
  fin_cases a
  · exact context_12_87048_895
  · exact context_12_87049_895
  · exact context_12_87050_640397
  · exact context_12_87051_640544

theorem selected_cut_25333 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 21763) = some ⟨11, 1, 0, 1736, 21763, 1, 262144⟩ := by
  decide +kernel

theorem context_11_21763_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21763 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 21763 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 21763, 1, 262144⟩
    (by decide) selected_cut_25333

theorem unmarked_context_10_5440_640546 : frontier 11 ⟨640546, by decide⟩
    (prefixCache 10 5440) (prefixPartial 10 5440) = false := by
  decide +kernel

theorem node_context_10_5440_640546 : EJMOriginalGlobalDAGData.nodes 11 ⟨640546, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨640249, by decide⟩,⟨640545, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5440_640546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5440 ⟨640546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5440
    ⟨640546, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨640249, by decide⟩,⟨640545, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_5440_640546 node_context_10_5440_640546
  intro a
  fin_cases a
  · exact context_11_21760_434745
  · exact context_11_21761_640249
  · exact context_11_21762_640545
  · exact context_11_21763_1736

theorem selected_cut_25334 : selected 9 ⟨307381, by decide⟩
    (prefixPartial 12 87056) = some ⟨12, 1, 0, 307381, 87056, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87056_307381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87056 ⟨307381, by decide⟩ :=
  accepted_of_selected 12 87056 ⟨307381, by decide⟩ ⟨12, 1, 0, 307381, 87056, 1, 65536⟩
    (by decide) selected_cut_25334

theorem selected_cut_25335 : selected 9 ⟨640600, by decide⟩
    (prefixPartial 12 87057) = some ⟨12, 2, 0, 640600, 87057, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_87057_640600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87057 ⟨640600, by decide⟩ :=
  accepted_of_selected 12 87057 ⟨640600, by decide⟩ ⟨12, 2, 0, 640600, 87057, 2549, 65536⟩
    (by decide) selected_cut_25335

theorem selected_cut_25336 : selected 8 ⟨640627, by decide⟩
    (prefixPartial 13 348232) = some ⟨13, 2, 0, 640627, 348232, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_348232_640627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348232 ⟨640627, by decide⟩ :=
  accepted_of_selected 13 348232 ⟨640627, by decide⟩ ⟨13, 2, 0, 640627, 348232, 1457, 16384⟩
    (by decide) selected_cut_25336

theorem selected_cut_25337 : selected 8 ⟨640651, by decide⟩
    (prefixPartial 13 348233) = some ⟨13, 2, 0, 640651, 348233, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_348233_640651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348233 ⟨640651, by decide⟩ :=
  accepted_of_selected 13 348233 ⟨640651, by decide⟩ ⟨13, 2, 0, 640651, 348233, 1653, 16384⟩
    (by decide) selected_cut_25337

theorem selected_cut_25338 : selected 8 ⟨640667, by decide⟩
    (prefixPartial 13 348234) = some ⟨13, 2, 0, 640667, 348234, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_348234_640667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348234 ⟨640667, by decide⟩ :=
  accepted_of_selected 13 348234 ⟨640667, by decide⟩ ⟨13, 2, 0, 640667, 348234, 1429, 16384⟩
    (by decide) selected_cut_25338

theorem selected_cut_25339 : selected 8 ⟨640674, by decide⟩
    (prefixPartial 13 348235) = some ⟨13, 2, 0, 640674, 348235, 969, 16384⟩ := by
  decide +kernel

theorem context_13_348235_640674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348235 ⟨640674, by decide⟩ :=
  accepted_of_selected 13 348235 ⟨640674, by decide⟩ ⟨13, 2, 0, 640674, 348235, 969, 16384⟩
    (by decide) selected_cut_25339

theorem unmarked_context_12_87058_640675 : frontier 9 ⟨640675, by decide⟩
    (prefixCache 12 87058) (prefixPartial 12 87058) = false := by
  decide +kernel

theorem node_context_12_87058_640675 : EJMOriginalGlobalDAGData.nodes 9 ⟨640675, by decide⟩ =
    .split (coordinate 12) (![⟨640627, by decide⟩,⟨640651, by decide⟩,⟨640667, by decide⟩,⟨640674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_87058_640675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87058 ⟨640675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 87058
    ⟨640675, by decide⟩ (by decide) (![⟨640627, by decide⟩,⟨640651, by decide⟩,⟨640667, by decide⟩,⟨640674, by decide⟩]) unmarked_context_12_87058_640675 node_context_12_87058_640675
  intro a
  fin_cases a
  · exact context_13_348232_640627
  · exact context_13_348233_640651
  · exact context_13_348234_640667
  · exact context_13_348235_640674

theorem selected_cut_25340 : selected 9 ⟨893, by decide⟩
    (prefixPartial 12 87059) = some ⟨12, 1, 0, 893, 87059, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87059_893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87059 ⟨893, by decide⟩ :=
  accepted_of_selected 12 87059 ⟨893, by decide⟩ ⟨12, 1, 0, 893, 87059, 1, 65536⟩
    (by decide) selected_cut_25340

theorem unmarked_context_11_21764_640676 : frontier 10 ⟨640676, by decide⟩
    (prefixCache 11 21764) (prefixPartial 11 21764) = false := by
  decide +kernel

theorem node_context_11_21764_640676 : EJMOriginalGlobalDAGData.nodes 10 ⟨640676, by decide⟩ =
    .split (coordinate 11) (![⟨307381, by decide⟩,⟨640600, by decide⟩,⟨640675, by decide⟩,⟨893, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_21764_640676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 21764 ⟨640676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 21764
    ⟨640676, by decide⟩ (by decide) (![⟨307381, by decide⟩,⟨640600, by decide⟩,⟨640675, by decide⟩,⟨893, by decide⟩]) unmarked_context_11_21764_640676 node_context_11_21764_640676
  intro a
  fin_cases a
  · exact context_12_87056_307381
  · exact context_12_87057_640600
  · exact context_12_87058_640675
  · exact context_12_87059_893

theorem selected_cut_25341 : selected 9 ⟨640840, by decide⟩
    (prefixPartial 12 87060) = some ⟨12, 2, 0, 640840, 87060, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_87060_640840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87060 ⟨640840, by decide⟩ :=
  accepted_of_selected 12 87060 ⟨640840, by decide⟩ ⟨12, 2, 0, 640840, 87060, 2433, 65536⟩
    (by decide) selected_cut_25341

theorem selected_cut_25342 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 87061) = some ⟨12, 1, 0, 308705, 87061, 1, 65536⟩ := by
  decide +kernel

theorem context_12_87061_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 87061 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 87061 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 87061, 1, 65536⟩
    (by decide) selected_cut_25342

theorem selected_cut_25343 : selected 8 ⟨640899, by decide⟩
    (prefixPartial 13 348248) = some ⟨13, 2, 0, 640899, 348248, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_348248_640899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348248 ⟨640899, by decide⟩ :=
  accepted_of_selected 13 348248 ⟨640899, by decide⟩ ⟨13, 2, 0, 640899, 348248, 2145, 16384⟩
    (by decide) selected_cut_25343

theorem selected_cut_25344 : selected 8 ⟨640974, by decide⟩
    (prefixPartial 13 348249) = some ⟨13, 2, 0, 640974, 348249, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_348249_640974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348249 ⟨640974, by decide⟩ :=
  accepted_of_selected 13 348249 ⟨640974, by decide⟩ ⟨13, 2, 0, 640974, 348249, 2817, 16384⟩
    (by decide) selected_cut_25344

theorem selected_cut_25345 : selected 8 ⟨640996, by decide⟩
    (prefixPartial 13 348250) = some ⟨13, 2, 0, 640996, 348250, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_348250_640996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348250 ⟨640996, by decide⟩ :=
  accepted_of_selected 13 348250 ⟨640996, by decide⟩ ⟨13, 2, 0, 640996, 348250, 1853, 16384⟩
    (by decide) selected_cut_25345

theorem selected_cut_25346 : selected 8 ⟨641008, by decide⟩
    (prefixPartial 13 348251) = some ⟨13, 2, 0, 641008, 348251, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_348251_641008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 348251 ⟨641008, by decide⟩ :=
  accepted_of_selected 13 348251 ⟨641008, by decide⟩ ⟨13, 2, 0, 641008, 348251, 1113, 16384⟩
    (by decide) selected_cut_25346

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
