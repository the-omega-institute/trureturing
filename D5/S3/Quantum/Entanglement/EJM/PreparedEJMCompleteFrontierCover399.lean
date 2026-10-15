/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover398
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38307 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 301194) = some ⟨12, 1, 0, 984676, 301194, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301194_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301194 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 301194 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 301194, 1, 65536⟩
    (by decide) selected_cut_38307

theorem selected_cut_38308 : selected 9 ⟨1031504, by decide⟩
    (prefixPartial 12 301195) = some ⟨12, 2, 0, 1031504, 301195, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_301195_1031504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301195 ⟨1031504, by decide⟩ :=
  accepted_of_selected 12 301195 ⟨1031504, by decide⟩ ⟨12, 2, 0, 1031504, 301195, 1557, 65536⟩
    (by decide) selected_cut_38308

theorem unmarked_context_11_75298_1031505 : frontier 10 ⟨1031505, by decide⟩
    (prefixCache 11 75298) (prefixPartial 11 75298) = false := by
  decide +kernel

theorem node_context_11_75298_1031505 : EJMOriginalGlobalDAGData.nodes 10 ⟨1031505, by decide⟩ =
    .split (coordinate 11) (![⟨1031454, by decide⟩,⟨1031479, by decide⟩,⟨984676, by decide⟩,⟨1031504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75298_1031505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75298 ⟨1031505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75298
    ⟨1031505, by decide⟩ (by decide) (![⟨1031454, by decide⟩,⟨1031479, by decide⟩,⟨984676, by decide⟩,⟨1031504, by decide⟩]) unmarked_context_11_75298_1031505 node_context_11_75298_1031505
  intro a
  fin_cases a
  · exact context_12_301192_1031454
  · exact context_12_301193_1031479
  · exact context_12_301194_984676
  · exact context_12_301195_1031504

theorem selected_cut_38309 : selected 9 ⟨1031530, by decide⟩
    (prefixPartial 12 301196) = some ⟨12, 2, 0, 1031530, 301196, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_301196_1031530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301196 ⟨1031530, by decide⟩ :=
  accepted_of_selected 12 301196 ⟨1031530, by decide⟩ ⟨12, 2, 0, 1031530, 301196, 1385, 65536⟩
    (by decide) selected_cut_38309

theorem selected_cut_38310 : selected 9 ⟨1031554, by decide⟩
    (prefixPartial 12 301197) = some ⟨12, 2, 0, 1031554, 301197, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_301197_1031554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301197 ⟨1031554, by decide⟩ :=
  accepted_of_selected 12 301197 ⟨1031554, by decide⟩ ⟨12, 2, 0, 1031554, 301197, 1477, 65536⟩
    (by decide) selected_cut_38310

theorem selected_cut_38311 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 301198) = some ⟨12, 1, 0, 984676, 301198, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301198_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301198 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 301198 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 301198, 1, 65536⟩
    (by decide) selected_cut_38311

theorem selected_cut_38312 : selected 9 ⟨1031575, by decide⟩
    (prefixPartial 12 301199) = some ⟨12, 2, 0, 1031575, 301199, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_301199_1031575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301199 ⟨1031575, by decide⟩ :=
  accepted_of_selected 12 301199 ⟨1031575, by decide⟩ ⟨12, 2, 0, 1031575, 301199, 1325, 65536⟩
    (by decide) selected_cut_38312

theorem unmarked_context_11_75299_1031576 : frontier 10 ⟨1031576, by decide⟩
    (prefixCache 11 75299) (prefixPartial 11 75299) = false := by
  decide +kernel

theorem node_context_11_75299_1031576 : EJMOriginalGlobalDAGData.nodes 10 ⟨1031576, by decide⟩ =
    .split (coordinate 11) (![⟨1031530, by decide⟩,⟨1031554, by decide⟩,⟨984676, by decide⟩,⟨1031575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75299_1031576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75299 ⟨1031576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75299
    ⟨1031576, by decide⟩ (by decide) (![⟨1031530, by decide⟩,⟨1031554, by decide⟩,⟨984676, by decide⟩,⟨1031575, by decide⟩]) unmarked_context_11_75299_1031576 node_context_11_75299_1031576
  intro a
  fin_cases a
  · exact context_12_301196_1031530
  · exact context_12_301197_1031554
  · exact context_12_301198_984676
  · exact context_12_301199_1031575

theorem unmarked_context_10_18824_1031577 : frontier 11 ⟨1031577, by decide⟩
    (prefixCache 10 18824) (prefixPartial 10 18824) = false := by
  decide +kernel

theorem node_context_10_18824_1031577 : EJMOriginalGlobalDAGData.nodes 11 ⟨1031577, by decide⟩ =
    .split (coordinate 10) (![⟨1031343, by decide⟩,⟨1031431, by decide⟩,⟨1031505, by decide⟩,⟨1031576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18824_1031577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18824 ⟨1031577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18824
    ⟨1031577, by decide⟩ (by decide) (![⟨1031343, by decide⟩,⟨1031431, by decide⟩,⟨1031505, by decide⟩,⟨1031576, by decide⟩]) unmarked_context_10_18824_1031577 node_context_10_18824_1031577
  intro a
  fin_cases a
  · exact context_11_75296_1031343
  · exact context_11_75297_1031431
  · exact context_11_75298_1031505
  · exact context_11_75299_1031576

theorem selected_cut_38313 : selected 10 ⟨1031605, by decide⟩
    (prefixPartial 11 75300) = some ⟨11, 2, 0, 1031605, 75300, 2061, 262144⟩ := by
  decide +kernel

theorem context_11_75300_1031605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75300 ⟨1031605, by decide⟩ :=
  accepted_of_selected 11 75300 ⟨1031605, by decide⟩ ⟨11, 2, 0, 1031605, 75300, 2061, 262144⟩
    (by decide) selected_cut_38313

theorem selected_cut_38314 : selected 10 ⟨1031645, by decide⟩
    (prefixPartial 11 75301) = some ⟨11, 2, 0, 1031645, 75301, 2269, 262144⟩ := by
  decide +kernel

theorem context_11_75301_1031645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75301 ⟨1031645, by decide⟩ :=
  accepted_of_selected 11 75301 ⟨1031645, by decide⟩ ⟨11, 2, 0, 1031645, 75301, 2269, 262144⟩
    (by decide) selected_cut_38314

theorem selected_cut_38315 : selected 10 ⟨1031696, by decide⟩
    (prefixPartial 11 75302) = some ⟨11, 2, 0, 1031696, 75302, 3229, 262144⟩ := by
  decide +kernel

theorem context_11_75302_1031696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75302 ⟨1031696, by decide⟩ :=
  accepted_of_selected 11 75302 ⟨1031696, by decide⟩ ⟨11, 2, 0, 1031696, 75302, 3229, 262144⟩
    (by decide) selected_cut_38315

theorem selected_cut_38316 : selected 10 ⟨1031751, by decide⟩
    (prefixPartial 11 75303) = some ⟨11, 2, 0, 1031751, 75303, 3261, 262144⟩ := by
  decide +kernel

theorem context_11_75303_1031751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75303 ⟨1031751, by decide⟩ :=
  accepted_of_selected 11 75303 ⟨1031751, by decide⟩ ⟨11, 2, 0, 1031751, 75303, 3261, 262144⟩
    (by decide) selected_cut_38316

theorem unmarked_context_10_18825_1031752 : frontier 11 ⟨1031752, by decide⟩
    (prefixCache 10 18825) (prefixPartial 10 18825) = false := by
  decide +kernel

theorem node_context_10_18825_1031752 : EJMOriginalGlobalDAGData.nodes 11 ⟨1031752, by decide⟩ =
    .split (coordinate 10) (![⟨1031605, by decide⟩,⟨1031645, by decide⟩,⟨1031696, by decide⟩,⟨1031751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18825_1031752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18825 ⟨1031752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18825
    ⟨1031752, by decide⟩ (by decide) (![⟨1031605, by decide⟩,⟨1031645, by decide⟩,⟨1031696, by decide⟩,⟨1031751, by decide⟩]) unmarked_context_10_18825_1031752 node_context_10_18825_1031752
  intro a
  fin_cases a
  · exact context_11_75300_1031605
  · exact context_11_75301_1031645
  · exact context_11_75302_1031696
  · exact context_11_75303_1031751

theorem selected_cut_38317 : selected 10 ⟨1031772, by decide⟩
    (prefixPartial 11 75304) = some ⟨11, 2, 0, 1031772, 75304, 1665, 262144⟩ := by
  decide +kernel

theorem context_11_75304_1031772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75304 ⟨1031772, by decide⟩ :=
  accepted_of_selected 11 75304 ⟨1031772, by decide⟩ ⟨11, 2, 0, 1031772, 75304, 1665, 262144⟩
    (by decide) selected_cut_38317

theorem selected_cut_38318 : selected 10 ⟨1031819, by decide⟩
    (prefixPartial 11 75305) = some ⟨11, 2, 0, 1031819, 75305, 2993, 262144⟩ := by
  decide +kernel

theorem context_11_75305_1031819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75305 ⟨1031819, by decide⟩ :=
  accepted_of_selected 11 75305 ⟨1031819, by decide⟩ ⟨11, 2, 0, 1031819, 75305, 2993, 262144⟩
    (by decide) selected_cut_38318

theorem selected_cut_38319 : selected 10 ⟨906566, by decide⟩
    (prefixPartial 11 75306) = some ⟨11, 1, 0, 906566, 75306, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75306_906566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75306 ⟨906566, by decide⟩ :=
  accepted_of_selected 11 75306 ⟨906566, by decide⟩ ⟨11, 1, 0, 906566, 75306, 1, 262144⟩
    (by decide) selected_cut_38319

theorem selected_cut_38320 : selected 10 ⟨1031860, by decide⟩
    (prefixPartial 11 75307) = some ⟨11, 2, 0, 1031860, 75307, 2717, 262144⟩ := by
  decide +kernel

theorem context_11_75307_1031860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75307 ⟨1031860, by decide⟩ :=
  accepted_of_selected 11 75307 ⟨1031860, by decide⟩ ⟨11, 2, 0, 1031860, 75307, 2717, 262144⟩
    (by decide) selected_cut_38320

theorem unmarked_context_10_18826_1031861 : frontier 11 ⟨1031861, by decide⟩
    (prefixCache 10 18826) (prefixPartial 10 18826) = false := by
  decide +kernel

theorem node_context_10_18826_1031861 : EJMOriginalGlobalDAGData.nodes 11 ⟨1031861, by decide⟩ =
    .split (coordinate 10) (![⟨1031772, by decide⟩,⟨1031819, by decide⟩,⟨906566, by decide⟩,⟨1031860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18826_1031861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18826 ⟨1031861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18826
    ⟨1031861, by decide⟩ (by decide) (![⟨1031772, by decide⟩,⟨1031819, by decide⟩,⟨906566, by decide⟩,⟨1031860, by decide⟩]) unmarked_context_10_18826_1031861 node_context_10_18826_1031861
  intro a
  fin_cases a
  · exact context_11_75304_1031772
  · exact context_11_75305_1031819
  · exact context_11_75306_906566
  · exact context_11_75307_1031860

theorem selected_cut_38321 : selected 10 ⟨1031883, by decide⟩
    (prefixPartial 11 75308) = some ⟨11, 2, 0, 1031883, 75308, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_75308_1031883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75308 ⟨1031883, by decide⟩ :=
  accepted_of_selected 11 75308 ⟨1031883, by decide⟩ ⟨11, 2, 0, 1031883, 75308, 1537, 262144⟩
    (by decide) selected_cut_38321

theorem selected_cut_38322 : selected 10 ⟨1031929, by decide⟩
    (prefixPartial 11 75309) = some ⟨11, 2, 0, 1031929, 75309, 2629, 262144⟩ := by
  decide +kernel

theorem context_11_75309_1031929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75309 ⟨1031929, by decide⟩ :=
  accepted_of_selected 11 75309 ⟨1031929, by decide⟩ ⟨11, 2, 0, 1031929, 75309, 2629, 262144⟩
    (by decide) selected_cut_38322

theorem selected_cut_38323 : selected 10 ⟨1031957, by decide⟩
    (prefixPartial 11 75310) = some ⟨11, 2, 0, 1031957, 75310, 2217, 262144⟩ := by
  decide +kernel

theorem context_11_75310_1031957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75310 ⟨1031957, by decide⟩ :=
  accepted_of_selected 11 75310 ⟨1031957, by decide⟩ ⟨11, 2, 0, 1031957, 75310, 2217, 262144⟩
    (by decide) selected_cut_38323

theorem selected_cut_38324 : selected 10 ⟨1031997, by decide⟩
    (prefixPartial 11 75311) = some ⟨11, 2, 0, 1031997, 75311, 2189, 262144⟩ := by
  decide +kernel

theorem context_11_75311_1031997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75311 ⟨1031997, by decide⟩ :=
  accepted_of_selected 11 75311 ⟨1031997, by decide⟩ ⟨11, 2, 0, 1031997, 75311, 2189, 262144⟩
    (by decide) selected_cut_38324

theorem unmarked_context_10_18827_1031998 : frontier 11 ⟨1031998, by decide⟩
    (prefixCache 10 18827) (prefixPartial 10 18827) = false := by
  decide +kernel

theorem node_context_10_18827_1031998 : EJMOriginalGlobalDAGData.nodes 11 ⟨1031998, by decide⟩ =
    .split (coordinate 10) (![⟨1031883, by decide⟩,⟨1031929, by decide⟩,⟨1031957, by decide⟩,⟨1031997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18827_1031998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18827 ⟨1031998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18827
    ⟨1031998, by decide⟩ (by decide) (![⟨1031883, by decide⟩,⟨1031929, by decide⟩,⟨1031957, by decide⟩,⟨1031997, by decide⟩]) unmarked_context_10_18827_1031998 node_context_10_18827_1031998
  intro a
  fin_cases a
  · exact context_11_75308_1031883
  · exact context_11_75309_1031929
  · exact context_11_75310_1031957
  · exact context_11_75311_1031997

theorem unmarked_context_9_4706_1031999 : frontier 12 ⟨1031999, by decide⟩
    (prefixCache 9 4706) (prefixPartial 9 4706) = false := by
  decide +kernel

theorem node_context_9_4706_1031999 : EJMOriginalGlobalDAGData.nodes 12 ⟨1031999, by decide⟩ =
    .split (coordinate 9) (![⟨1031577, by decide⟩,⟨1031752, by decide⟩,⟨1031861, by decide⟩,⟨1031998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4706_1031999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4706 ⟨1031999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4706
    ⟨1031999, by decide⟩ (by decide) (![⟨1031577, by decide⟩,⟨1031752, by decide⟩,⟨1031861, by decide⟩,⟨1031998, by decide⟩]) unmarked_context_9_4706_1031999 node_context_9_4706_1031999
  intro a
  fin_cases a
  · exact context_10_18824_1031577
  · exact context_10_18825_1031752
  · exact context_10_18826_1031861
  · exact context_10_18827_1031998

theorem selected_cut_38325 : selected 10 ⟨1032021, by decide⟩
    (prefixPartial 11 75312) = some ⟨11, 2, 0, 1032021, 75312, 1729, 262144⟩ := by
  decide +kernel

theorem context_11_75312_1032021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75312 ⟨1032021, by decide⟩ :=
  accepted_of_selected 11 75312 ⟨1032021, by decide⟩ ⟨11, 2, 0, 1032021, 75312, 1729, 262144⟩
    (by decide) selected_cut_38325

theorem selected_cut_38326 : selected 10 ⟨1032059, by decide⟩
    (prefixPartial 11 75313) = some ⟨11, 2, 0, 1032059, 75313, 2397, 262144⟩ := by
  decide +kernel

theorem context_11_75313_1032059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75313 ⟨1032059, by decide⟩ :=
  accepted_of_selected 11 75313 ⟨1032059, by decide⟩ ⟨11, 2, 0, 1032059, 75313, 2397, 262144⟩
    (by decide) selected_cut_38326

theorem selected_cut_38327 : selected 10 ⟨1032093, by decide⟩
    (prefixPartial 11 75314) = some ⟨11, 2, 0, 1032093, 75314, 2281, 262144⟩ := by
  decide +kernel

theorem context_11_75314_1032093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75314 ⟨1032093, by decide⟩ :=
  accepted_of_selected 11 75314 ⟨1032093, by decide⟩ ⟨11, 2, 0, 1032093, 75314, 2281, 262144⟩
    (by decide) selected_cut_38327

theorem selected_cut_38328 : selected 10 ⟨1032132, by decide⟩
    (prefixPartial 11 75315) = some ⟨11, 2, 0, 1032132, 75315, 2213, 262144⟩ := by
  decide +kernel

theorem context_11_75315_1032132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75315 ⟨1032132, by decide⟩ :=
  accepted_of_selected 11 75315 ⟨1032132, by decide⟩ ⟨11, 2, 0, 1032132, 75315, 2213, 262144⟩
    (by decide) selected_cut_38328

theorem unmarked_context_10_18828_1032133 : frontier 11 ⟨1032133, by decide⟩
    (prefixCache 10 18828) (prefixPartial 10 18828) = false := by
  decide +kernel

theorem node_context_10_18828_1032133 : EJMOriginalGlobalDAGData.nodes 11 ⟨1032133, by decide⟩ =
    .split (coordinate 10) (![⟨1032021, by decide⟩,⟨1032059, by decide⟩,⟨1032093, by decide⟩,⟨1032132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18828_1032133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18828 ⟨1032133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18828
    ⟨1032133, by decide⟩ (by decide) (![⟨1032021, by decide⟩,⟨1032059, by decide⟩,⟨1032093, by decide⟩,⟨1032132, by decide⟩]) unmarked_context_10_18828_1032133 node_context_10_18828_1032133
  intro a
  fin_cases a
  · exact context_11_75312_1032021
  · exact context_11_75313_1032059
  · exact context_11_75314_1032093
  · exact context_11_75315_1032132

theorem selected_cut_38329 : selected 10 ⟨1032145, by decide⟩
    (prefixPartial 11 75316) = some ⟨11, 2, 0, 1032145, 75316, 1177, 262144⟩ := by
  decide +kernel

theorem context_11_75316_1032145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75316 ⟨1032145, by decide⟩ :=
  accepted_of_selected 11 75316 ⟨1032145, by decide⟩ ⟨11, 2, 0, 1032145, 75316, 1177, 262144⟩
    (by decide) selected_cut_38329

theorem selected_cut_38330 : selected 10 ⟨1032163, by decide⟩
    (prefixPartial 11 75317) = some ⟨11, 2, 0, 1032163, 75317, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_75317_1032163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75317 ⟨1032163, by decide⟩ :=
  accepted_of_selected 11 75317 ⟨1032163, by decide⟩ ⟨11, 2, 0, 1032163, 75317, 1461, 262144⟩
    (by decide) selected_cut_38330

theorem selected_cut_38331 : selected 10 ⟨1032182, by decide⟩
    (prefixPartial 11 75318) = some ⟨11, 2, 0, 1032182, 75318, 1297, 262144⟩ := by
  decide +kernel

theorem context_11_75318_1032182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75318 ⟨1032182, by decide⟩ :=
  accepted_of_selected 11 75318 ⟨1032182, by decide⟩ ⟨11, 2, 0, 1032182, 75318, 1297, 262144⟩
    (by decide) selected_cut_38331

theorem selected_cut_38332 : selected 10 ⟨1032204, by decide⟩
    (prefixPartial 11 75319) = some ⟨11, 2, 0, 1032204, 75319, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_75319_1032204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75319 ⟨1032204, by decide⟩ :=
  accepted_of_selected 11 75319 ⟨1032204, by decide⟩ ⟨11, 2, 0, 1032204, 75319, 1281, 262144⟩
    (by decide) selected_cut_38332

theorem unmarked_context_10_18829_1032205 : frontier 11 ⟨1032205, by decide⟩
    (prefixCache 10 18829) (prefixPartial 10 18829) = false := by
  decide +kernel

theorem node_context_10_18829_1032205 : EJMOriginalGlobalDAGData.nodes 11 ⟨1032205, by decide⟩ =
    .split (coordinate 10) (![⟨1032145, by decide⟩,⟨1032163, by decide⟩,⟨1032182, by decide⟩,⟨1032204, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18829_1032205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18829 ⟨1032205, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18829
    ⟨1032205, by decide⟩ (by decide) (![⟨1032145, by decide⟩,⟨1032163, by decide⟩,⟨1032182, by decide⟩,⟨1032204, by decide⟩]) unmarked_context_10_18829_1032205 node_context_10_18829_1032205
  intro a
  fin_cases a
  · exact context_11_75316_1032145
  · exact context_11_75317_1032163
  · exact context_11_75318_1032182
  · exact context_11_75319_1032204

theorem selected_cut_38333 : selected 11 ⟨1032243, by decide⟩
    (prefixPartial 10 18830) = some ⟨10, 2, 0, 1032243, 18830, 2301, 1048576⟩ := by
  decide +kernel

theorem context_10_18830_1032243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18830 ⟨1032243, by decide⟩ :=
  accepted_of_selected 10 18830 ⟨1032243, by decide⟩ ⟨10, 2, 0, 1032243, 18830, 2301, 1048576⟩
    (by decide) selected_cut_38333

theorem selected_cut_38334 : selected 11 ⟨1032275, by decide⟩
    (prefixPartial 10 18831) = some ⟨10, 2, 0, 1032275, 18831, 1237, 1048576⟩ := by
  decide +kernel

theorem context_10_18831_1032275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18831 ⟨1032275, by decide⟩ :=
  accepted_of_selected 10 18831 ⟨1032275, by decide⟩ ⟨10, 2, 0, 1032275, 18831, 1237, 1048576⟩
    (by decide) selected_cut_38334

theorem unmarked_context_9_4707_1032276 : frontier 12 ⟨1032276, by decide⟩
    (prefixCache 9 4707) (prefixPartial 9 4707) = false := by
  decide +kernel

theorem node_context_9_4707_1032276 : EJMOriginalGlobalDAGData.nodes 12 ⟨1032276, by decide⟩ =
    .split (coordinate 9) (![⟨1032133, by decide⟩,⟨1032205, by decide⟩,⟨1032243, by decide⟩,⟨1032275, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4707_1032276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4707 ⟨1032276, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4707
    ⟨1032276, by decide⟩ (by decide) (![⟨1032133, by decide⟩,⟨1032205, by decide⟩,⟨1032243, by decide⟩,⟨1032275, by decide⟩]) unmarked_context_9_4707_1032276 node_context_9_4707_1032276
  intro a
  fin_cases a
  · exact context_10_18828_1032133
  · exact context_10_18829_1032205
  · exact context_10_18830_1032243
  · exact context_10_18831_1032275

theorem unmarked_context_8_1176_1032277 : frontier 13 ⟨1032277, by decide⟩
    (prefixCache 8 1176) (prefixPartial 8 1176) = false := by
  decide +kernel

theorem node_context_8_1176_1032277 : EJMOriginalGlobalDAGData.nodes 13 ⟨1032277, by decide⟩ =
    .split (coordinate 8) (![⟨1030244, by decide⟩,⟨1031308, by decide⟩,⟨1031999, by decide⟩,⟨1032276, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1176_1032277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1176 ⟨1032277, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1176
    ⟨1032277, by decide⟩ (by decide) (![⟨1030244, by decide⟩,⟨1031308, by decide⟩,⟨1031999, by decide⟩,⟨1032276, by decide⟩]) unmarked_context_8_1176_1032277 node_context_8_1176_1032277
  intro a
  fin_cases a
  · exact context_9_4704_1030244
  · exact context_9_4705_1031308
  · exact context_9_4706_1031999
  · exact context_9_4707_1032276

theorem selected_cut_38335 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 301312) = some ⟨12, 1, 0, 34034, 301312, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301312_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301312 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 301312 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 301312, 1, 65536⟩
    (by decide) selected_cut_38335

theorem selected_cut_38336 : selected 9 ⟨1032336, by decide⟩
    (prefixPartial 12 301313) = some ⟨12, 2, 0, 1032336, 301313, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_301313_1032336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301313 ⟨1032336, by decide⟩ :=
  accepted_of_selected 12 301313 ⟨1032336, by decide⟩ ⟨12, 2, 0, 1032336, 301313, 1969, 65536⟩
    (by decide) selected_cut_38336

theorem selected_cut_38337 : selected 9 ⟨1032393, by decide⟩
    (prefixPartial 12 301314) = some ⟨12, 2, 0, 1032393, 301314, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_301314_1032393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301314 ⟨1032393, by decide⟩ :=
  accepted_of_selected 12 301314 ⟨1032393, by decide⟩ ⟨12, 2, 0, 1032393, 301314, 2725, 65536⟩
    (by decide) selected_cut_38337

theorem selected_cut_38338 : selected 9 ⟨1032440, by decide⟩
    (prefixPartial 12 301315) = some ⟨12, 2, 0, 1032440, 301315, 2993, 65536⟩ := by
  decide +kernel

theorem context_12_301315_1032440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301315 ⟨1032440, by decide⟩ :=
  accepted_of_selected 12 301315 ⟨1032440, by decide⟩ ⟨12, 2, 0, 1032440, 301315, 2993, 65536⟩
    (by decide) selected_cut_38338

theorem unmarked_context_11_75328_1032441 : frontier 10 ⟨1032441, by decide⟩
    (prefixCache 11 75328) (prefixPartial 11 75328) = false := by
  decide +kernel

theorem node_context_11_75328_1032441 : EJMOriginalGlobalDAGData.nodes 10 ⟨1032441, by decide⟩ =
    .split (coordinate 11) (![⟨34034, by decide⟩,⟨1032336, by decide⟩,⟨1032393, by decide⟩,⟨1032440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75328_1032441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75328 ⟨1032441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75328
    ⟨1032441, by decide⟩ (by decide) (![⟨34034, by decide⟩,⟨1032336, by decide⟩,⟨1032393, by decide⟩,⟨1032440, by decide⟩]) unmarked_context_11_75328_1032441 node_context_11_75328_1032441
  intro a
  fin_cases a
  · exact context_12_301312_34034
  · exact context_12_301313_1032336
  · exact context_12_301314_1032393
  · exact context_12_301315_1032440

theorem selected_cut_38339 : selected 9 ⟨1032544, by decide⟩
    (prefixPartial 12 301316) = some ⟨12, 2, 0, 1032544, 301316, 4025, 65536⟩ := by
  decide +kernel

theorem context_12_301316_1032544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301316 ⟨1032544, by decide⟩ :=
  accepted_of_selected 12 301316 ⟨1032544, by decide⟩ ⟨12, 2, 0, 1032544, 301316, 4025, 65536⟩
    (by decide) selected_cut_38339

theorem selected_cut_38340 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 301317) = some ⟨12, 1, 0, 891951, 301317, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301317_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301317 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 301317 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 301317, 1, 65536⟩
    (by decide) selected_cut_38340

theorem selected_cut_38341 : selected 9 ⟨1032612, by decide⟩
    (prefixPartial 12 301318) = some ⟨12, 2, 0, 1032612, 301318, 3461, 65536⟩ := by
  decide +kernel

theorem context_12_301318_1032612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301318 ⟨1032612, by decide⟩ :=
  accepted_of_selected 12 301318 ⟨1032612, by decide⟩ ⟨12, 2, 0, 1032612, 301318, 3461, 65536⟩
    (by decide) selected_cut_38341

theorem selected_cut_38342 : selected 9 ⟨1032686, by decide⟩
    (prefixPartial 12 301319) = some ⟨12, 2, 0, 1032686, 301319, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_301319_1032686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301319 ⟨1032686, by decide⟩ :=
  accepted_of_selected 12 301319 ⟨1032686, by decide⟩ ⟨12, 2, 0, 1032686, 301319, 3653, 65536⟩
    (by decide) selected_cut_38342

theorem unmarked_context_11_75329_1032687 : frontier 10 ⟨1032687, by decide⟩
    (prefixCache 11 75329) (prefixPartial 11 75329) = false := by
  decide +kernel

theorem node_context_11_75329_1032687 : EJMOriginalGlobalDAGData.nodes 10 ⟨1032687, by decide⟩ =
    .split (coordinate 11) (![⟨1032544, by decide⟩,⟨891951, by decide⟩,⟨1032612, by decide⟩,⟨1032686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75329_1032687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75329 ⟨1032687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75329
    ⟨1032687, by decide⟩ (by decide) (![⟨1032544, by decide⟩,⟨891951, by decide⟩,⟨1032612, by decide⟩,⟨1032686, by decide⟩]) unmarked_context_11_75329_1032687 node_context_11_75329_1032687
  intro a
  fin_cases a
  · exact context_12_301316_1032544
  · exact context_12_301317_891951
  · exact context_12_301318_1032612
  · exact context_12_301319_1032686

theorem selected_cut_38343 : selected 9 ⟨1032734, by decide⟩
    (prefixPartial 12 301320) = some ⟨12, 2, 0, 1032734, 301320, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_301320_1032734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301320 ⟨1032734, by decide⟩ :=
  accepted_of_selected 12 301320 ⟨1032734, by decide⟩ ⟨12, 2, 0, 1032734, 301320, 1841, 65536⟩
    (by decide) selected_cut_38343

theorem selected_cut_38344 : selected 9 ⟨1032788, by decide⟩
    (prefixPartial 12 301321) = some ⟨12, 2, 0, 1032788, 301321, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_301321_1032788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301321 ⟨1032788, by decide⟩ :=
  accepted_of_selected 12 301321 ⟨1032788, by decide⟩ ⟨12, 2, 0, 1032788, 301321, 3349, 65536⟩
    (by decide) selected_cut_38344

theorem selected_cut_38345 : selected 9 ⟨1032847, by decide⟩
    (prefixPartial 12 301322) = some ⟨12, 2, 0, 1032847, 301322, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_301322_1032847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301322 ⟨1032847, by decide⟩ :=
  accepted_of_selected 12 301322 ⟨1032847, by decide⟩ ⟨12, 2, 0, 1032847, 301322, 3245, 65536⟩
    (by decide) selected_cut_38345

theorem selected_cut_38346 : selected 9 ⟨1032900, by decide⟩
    (prefixPartial 12 301323) = some ⟨12, 2, 0, 1032900, 301323, 3349, 65536⟩ := by
  decide +kernel

theorem context_12_301323_1032900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301323 ⟨1032900, by decide⟩ :=
  accepted_of_selected 12 301323 ⟨1032900, by decide⟩ ⟨12, 2, 0, 1032900, 301323, 3349, 65536⟩
    (by decide) selected_cut_38346

theorem unmarked_context_11_75330_1032901 : frontier 10 ⟨1032901, by decide⟩
    (prefixCache 11 75330) (prefixPartial 11 75330) = false := by
  decide +kernel

theorem node_context_11_75330_1032901 : EJMOriginalGlobalDAGData.nodes 10 ⟨1032901, by decide⟩ =
    .split (coordinate 11) (![⟨1032734, by decide⟩,⟨1032788, by decide⟩,⟨1032847, by decide⟩,⟨1032900, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75330_1032901 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75330 ⟨1032901, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75330
    ⟨1032901, by decide⟩ (by decide) (![⟨1032734, by decide⟩,⟨1032788, by decide⟩,⟨1032847, by decide⟩,⟨1032900, by decide⟩]) unmarked_context_11_75330_1032901 node_context_11_75330_1032901
  intro a
  fin_cases a
  · exact context_12_301320_1032734
  · exact context_12_301321_1032788
  · exact context_12_301322_1032847
  · exact context_12_301323_1032900

theorem selected_cut_38347 : selected 9 ⟨1032954, by decide⟩
    (prefixPartial 12 301324) = some ⟨12, 2, 0, 1032954, 301324, 3221, 65536⟩ := by
  decide +kernel

theorem context_12_301324_1032954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301324 ⟨1032954, by decide⟩ :=
  accepted_of_selected 12 301324 ⟨1032954, by decide⟩ ⟨12, 2, 0, 1032954, 301324, 3221, 65536⟩
    (by decide) selected_cut_38347

theorem selected_cut_38348 : selected 9 ⟨1033016, by decide⟩
    (prefixPartial 12 301325) = some ⟨12, 2, 0, 1033016, 301325, 3449, 65536⟩ := by
  decide +kernel

theorem context_12_301325_1033016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301325 ⟨1033016, by decide⟩ :=
  accepted_of_selected 12 301325 ⟨1033016, by decide⟩ ⟨12, 2, 0, 1033016, 301325, 3449, 65536⟩
    (by decide) selected_cut_38348

theorem selected_cut_38349 : selected 9 ⟨1033082, by decide⟩
    (prefixPartial 12 301326) = some ⟨12, 2, 0, 1033082, 301326, 3157, 65536⟩ := by
  decide +kernel

theorem context_12_301326_1033082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301326 ⟨1033082, by decide⟩ :=
  accepted_of_selected 12 301326 ⟨1033082, by decide⟩ ⟨12, 2, 0, 1033082, 301326, 3157, 65536⟩
    (by decide) selected_cut_38349

theorem selected_cut_38350 : selected 9 ⟨1033145, by decide⟩
    (prefixPartial 12 301327) = some ⟨12, 2, 0, 1033145, 301327, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_301327_1033145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301327 ⟨1033145, by decide⟩ :=
  accepted_of_selected 12 301327 ⟨1033145, by decide⟩ ⟨12, 2, 0, 1033145, 301327, 3437, 65536⟩
    (by decide) selected_cut_38350

theorem unmarked_context_11_75331_1033146 : frontier 10 ⟨1033146, by decide⟩
    (prefixCache 11 75331) (prefixPartial 11 75331) = false := by
  decide +kernel

theorem node_context_11_75331_1033146 : EJMOriginalGlobalDAGData.nodes 10 ⟨1033146, by decide⟩ =
    .split (coordinate 11) (![⟨1032954, by decide⟩,⟨1033016, by decide⟩,⟨1033082, by decide⟩,⟨1033145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75331_1033146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75331 ⟨1033146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75331
    ⟨1033146, by decide⟩ (by decide) (![⟨1032954, by decide⟩,⟨1033016, by decide⟩,⟨1033082, by decide⟩,⟨1033145, by decide⟩]) unmarked_context_11_75331_1033146 node_context_11_75331_1033146
  intro a
  fin_cases a
  · exact context_12_301324_1032954
  · exact context_12_301325_1033016
  · exact context_12_301326_1033082
  · exact context_12_301327_1033145

theorem unmarked_context_10_18832_1033147 : frontier 11 ⟨1033147, by decide⟩
    (prefixCache 10 18832) (prefixPartial 10 18832) = false := by
  decide +kernel

theorem node_context_10_18832_1033147 : EJMOriginalGlobalDAGData.nodes 11 ⟨1033147, by decide⟩ =
    .split (coordinate 10) (![⟨1032441, by decide⟩,⟨1032687, by decide⟩,⟨1032901, by decide⟩,⟨1033146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18832_1033147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18832 ⟨1033147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18832
    ⟨1033147, by decide⟩ (by decide) (![⟨1032441, by decide⟩,⟨1032687, by decide⟩,⟨1032901, by decide⟩,⟨1033146, by decide⟩]) unmarked_context_10_18832_1033147 node_context_10_18832_1033147
  intro a
  fin_cases a
  · exact context_11_75328_1032441
  · exact context_11_75329_1032687
  · exact context_11_75330_1032901
  · exact context_11_75331_1033146

theorem selected_cut_38351 : selected 9 ⟨1033191, by decide⟩
    (prefixPartial 12 301328) = some ⟨12, 2, 0, 1033191, 301328, 1389, 65536⟩ := by
  decide +kernel

theorem context_12_301328_1033191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301328 ⟨1033191, by decide⟩ :=
  accepted_of_selected 12 301328 ⟨1033191, by decide⟩ ⟨12, 2, 0, 1033191, 301328, 1389, 65536⟩
    (by decide) selected_cut_38351

theorem selected_cut_38352 : selected 9 ⟨1033241, by decide⟩
    (prefixPartial 12 301329) = some ⟨12, 2, 0, 1033241, 301329, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_301329_1033241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301329 ⟨1033241, by decide⟩ :=
  accepted_of_selected 12 301329 ⟨1033241, by decide⟩ ⟨12, 2, 0, 1033241, 301329, 2341, 65536⟩
    (by decide) selected_cut_38352

theorem selected_cut_38353 : selected 9 ⟨1033279, by decide⟩
    (prefixPartial 12 301330) = some ⟨12, 2, 0, 1033279, 301330, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_301330_1033279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301330 ⟨1033279, by decide⟩ :=
  accepted_of_selected 12 301330 ⟨1033279, by decide⟩ ⟨12, 2, 0, 1033279, 301330, 2041, 65536⟩
    (by decide) selected_cut_38353

theorem selected_cut_38354 : selected 9 ⟨1033318, by decide⟩
    (prefixPartial 12 301331) = some ⟨12, 2, 0, 1033318, 301331, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_301331_1033318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301331 ⟨1033318, by decide⟩ :=
  accepted_of_selected 12 301331 ⟨1033318, by decide⟩ ⟨12, 2, 0, 1033318, 301331, 2377, 65536⟩
    (by decide) selected_cut_38354

theorem unmarked_context_11_75332_1033319 : frontier 10 ⟨1033319, by decide⟩
    (prefixCache 11 75332) (prefixPartial 11 75332) = false := by
  decide +kernel

theorem node_context_11_75332_1033319 : EJMOriginalGlobalDAGData.nodes 10 ⟨1033319, by decide⟩ =
    .split (coordinate 11) (![⟨1033191, by decide⟩,⟨1033241, by decide⟩,⟨1033279, by decide⟩,⟨1033318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75332_1033319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75332 ⟨1033319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75332
    ⟨1033319, by decide⟩ (by decide) (![⟨1033191, by decide⟩,⟨1033241, by decide⟩,⟨1033279, by decide⟩,⟨1033318, by decide⟩]) unmarked_context_11_75332_1033319 node_context_11_75332_1033319
  intro a
  fin_cases a
  · exact context_12_301328_1033191
  · exact context_12_301329_1033241
  · exact context_12_301330_1033279
  · exact context_12_301331_1033318

theorem selected_cut_38355 : selected 9 ⟨1033365, by decide⟩
    (prefixPartial 12 301332) = some ⟨12, 2, 0, 1033365, 301332, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_301332_1033365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301332 ⟨1033365, by decide⟩ :=
  accepted_of_selected 12 301332 ⟨1033365, by decide⟩ ⟨12, 2, 0, 1033365, 301332, 2489, 65536⟩
    (by decide) selected_cut_38355

theorem selected_cut_38356 : selected 9 ⟨692793, by decide⟩
    (prefixPartial 12 301333) = some ⟨12, 1, 0, 692793, 301333, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301333_692793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301333 ⟨692793, by decide⟩ :=
  accepted_of_selected 12 301333 ⟨692793, by decide⟩ ⟨12, 1, 0, 692793, 301333, 1, 65536⟩
    (by decide) selected_cut_38356

theorem selected_cut_38357 : selected 9 ⟨1033401, by decide⟩
    (prefixPartial 12 301334) = some ⟨12, 2, 0, 1033401, 301334, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_301334_1033401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301334 ⟨1033401, by decide⟩ :=
  accepted_of_selected 12 301334 ⟨1033401, by decide⟩ ⟨12, 2, 0, 1033401, 301334, 2313, 65536⟩
    (by decide) selected_cut_38357

theorem selected_cut_38358 : selected 9 ⟨1033439, by decide⟩
    (prefixPartial 12 301335) = some ⟨12, 2, 0, 1033439, 301335, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_301335_1033439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301335 ⟨1033439, by decide⟩ :=
  accepted_of_selected 12 301335 ⟨1033439, by decide⟩ ⟨12, 2, 0, 1033439, 301335, 2593, 65536⟩
    (by decide) selected_cut_38358

theorem unmarked_context_11_75333_1033440 : frontier 10 ⟨1033440, by decide⟩
    (prefixCache 11 75333) (prefixPartial 11 75333) = false := by
  decide +kernel

theorem node_context_11_75333_1033440 : EJMOriginalGlobalDAGData.nodes 10 ⟨1033440, by decide⟩ =
    .split (coordinate 11) (![⟨1033365, by decide⟩,⟨692793, by decide⟩,⟨1033401, by decide⟩,⟨1033439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75333_1033440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75333 ⟨1033440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75333
    ⟨1033440, by decide⟩ (by decide) (![⟨1033365, by decide⟩,⟨692793, by decide⟩,⟨1033401, by decide⟩,⟨1033439, by decide⟩]) unmarked_context_11_75333_1033440 node_context_11_75333_1033440
  intro a
  fin_cases a
  · exact context_12_301332_1033365
  · exact context_12_301333_692793
  · exact context_12_301334_1033401
  · exact context_12_301335_1033439

theorem selected_cut_38359 : selected 9 ⟨1033479, by decide⟩
    (prefixPartial 12 301336) = some ⟨12, 2, 0, 1033479, 301336, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_301336_1033479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301336 ⟨1033479, by decide⟩ :=
  accepted_of_selected 12 301336 ⟨1033479, by decide⟩ ⟨12, 2, 0, 1033479, 301336, 2313, 65536⟩
    (by decide) selected_cut_38359

theorem selected_cut_38360 : selected 9 ⟨1033516, by decide⟩
    (prefixPartial 12 301337) = some ⟨12, 2, 0, 1033516, 301337, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_301337_1033516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301337 ⟨1033516, by decide⟩ :=
  accepted_of_selected 12 301337 ⟨1033516, by decide⟩ ⟨12, 2, 0, 1033516, 301337, 2389, 65536⟩
    (by decide) selected_cut_38360

theorem selected_cut_38361 : selected 9 ⟨1033552, by decide⟩
    (prefixPartial 12 301338) = some ⟨12, 2, 0, 1033552, 301338, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_301338_1033552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301338 ⟨1033552, by decide⟩ :=
  accepted_of_selected 12 301338 ⟨1033552, by decide⟩ ⟨12, 2, 0, 1033552, 301338, 2317, 65536⟩
    (by decide) selected_cut_38361

theorem selected_cut_38362 : selected 9 ⟨1033584, by decide⟩
    (prefixPartial 12 301339) = some ⟨12, 2, 0, 1033584, 301339, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_301339_1033584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301339 ⟨1033584, by decide⟩ :=
  accepted_of_selected 12 301339 ⟨1033584, by decide⟩ ⟨12, 2, 0, 1033584, 301339, 2561, 65536⟩
    (by decide) selected_cut_38362

theorem unmarked_context_11_75334_1033585 : frontier 10 ⟨1033585, by decide⟩
    (prefixCache 11 75334) (prefixPartial 11 75334) = false := by
  decide +kernel

theorem node_context_11_75334_1033585 : EJMOriginalGlobalDAGData.nodes 10 ⟨1033585, by decide⟩ =
    .split (coordinate 11) (![⟨1033479, by decide⟩,⟨1033516, by decide⟩,⟨1033552, by decide⟩,⟨1033584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75334_1033585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75334 ⟨1033585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75334
    ⟨1033585, by decide⟩ (by decide) (![⟨1033479, by decide⟩,⟨1033516, by decide⟩,⟨1033552, by decide⟩,⟨1033584, by decide⟩]) unmarked_context_11_75334_1033585 node_context_11_75334_1033585
  intro a
  fin_cases a
  · exact context_12_301336_1033479
  · exact context_12_301337_1033516
  · exact context_12_301338_1033552
  · exact context_12_301339_1033584

theorem selected_cut_38363 : selected 9 ⟨1033622, by decide⟩
    (prefixPartial 12 301340) = some ⟨12, 2, 0, 1033622, 301340, 2377, 65536⟩ := by
  decide +kernel

theorem context_12_301340_1033622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301340 ⟨1033622, by decide⟩ :=
  accepted_of_selected 12 301340 ⟨1033622, by decide⟩ ⟨12, 2, 0, 1033622, 301340, 2377, 65536⟩
    (by decide) selected_cut_38363

theorem selected_cut_38364 : selected 9 ⟨1033661, by decide⟩
    (prefixPartial 12 301341) = some ⟨12, 2, 0, 1033661, 301341, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_301341_1033661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301341 ⟨1033661, by decide⟩ :=
  accepted_of_selected 12 301341 ⟨1033661, by decide⟩ ⟨12, 2, 0, 1033661, 301341, 2481, 65536⟩
    (by decide) selected_cut_38364

theorem selected_cut_38365 : selected 9 ⟨1033699, by decide⟩
    (prefixPartial 12 301342) = some ⟨12, 2, 0, 1033699, 301342, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_301342_1033699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301342 ⟨1033699, by decide⟩ :=
  accepted_of_selected 12 301342 ⟨1033699, by decide⟩ ⟨12, 2, 0, 1033699, 301342, 2317, 65536⟩
    (by decide) selected_cut_38365

theorem selected_cut_38366 : selected 9 ⟨1033736, by decide⟩
    (prefixPartial 12 301343) = some ⟨12, 2, 0, 1033736, 301343, 2493, 65536⟩ := by
  decide +kernel

theorem context_12_301343_1033736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301343 ⟨1033736, by decide⟩ :=
  accepted_of_selected 12 301343 ⟨1033736, by decide⟩ ⟨12, 2, 0, 1033736, 301343, 2493, 65536⟩
    (by decide) selected_cut_38366

theorem unmarked_context_11_75335_1033737 : frontier 10 ⟨1033737, by decide⟩
    (prefixCache 11 75335) (prefixPartial 11 75335) = false := by
  decide +kernel

theorem node_context_11_75335_1033737 : EJMOriginalGlobalDAGData.nodes 10 ⟨1033737, by decide⟩ =
    .split (coordinate 11) (![⟨1033622, by decide⟩,⟨1033661, by decide⟩,⟨1033699, by decide⟩,⟨1033736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75335_1033737 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75335 ⟨1033737, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75335
    ⟨1033737, by decide⟩ (by decide) (![⟨1033622, by decide⟩,⟨1033661, by decide⟩,⟨1033699, by decide⟩,⟨1033736, by decide⟩]) unmarked_context_11_75335_1033737 node_context_11_75335_1033737
  intro a
  fin_cases a
  · exact context_12_301340_1033622
  · exact context_12_301341_1033661
  · exact context_12_301342_1033699
  · exact context_12_301343_1033736

theorem unmarked_context_10_18833_1033738 : frontier 11 ⟨1033738, by decide⟩
    (prefixCache 10 18833) (prefixPartial 10 18833) = false := by
  decide +kernel

theorem node_context_10_18833_1033738 : EJMOriginalGlobalDAGData.nodes 11 ⟨1033738, by decide⟩ =
    .split (coordinate 10) (![⟨1033319, by decide⟩,⟨1033440, by decide⟩,⟨1033585, by decide⟩,⟨1033737, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18833_1033738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18833 ⟨1033738, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18833
    ⟨1033738, by decide⟩ (by decide) (![⟨1033319, by decide⟩,⟨1033440, by decide⟩,⟨1033585, by decide⟩,⟨1033737, by decide⟩]) unmarked_context_10_18833_1033738 node_context_10_18833_1033738
  intro a
  fin_cases a
  · exact context_11_75332_1033319
  · exact context_11_75333_1033440
  · exact context_11_75334_1033585
  · exact context_11_75335_1033737

theorem selected_cut_38367 : selected 9 ⟨1033739, by decide⟩
    (prefixPartial 12 301344) = some ⟨12, 1, 0, 1033739, 301344, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301344_1033739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301344 ⟨1033739, by decide⟩ :=
  accepted_of_selected 12 301344 ⟨1033739, by decide⟩ ⟨12, 1, 0, 1033739, 301344, 1, 65536⟩
    (by decide) selected_cut_38367

theorem selected_cut_38368 : selected 9 ⟨1033779, by decide⟩
    (prefixPartial 12 301345) = some ⟨12, 2, 0, 1033779, 301345, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_301345_1033779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301345 ⟨1033779, by decide⟩ :=
  accepted_of_selected 12 301345 ⟨1033779, by decide⟩ ⟨12, 2, 0, 1033779, 301345, 2513, 65536⟩
    (by decide) selected_cut_38368

theorem selected_cut_38369 : selected 9 ⟨1033819, by decide⟩
    (prefixPartial 12 301346) = some ⟨12, 2, 0, 1033819, 301346, 2037, 65536⟩ := by
  decide +kernel

theorem context_12_301346_1033819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301346 ⟨1033819, by decide⟩ :=
  accepted_of_selected 12 301346 ⟨1033819, by decide⟩ ⟨12, 2, 0, 1033819, 301346, 2037, 65536⟩
    (by decide) selected_cut_38369

theorem selected_cut_38370 : selected 9 ⟨1033850, by decide⟩
    (prefixPartial 12 301347) = some ⟨12, 2, 0, 1033850, 301347, 2401, 65536⟩ := by
  decide +kernel

theorem context_12_301347_1033850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301347 ⟨1033850, by decide⟩ :=
  accepted_of_selected 12 301347 ⟨1033850, by decide⟩ ⟨12, 2, 0, 1033850, 301347, 2401, 65536⟩
    (by decide) selected_cut_38370

theorem unmarked_context_11_75336_1033851 : frontier 10 ⟨1033851, by decide⟩
    (prefixCache 11 75336) (prefixPartial 11 75336) = false := by
  decide +kernel

theorem node_context_11_75336_1033851 : EJMOriginalGlobalDAGData.nodes 10 ⟨1033851, by decide⟩ =
    .split (coordinate 11) (![⟨1033739, by decide⟩,⟨1033779, by decide⟩,⟨1033819, by decide⟩,⟨1033850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75336_1033851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75336 ⟨1033851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75336
    ⟨1033851, by decide⟩ (by decide) (![⟨1033739, by decide⟩,⟨1033779, by decide⟩,⟨1033819, by decide⟩,⟨1033850, by decide⟩]) unmarked_context_11_75336_1033851 node_context_11_75336_1033851
  intro a
  fin_cases a
  · exact context_12_301344_1033739
  · exact context_12_301345_1033779
  · exact context_12_301346_1033819
  · exact context_12_301347_1033850

theorem selected_cut_38371 : selected 9 ⟨1033912, by decide⟩
    (prefixPartial 12 301348) = some ⟨12, 2, 0, 1033912, 301348, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_301348_1033912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301348 ⟨1033912, by decide⟩ :=
  accepted_of_selected 12 301348 ⟨1033912, by decide⟩ ⟨12, 2, 0, 1033912, 301348, 2853, 65536⟩
    (by decide) selected_cut_38371

theorem selected_cut_38372 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 301349) = some ⟨12, 1, 0, 891951, 301349, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301349_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301349 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 301349 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 301349, 1, 65536⟩
    (by decide) selected_cut_38372

theorem selected_cut_38373 : selected 9 ⟨1033960, by decide⟩
    (prefixPartial 12 301350) = some ⟨12, 2, 0, 1033960, 301350, 2437, 65536⟩ := by
  decide +kernel

theorem context_12_301350_1033960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301350 ⟨1033960, by decide⟩ :=
  accepted_of_selected 12 301350 ⟨1033960, by decide⟩ ⟨12, 2, 0, 1033960, 301350, 2437, 65536⟩
    (by decide) selected_cut_38373

theorem selected_cut_38374 : selected 9 ⟨1034001, by decide⟩
    (prefixPartial 12 301351) = some ⟨12, 2, 0, 1034001, 301351, 2737, 65536⟩ := by
  decide +kernel

theorem context_12_301351_1034001 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301351 ⟨1034001, by decide⟩ :=
  accepted_of_selected 12 301351 ⟨1034001, by decide⟩ ⟨12, 2, 0, 1034001, 301351, 2737, 65536⟩
    (by decide) selected_cut_38374

theorem unmarked_context_11_75337_1034002 : frontier 10 ⟨1034002, by decide⟩
    (prefixCache 11 75337) (prefixPartial 11 75337) = false := by
  decide +kernel

theorem node_context_11_75337_1034002 : EJMOriginalGlobalDAGData.nodes 10 ⟨1034002, by decide⟩ =
    .split (coordinate 11) (![⟨1033912, by decide⟩,⟨891951, by decide⟩,⟨1033960, by decide⟩,⟨1034001, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75337_1034002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75337 ⟨1034002, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75337
    ⟨1034002, by decide⟩ (by decide) (![⟨1033912, by decide⟩,⟨891951, by decide⟩,⟨1033960, by decide⟩,⟨1034001, by decide⟩]) unmarked_context_11_75337_1034002 node_context_11_75337_1034002
  intro a
  fin_cases a
  · exact context_12_301348_1033912
  · exact context_12_301349_891951
  · exact context_12_301350_1033960
  · exact context_12_301351_1034001

theorem selected_cut_38375 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 75338) = some ⟨11, 1, 0, 900587, 75338, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75338_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75338 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 75338 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 75338, 1, 262144⟩
    (by decide) selected_cut_38375

theorem selected_cut_38376 : selected 9 ⟨1034035, by decide⟩
    (prefixPartial 12 301356) = some ⟨12, 2, 0, 1034035, 301356, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_301356_1034035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301356 ⟨1034035, by decide⟩ :=
  accepted_of_selected 12 301356 ⟨1034035, by decide⟩ ⟨12, 2, 0, 1034035, 301356, 2381, 65536⟩
    (by decide) selected_cut_38376

theorem selected_cut_38377 : selected 9 ⟨1034070, by decide⟩
    (prefixPartial 12 301357) = some ⟨12, 2, 0, 1034070, 301357, 2549, 65536⟩ := by
  decide +kernel

theorem context_12_301357_1034070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301357 ⟨1034070, by decide⟩ :=
  accepted_of_selected 12 301357 ⟨1034070, by decide⟩ ⟨12, 2, 0, 1034070, 301357, 2549, 65536⟩
    (by decide) selected_cut_38377

theorem selected_cut_38378 : selected 9 ⟨1034108, by decide⟩
    (prefixPartial 12 301358) = some ⟨12, 2, 0, 1034108, 301358, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_301358_1034108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301358 ⟨1034108, by decide⟩ :=
  accepted_of_selected 12 301358 ⟨1034108, by decide⟩ ⟨12, 2, 0, 1034108, 301358, 2217, 65536⟩
    (by decide) selected_cut_38378

theorem selected_cut_38379 : selected 9 ⟨1034145, by decide⟩
    (prefixPartial 12 301359) = some ⟨12, 2, 0, 1034145, 301359, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_301359_1034145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301359 ⟨1034145, by decide⟩ :=
  accepted_of_selected 12 301359 ⟨1034145, by decide⟩ ⟨12, 2, 0, 1034145, 301359, 2529, 65536⟩
    (by decide) selected_cut_38379

theorem unmarked_context_11_75339_1034146 : frontier 10 ⟨1034146, by decide⟩
    (prefixCache 11 75339) (prefixPartial 11 75339) = false := by
  decide +kernel

theorem node_context_11_75339_1034146 : EJMOriginalGlobalDAGData.nodes 10 ⟨1034146, by decide⟩ =
    .split (coordinate 11) (![⟨1034035, by decide⟩,⟨1034070, by decide⟩,⟨1034108, by decide⟩,⟨1034145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75339_1034146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75339 ⟨1034146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75339
    ⟨1034146, by decide⟩ (by decide) (![⟨1034035, by decide⟩,⟨1034070, by decide⟩,⟨1034108, by decide⟩,⟨1034145, by decide⟩]) unmarked_context_11_75339_1034146 node_context_11_75339_1034146
  intro a
  fin_cases a
  · exact context_12_301356_1034035
  · exact context_12_301357_1034070
  · exact context_12_301358_1034108
  · exact context_12_301359_1034145

theorem unmarked_context_10_18834_1034147 : frontier 11 ⟨1034147, by decide⟩
    (prefixCache 10 18834) (prefixPartial 10 18834) = false := by
  decide +kernel

theorem node_context_10_18834_1034147 : EJMOriginalGlobalDAGData.nodes 11 ⟨1034147, by decide⟩ =
    .split (coordinate 10) (![⟨1033851, by decide⟩,⟨1034002, by decide⟩,⟨900587, by decide⟩,⟨1034146, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18834_1034147 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18834 ⟨1034147, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18834
    ⟨1034147, by decide⟩ (by decide) (![⟨1033851, by decide⟩,⟨1034002, by decide⟩,⟨900587, by decide⟩,⟨1034146, by decide⟩]) unmarked_context_10_18834_1034147 node_context_10_18834_1034147
  intro a
  fin_cases a
  · exact context_11_75336_1033851
  · exact context_11_75337_1034002
  · exact context_11_75338_900587
  · exact context_11_75339_1034146

theorem selected_cut_38380 : selected 9 ⟨1034184, by decide⟩
    (prefixPartial 12 301360) = some ⟨12, 2, 0, 1034184, 301360, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_301360_1034184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301360 ⟨1034184, by decide⟩ :=
  accepted_of_selected 12 301360 ⟨1034184, by decide⟩ ⟨12, 2, 0, 1034184, 301360, 2241, 65536⟩
    (by decide) selected_cut_38380

theorem selected_cut_38381 : selected 9 ⟨1034231, by decide⟩
    (prefixPartial 12 301361) = some ⟨12, 2, 0, 1034231, 301361, 2661, 65536⟩ := by
  decide +kernel

theorem context_12_301361_1034231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301361 ⟨1034231, by decide⟩ :=
  accepted_of_selected 12 301361 ⟨1034231, by decide⟩ ⟨12, 2, 0, 1034231, 301361, 2661, 65536⟩
    (by decide) selected_cut_38381

theorem selected_cut_38382 : selected 9 ⟨1034265, by decide⟩
    (prefixPartial 12 301362) = some ⟨12, 2, 0, 1034265, 301362, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_301362_1034265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301362 ⟨1034265, by decide⟩ :=
  accepted_of_selected 12 301362 ⟨1034265, by decide⟩ ⟨12, 2, 0, 1034265, 301362, 2177, 65536⟩
    (by decide) selected_cut_38382

theorem selected_cut_38383 : selected 9 ⟨1034322, by decide⟩
    (prefixPartial 12 301363) = some ⟨12, 2, 0, 1034322, 301363, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_301363_1034322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301363 ⟨1034322, by decide⟩ :=
  accepted_of_selected 12 301363 ⟨1034322, by decide⟩ ⟨12, 2, 0, 1034322, 301363, 2481, 65536⟩
    (by decide) selected_cut_38383

theorem unmarked_context_11_75340_1034323 : frontier 10 ⟨1034323, by decide⟩
    (prefixCache 11 75340) (prefixPartial 11 75340) = false := by
  decide +kernel

theorem node_context_11_75340_1034323 : EJMOriginalGlobalDAGData.nodes 10 ⟨1034323, by decide⟩ =
    .split (coordinate 11) (![⟨1034184, by decide⟩,⟨1034231, by decide⟩,⟨1034265, by decide⟩,⟨1034322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75340_1034323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75340 ⟨1034323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75340
    ⟨1034323, by decide⟩ (by decide) (![⟨1034184, by decide⟩,⟨1034231, by decide⟩,⟨1034265, by decide⟩,⟨1034322, by decide⟩]) unmarked_context_11_75340_1034323 node_context_11_75340_1034323
  intro a
  fin_cases a
  · exact context_12_301360_1034184
  · exact context_12_301361_1034231
  · exact context_12_301362_1034265
  · exact context_12_301363_1034322

theorem selected_cut_38384 : selected 9 ⟨1034371, by decide⟩
    (prefixPartial 12 301364) = some ⟨12, 2, 0, 1034371, 301364, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_301364_1034371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301364 ⟨1034371, by decide⟩ :=
  accepted_of_selected 12 301364 ⟨1034371, by decide⟩ ⟨12, 2, 0, 1034371, 301364, 2729, 65536⟩
    (by decide) selected_cut_38384

theorem selected_cut_38385 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 301365) = some ⟨12, 1, 0, 891951, 301365, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301365_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301365 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 301365 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 301365, 1, 65536⟩
    (by decide) selected_cut_38385

theorem selected_cut_38386 : selected 9 ⟨1034408, by decide⟩
    (prefixPartial 12 301366) = some ⟨12, 2, 0, 1034408, 301366, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_301366_1034408 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301366 ⟨1034408, by decide⟩ :=
  accepted_of_selected 12 301366 ⟨1034408, by decide⟩ ⟨12, 2, 0, 1034408, 301366, 2533, 65536⟩
    (by decide) selected_cut_38386

theorem selected_cut_38387 : selected 9 ⟨1034464, by decide⟩
    (prefixPartial 12 301367) = some ⟨12, 2, 0, 1034464, 301367, 2729, 65536⟩ := by
  decide +kernel

theorem context_12_301367_1034464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301367 ⟨1034464, by decide⟩ :=
  accepted_of_selected 12 301367 ⟨1034464, by decide⟩ ⟨12, 2, 0, 1034464, 301367, 2729, 65536⟩
    (by decide) selected_cut_38387

theorem unmarked_context_11_75341_1034465 : frontier 10 ⟨1034465, by decide⟩
    (prefixCache 11 75341) (prefixPartial 11 75341) = false := by
  decide +kernel

theorem node_context_11_75341_1034465 : EJMOriginalGlobalDAGData.nodes 10 ⟨1034465, by decide⟩ =
    .split (coordinate 11) (![⟨1034371, by decide⟩,⟨891951, by decide⟩,⟨1034408, by decide⟩,⟨1034464, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75341_1034465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75341 ⟨1034465, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75341
    ⟨1034465, by decide⟩ (by decide) (![⟨1034371, by decide⟩,⟨891951, by decide⟩,⟨1034408, by decide⟩,⟨1034464, by decide⟩]) unmarked_context_11_75341_1034465 node_context_11_75341_1034465
  intro a
  fin_cases a
  · exact context_12_301364_1034371
  · exact context_12_301365_891951
  · exact context_12_301366_1034408
  · exact context_12_301367_1034464

theorem selected_cut_38388 : selected 9 ⟨1034498, by decide⟩
    (prefixPartial 12 301368) = some ⟨12, 2, 0, 1034498, 301368, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_301368_1034498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301368 ⟨1034498, by decide⟩ :=
  accepted_of_selected 12 301368 ⟨1034498, by decide⟩ ⟨12, 2, 0, 1034498, 301368, 2197, 65536⟩
    (by decide) selected_cut_38388

theorem selected_cut_38389 : selected 9 ⟨1034537, by decide⟩
    (prefixPartial 12 301369) = some ⟨12, 2, 0, 1034537, 301369, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_301369_1034537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301369 ⟨1034537, by decide⟩ :=
  accepted_of_selected 12 301369 ⟨1034537, by decide⟩ ⟨12, 2, 0, 1034537, 301369, 2473, 65536⟩
    (by decide) selected_cut_38389

theorem selected_cut_38390 : selected 9 ⟨1034579, by decide⟩
    (prefixPartial 12 301370) = some ⟨12, 2, 0, 1034579, 301370, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_301370_1034579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301370 ⟨1034579, by decide⟩ :=
  accepted_of_selected 12 301370 ⟨1034579, by decide⟩ ⟨12, 2, 0, 1034579, 301370, 2333, 65536⟩
    (by decide) selected_cut_38390

theorem selected_cut_38391 : selected 9 ⟨1034624, by decide⟩
    (prefixPartial 12 301371) = some ⟨12, 2, 0, 1034624, 301371, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_301371_1034624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301371 ⟨1034624, by decide⟩ :=
  accepted_of_selected 12 301371 ⟨1034624, by decide⟩ ⟨12, 2, 0, 1034624, 301371, 2513, 65536⟩
    (by decide) selected_cut_38391

theorem unmarked_context_11_75342_1034625 : frontier 10 ⟨1034625, by decide⟩
    (prefixCache 11 75342) (prefixPartial 11 75342) = false := by
  decide +kernel

theorem node_context_11_75342_1034625 : EJMOriginalGlobalDAGData.nodes 10 ⟨1034625, by decide⟩ =
    .split (coordinate 11) (![⟨1034498, by decide⟩,⟨1034537, by decide⟩,⟨1034579, by decide⟩,⟨1034624, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75342_1034625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75342 ⟨1034625, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75342
    ⟨1034625, by decide⟩ (by decide) (![⟨1034498, by decide⟩,⟨1034537, by decide⟩,⟨1034579, by decide⟩,⟨1034624, by decide⟩]) unmarked_context_11_75342_1034625 node_context_11_75342_1034625
  intro a
  fin_cases a
  · exact context_12_301368_1034498
  · exact context_12_301369_1034537
  · exact context_12_301370_1034579
  · exact context_12_301371_1034624

theorem selected_cut_38392 : selected 9 ⟨1034655, by decide⟩
    (prefixPartial 12 301372) = some ⟨12, 2, 0, 1034655, 301372, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_301372_1034655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301372 ⟨1034655, by decide⟩ :=
  accepted_of_selected 12 301372 ⟨1034655, by decide⟩ ⟨12, 2, 0, 1034655, 301372, 2089, 65536⟩
    (by decide) selected_cut_38392

theorem selected_cut_38393 : selected 9 ⟨1034693, by decide⟩
    (prefixPartial 12 301373) = some ⟨12, 2, 0, 1034693, 301373, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_301373_1034693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301373 ⟨1034693, by decide⟩ :=
  accepted_of_selected 12 301373 ⟨1034693, by decide⟩ ⟨12, 2, 0, 1034693, 301373, 2269, 65536⟩
    (by decide) selected_cut_38393

theorem selected_cut_38394 : selected 9 ⟨1034724, by decide⟩
    (prefixPartial 12 301374) = some ⟨12, 2, 0, 1034724, 301374, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_301374_1034724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301374 ⟨1034724, by decide⟩ :=
  accepted_of_selected 12 301374 ⟨1034724, by decide⟩ ⟨12, 2, 0, 1034724, 301374, 2069, 65536⟩
    (by decide) selected_cut_38394

theorem selected_cut_38395 : selected 9 ⟨1034758, by decide⟩
    (prefixPartial 12 301375) = some ⟨12, 2, 0, 1034758, 301375, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_301375_1034758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301375 ⟨1034758, by decide⟩ :=
  accepted_of_selected 12 301375 ⟨1034758, by decide⟩ ⟨12, 2, 0, 1034758, 301375, 2241, 65536⟩
    (by decide) selected_cut_38395

theorem unmarked_context_11_75343_1034759 : frontier 10 ⟨1034759, by decide⟩
    (prefixCache 11 75343) (prefixPartial 11 75343) = false := by
  decide +kernel

theorem node_context_11_75343_1034759 : EJMOriginalGlobalDAGData.nodes 10 ⟨1034759, by decide⟩ =
    .split (coordinate 11) (![⟨1034655, by decide⟩,⟨1034693, by decide⟩,⟨1034724, by decide⟩,⟨1034758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75343_1034759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75343 ⟨1034759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75343
    ⟨1034759, by decide⟩ (by decide) (![⟨1034655, by decide⟩,⟨1034693, by decide⟩,⟨1034724, by decide⟩,⟨1034758, by decide⟩]) unmarked_context_11_75343_1034759 node_context_11_75343_1034759
  intro a
  fin_cases a
  · exact context_12_301372_1034655
  · exact context_12_301373_1034693
  · exact context_12_301374_1034724
  · exact context_12_301375_1034758

theorem unmarked_context_10_18835_1034760 : frontier 11 ⟨1034760, by decide⟩
    (prefixCache 10 18835) (prefixPartial 10 18835) = false := by
  decide +kernel

theorem node_context_10_18835_1034760 : EJMOriginalGlobalDAGData.nodes 11 ⟨1034760, by decide⟩ =
    .split (coordinate 10) (![⟨1034323, by decide⟩,⟨1034465, by decide⟩,⟨1034625, by decide⟩,⟨1034759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18835_1034760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18835 ⟨1034760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18835
    ⟨1034760, by decide⟩ (by decide) (![⟨1034323, by decide⟩,⟨1034465, by decide⟩,⟨1034625, by decide⟩,⟨1034759, by decide⟩]) unmarked_context_10_18835_1034760 node_context_10_18835_1034760
  intro a
  fin_cases a
  · exact context_11_75340_1034323
  · exact context_11_75341_1034465
  · exact context_11_75342_1034625
  · exact context_11_75343_1034759

theorem unmarked_context_9_4708_1034761 : frontier 12 ⟨1034761, by decide⟩
    (prefixCache 9 4708) (prefixPartial 9 4708) = false := by
  decide +kernel

theorem node_context_9_4708_1034761 : EJMOriginalGlobalDAGData.nodes 12 ⟨1034761, by decide⟩ =
    .split (coordinate 9) (![⟨1033147, by decide⟩,⟨1033738, by decide⟩,⟨1034147, by decide⟩,⟨1034760, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4708_1034761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4708 ⟨1034761, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4708
    ⟨1034761, by decide⟩ (by decide) (![⟨1033147, by decide⟩,⟨1033738, by decide⟩,⟨1034147, by decide⟩,⟨1034760, by decide⟩]) unmarked_context_9_4708_1034761 node_context_9_4708_1034761
  intro a
  fin_cases a
  · exact context_10_18832_1033147
  · exact context_10_18833_1033738
  · exact context_10_18834_1034147
  · exact context_10_18835_1034760

theorem selected_cut_38396 : selected 9 ⟨1034854, by decide⟩
    (prefixPartial 12 301376) = some ⟨12, 2, 0, 1034854, 301376, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_301376_1034854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301376 ⟨1034854, by decide⟩ :=
  accepted_of_selected 12 301376 ⟨1034854, by decide⟩ ⟨12, 2, 0, 1034854, 301376, 1293, 65536⟩
    (by decide) selected_cut_38396

theorem selected_cut_38397 : selected 9 ⟨1034898, by decide⟩
    (prefixPartial 12 301377) = some ⟨12, 2, 0, 1034898, 301377, 1909, 65536⟩ := by
  decide +kernel

theorem context_12_301377_1034898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301377 ⟨1034898, by decide⟩ :=
  accepted_of_selected 12 301377 ⟨1034898, by decide⟩ ⟨12, 2, 0, 1034898, 301377, 1909, 65536⟩
    (by decide) selected_cut_38397

theorem selected_cut_38398 : selected 9 ⟨1034934, by decide⟩
    (prefixPartial 12 301378) = some ⟨12, 2, 0, 1034934, 301378, 1845, 65536⟩ := by
  decide +kernel

theorem context_12_301378_1034934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301378 ⟨1034934, by decide⟩ :=
  accepted_of_selected 12 301378 ⟨1034934, by decide⟩ ⟨12, 2, 0, 1034934, 301378, 1845, 65536⟩
    (by decide) selected_cut_38398

theorem selected_cut_38399 : selected 9 ⟨1034968, by decide⟩
    (prefixPartial 12 301379) = some ⟨12, 2, 0, 1034968, 301379, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_301379_1034968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301379 ⟨1034968, by decide⟩ :=
  accepted_of_selected 12 301379 ⟨1034968, by decide⟩ ⟨12, 2, 0, 1034968, 301379, 1857, 65536⟩
    (by decide) selected_cut_38399

theorem unmarked_context_11_75344_1034969 : frontier 10 ⟨1034969, by decide⟩
    (prefixCache 11 75344) (prefixPartial 11 75344) = false := by
  decide +kernel

theorem node_context_11_75344_1034969 : EJMOriginalGlobalDAGData.nodes 10 ⟨1034969, by decide⟩ =
    .split (coordinate 11) (![⟨1034854, by decide⟩,⟨1034898, by decide⟩,⟨1034934, by decide⟩,⟨1034968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75344_1034969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75344 ⟨1034969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75344
    ⟨1034969, by decide⟩ (by decide) (![⟨1034854, by decide⟩,⟨1034898, by decide⟩,⟨1034934, by decide⟩,⟨1034968, by decide⟩]) unmarked_context_11_75344_1034969 node_context_11_75344_1034969
  intro a
  fin_cases a
  · exact context_12_301376_1034854
  · exact context_12_301377_1034898
  · exact context_12_301378_1034934
  · exact context_12_301379_1034968

theorem selected_cut_38400 : selected 9 ⟨1035030, by decide⟩
    (prefixPartial 12 301380) = some ⟨12, 2, 0, 1035030, 301380, 2925, 65536⟩ := by
  decide +kernel

theorem context_12_301380_1035030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301380 ⟨1035030, by decide⟩ :=
  accepted_of_selected 12 301380 ⟨1035030, by decide⟩ ⟨12, 2, 0, 1035030, 301380, 2925, 65536⟩
    (by decide) selected_cut_38400

theorem selected_cut_38401 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 301381) = some ⟨12, 1, 0, 891951, 301381, 1, 65536⟩ := by
  decide +kernel

theorem context_12_301381_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301381 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 301381 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 301381, 1, 65536⟩
    (by decide) selected_cut_38401

theorem selected_cut_38402 : selected 9 ⟨1035077, by decide⟩
    (prefixPartial 12 301382) = some ⟨12, 2, 0, 1035077, 301382, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_301382_1035077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 301382 ⟨1035077, by decide⟩ :=
  accepted_of_selected 12 301382 ⟨1035077, by decide⟩ ⟨12, 2, 0, 1035077, 301382, 2277, 65536⟩
    (by decide) selected_cut_38402

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
