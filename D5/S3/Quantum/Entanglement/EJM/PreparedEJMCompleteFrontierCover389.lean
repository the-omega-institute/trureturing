/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover388
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_37347 : selected 9 ⟨998109, by decide⟩
    (prefixPartial 12 299640) = some ⟨12, 2, 0, 998109, 299640, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_299640_998109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299640 ⟨998109, by decide⟩ :=
  accepted_of_selected 12 299640 ⟨998109, by decide⟩ ⟨12, 2, 0, 998109, 299640, 1961, 65536⟩
    (by decide) selected_cut_37347

theorem selected_cut_37348 : selected 9 ⟨998145, by decide⟩
    (prefixPartial 12 299641) = some ⟨12, 2, 0, 998145, 299641, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_299641_998145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299641 ⟨998145, by decide⟩ :=
  accepted_of_selected 12 299641 ⟨998145, by decide⟩ ⟨12, 2, 0, 998145, 299641, 2117, 65536⟩
    (by decide) selected_cut_37348

theorem selected_cut_37349 : selected 9 ⟨893903, by decide⟩
    (prefixPartial 12 299642) = some ⟨12, 1, 0, 893903, 299642, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299642_893903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299642 ⟨893903, by decide⟩ :=
  accepted_of_selected 12 299642 ⟨893903, by decide⟩ ⟨12, 1, 0, 893903, 299642, 1, 65536⟩
    (by decide) selected_cut_37349

theorem selected_cut_37350 : selected 9 ⟨998179, by decide⟩
    (prefixPartial 12 299643) = some ⟨12, 2, 0, 998179, 299643, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_299643_998179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299643 ⟨998179, by decide⟩ :=
  accepted_of_selected 12 299643 ⟨998179, by decide⟩ ⟨12, 2, 0, 998179, 299643, 2013, 65536⟩
    (by decide) selected_cut_37350

theorem unmarked_context_11_74910_998180 : frontier 10 ⟨998180, by decide⟩
    (prefixCache 11 74910) (prefixPartial 11 74910) = false := by
  decide +kernel

theorem node_context_11_74910_998180 : EJMOriginalGlobalDAGData.nodes 10 ⟨998180, by decide⟩ =
    .split (coordinate 11) (![⟨998109, by decide⟩,⟨998145, by decide⟩,⟨893903, by decide⟩,⟨998179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74910_998180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74910 ⟨998180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74910
    ⟨998180, by decide⟩ (by decide) (![⟨998109, by decide⟩,⟨998145, by decide⟩,⟨893903, by decide⟩,⟨998179, by decide⟩]) unmarked_context_11_74910_998180 node_context_11_74910_998180
  intro a
  fin_cases a
  · exact context_12_299640_998109
  · exact context_12_299641_998145
  · exact context_12_299642_893903
  · exact context_12_299643_998179

theorem selected_cut_37351 : selected 9 ⟨998206, by decide⟩
    (prefixPartial 12 299644) = some ⟨12, 2, 0, 998206, 299644, 1837, 65536⟩ := by
  decide +kernel

theorem context_12_299644_998206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299644 ⟨998206, by decide⟩ :=
  accepted_of_selected 12 299644 ⟨998206, by decide⟩ ⟨12, 2, 0, 998206, 299644, 1837, 65536⟩
    (by decide) selected_cut_37351

theorem selected_cut_37352 : selected 9 ⟨998238, by decide⟩
    (prefixPartial 12 299645) = some ⟨12, 2, 0, 998238, 299645, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_299645_998238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299645 ⟨998238, by decide⟩ :=
  accepted_of_selected 12 299645 ⟨998238, by decide⟩ ⟨12, 2, 0, 998238, 299645, 2013, 65536⟩
    (by decide) selected_cut_37352

theorem selected_cut_37353 : selected 9 ⟨998264, by decide⟩
    (prefixPartial 12 299646) = some ⟨12, 2, 0, 998264, 299646, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_299646_998264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299646 ⟨998264, by decide⟩ :=
  accepted_of_selected 12 299646 ⟨998264, by decide⟩ ⟨12, 2, 0, 998264, 299646, 1573, 65536⟩
    (by decide) selected_cut_37353

theorem selected_cut_37354 : selected 9 ⟨998289, by decide⟩
    (prefixPartial 12 299647) = some ⟨12, 2, 0, 998289, 299647, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_299647_998289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299647 ⟨998289, by decide⟩ :=
  accepted_of_selected 12 299647 ⟨998289, by decide⟩ ⟨12, 2, 0, 998289, 299647, 1677, 65536⟩
    (by decide) selected_cut_37354

theorem unmarked_context_11_74911_998290 : frontier 10 ⟨998290, by decide⟩
    (prefixCache 11 74911) (prefixPartial 11 74911) = false := by
  decide +kernel

theorem node_context_11_74911_998290 : EJMOriginalGlobalDAGData.nodes 10 ⟨998290, by decide⟩ =
    .split (coordinate 11) (![⟨998206, by decide⟩,⟨998238, by decide⟩,⟨998264, by decide⟩,⟨998289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74911_998290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74911 ⟨998290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74911
    ⟨998290, by decide⟩ (by decide) (![⟨998206, by decide⟩,⟨998238, by decide⟩,⟨998264, by decide⟩,⟨998289, by decide⟩]) unmarked_context_11_74911_998290 node_context_11_74911_998290
  intro a
  fin_cases a
  · exact context_12_299644_998206
  · exact context_12_299645_998238
  · exact context_12_299646_998264
  · exact context_12_299647_998289

theorem unmarked_context_10_18727_998291 : frontier 11 ⟨998291, by decide⟩
    (prefixCache 10 18727) (prefixPartial 10 18727) = false := by
  decide +kernel

theorem node_context_10_18727_998291 : EJMOriginalGlobalDAGData.nodes 11 ⟨998291, by decide⟩ =
    .split (coordinate 10) (![⟨998011, by decide⟩,⟨998082, by decide⟩,⟨998180, by decide⟩,⟨998290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18727_998291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18727 ⟨998291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18727
    ⟨998291, by decide⟩ (by decide) (![⟨998011, by decide⟩,⟨998082, by decide⟩,⟨998180, by decide⟩,⟨998290, by decide⟩]) unmarked_context_10_18727_998291 node_context_10_18727_998291
  intro a
  fin_cases a
  · exact context_11_74908_998011
  · exact context_11_74909_998082
  · exact context_11_74910_998180
  · exact context_11_74911_998290

theorem unmarked_context_9_4681_998292 : frontier 12 ⟨998292, by decide⟩
    (prefixCache 9 4681) (prefixPartial 9 4681) = false := by
  decide +kernel

theorem node_context_9_4681_998292 : EJMOriginalGlobalDAGData.nodes 12 ⟨998292, by decide⟩ =
    .split (coordinate 9) (![⟨997477, by decide⟩,⟨893098, by decide⟩,⟨997909, by decide⟩,⟨998291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4681_998292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4681 ⟨998292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4681
    ⟨998292, by decide⟩ (by decide) (![⟨997477, by decide⟩,⟨893098, by decide⟩,⟨997909, by decide⟩,⟨998291, by decide⟩]) unmarked_context_9_4681_998292 node_context_9_4681_998292
  intro a
  fin_cases a
  · exact context_10_18724_997477
  · exact context_10_18725_893098
  · exact context_10_18726_997909
  · exact context_10_18727_998291

theorem selected_cut_37355 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74912) = some ⟨11, 1, 0, 907917, 74912, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74912_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74912 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74912 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74912, 1, 262144⟩
    (by decide) selected_cut_37355

theorem selected_cut_37356 : selected 9 ⟨998308, by decide⟩
    (prefixPartial 12 299652) = some ⟨12, 2, 0, 998308, 299652, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_299652_998308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299652 ⟨998308, by decide⟩ :=
  accepted_of_selected 12 299652 ⟨998308, by decide⟩ ⟨12, 2, 0, 998308, 299652, 1357, 65536⟩
    (by decide) selected_cut_37356

theorem selected_cut_37357 : selected 9 ⟨998330, by decide⟩
    (prefixPartial 12 299653) = some ⟨12, 2, 0, 998330, 299653, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_299653_998330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299653 ⟨998330, by decide⟩ :=
  accepted_of_selected 12 299653 ⟨998330, by decide⟩ ⟨12, 2, 0, 998330, 299653, 1449, 65536⟩
    (by decide) selected_cut_37357

theorem selected_cut_37358 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 299654) = some ⟨12, 1, 0, 984676, 299654, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299654_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299654 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 299654 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 299654, 1, 65536⟩
    (by decide) selected_cut_37358

theorem selected_cut_37359 : selected 9 ⟨998352, by decide⟩
    (prefixPartial 12 299655) = some ⟨12, 2, 0, 998352, 299655, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_299655_998352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299655 ⟨998352, by decide⟩ :=
  accepted_of_selected 12 299655 ⟨998352, by decide⟩ ⟨12, 2, 0, 998352, 299655, 1385, 65536⟩
    (by decide) selected_cut_37359

theorem unmarked_context_11_74913_998353 : frontier 10 ⟨998353, by decide⟩
    (prefixCache 11 74913) (prefixPartial 11 74913) = false := by
  decide +kernel

theorem node_context_11_74913_998353 : EJMOriginalGlobalDAGData.nodes 10 ⟨998353, by decide⟩ =
    .split (coordinate 11) (![⟨998308, by decide⟩,⟨998330, by decide⟩,⟨984676, by decide⟩,⟨998352, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74913_998353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74913 ⟨998353, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74913
    ⟨998353, by decide⟩ (by decide) (![⟨998308, by decide⟩,⟨998330, by decide⟩,⟨984676, by decide⟩,⟨998352, by decide⟩]) unmarked_context_11_74913_998353 node_context_11_74913_998353
  intro a
  fin_cases a
  · exact context_12_299652_998308
  · exact context_12_299653_998330
  · exact context_12_299654_984676
  · exact context_12_299655_998352

theorem selected_cut_37360 : selected 9 ⟨998373, by decide⟩
    (prefixPartial 12 299656) = some ⟨12, 2, 0, 998373, 299656, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_299656_998373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299656 ⟨998373, by decide⟩ :=
  accepted_of_selected 12 299656 ⟨998373, by decide⟩ ⟨12, 2, 0, 998373, 299656, 1353, 65536⟩
    (by decide) selected_cut_37360

theorem selected_cut_37361 : selected 9 ⟨998393, by decide⟩
    (prefixPartial 12 299657) = some ⟨12, 2, 0, 998393, 299657, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_299657_998393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299657 ⟨998393, by decide⟩ :=
  accepted_of_selected 12 299657 ⟨998393, by decide⟩ ⟨12, 2, 0, 998393, 299657, 1465, 65536⟩
    (by decide) selected_cut_37361

theorem selected_cut_37362 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 299658) = some ⟨12, 1, 0, 984676, 299658, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299658_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299658 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 299658 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 299658, 1, 65536⟩
    (by decide) selected_cut_37362

theorem selected_cut_37363 : selected 9 ⟨998414, by decide⟩
    (prefixPartial 12 299659) = some ⟨12, 2, 0, 998414, 299659, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_299659_998414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299659 ⟨998414, by decide⟩ :=
  accepted_of_selected 12 299659 ⟨998414, by decide⟩ ⟨12, 2, 0, 998414, 299659, 1405, 65536⟩
    (by decide) selected_cut_37363

theorem unmarked_context_11_74914_998415 : frontier 10 ⟨998415, by decide⟩
    (prefixCache 11 74914) (prefixPartial 11 74914) = false := by
  decide +kernel

theorem node_context_11_74914_998415 : EJMOriginalGlobalDAGData.nodes 10 ⟨998415, by decide⟩ =
    .split (coordinate 11) (![⟨998373, by decide⟩,⟨998393, by decide⟩,⟨984676, by decide⟩,⟨998414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74914_998415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74914 ⟨998415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74914
    ⟨998415, by decide⟩ (by decide) (![⟨998373, by decide⟩,⟨998393, by decide⟩,⟨984676, by decide⟩,⟨998414, by decide⟩]) unmarked_context_11_74914_998415 node_context_11_74914_998415
  intro a
  fin_cases a
  · exact context_12_299656_998373
  · exact context_12_299657_998393
  · exact context_12_299658_984676
  · exact context_12_299659_998414

theorem selected_cut_37364 : selected 10 ⟨998475, by decide⟩
    (prefixPartial 11 74915) = some ⟨11, 2, 0, 998475, 74915, 3949, 262144⟩ := by
  decide +kernel

theorem context_11_74915_998475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74915 ⟨998475, by decide⟩ :=
  accepted_of_selected 11 74915 ⟨998475, by decide⟩ ⟨11, 2, 0, 998475, 74915, 3949, 262144⟩
    (by decide) selected_cut_37364

theorem unmarked_context_10_18728_998476 : frontier 11 ⟨998476, by decide⟩
    (prefixCache 10 18728) (prefixPartial 10 18728) = false := by
  decide +kernel

theorem node_context_10_18728_998476 : EJMOriginalGlobalDAGData.nodes 11 ⟨998476, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨998353, by decide⟩,⟨998415, by decide⟩,⟨998475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18728_998476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18728 ⟨998476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18728
    ⟨998476, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨998353, by decide⟩,⟨998415, by decide⟩,⟨998475, by decide⟩]) unmarked_context_10_18728_998476 node_context_10_18728_998476
  intro a
  fin_cases a
  · exact context_11_74912_907917
  · exact context_11_74913_998353
  · exact context_11_74914_998415
  · exact context_11_74915_998475

theorem selected_cut_37365 : selected 10 ⟨998534, by decide⟩
    (prefixPartial 11 74916) = some ⟨11, 2, 0, 998534, 74916, 3669, 262144⟩ := by
  decide +kernel

theorem context_11_74916_998534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74916 ⟨998534, by decide⟩ :=
  accepted_of_selected 11 74916 ⟨998534, by decide⟩ ⟨11, 2, 0, 998534, 74916, 3669, 262144⟩
    (by decide) selected_cut_37365

theorem selected_cut_37366 : selected 10 ⟨998583, by decide⟩
    (prefixPartial 11 74917) = some ⟨11, 2, 0, 998583, 74917, 3309, 262144⟩ := by
  decide +kernel

theorem context_11_74917_998583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74917 ⟨998583, by decide⟩ :=
  accepted_of_selected 11 74917 ⟨998583, by decide⟩ ⟨11, 2, 0, 998583, 74917, 3309, 262144⟩
    (by decide) selected_cut_37366

theorem selected_cut_37367 : selected 10 ⟨998631, by decide⟩
    (prefixPartial 11 74918) = some ⟨11, 2, 0, 998631, 74918, 3357, 262144⟩ := by
  decide +kernel

theorem context_11_74918_998631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74918 ⟨998631, by decide⟩ :=
  accepted_of_selected 11 74918 ⟨998631, by decide⟩ ⟨11, 2, 0, 998631, 74918, 3357, 262144⟩
    (by decide) selected_cut_37367

theorem selected_cut_37368 : selected 10 ⟨998690, by decide⟩
    (prefixPartial 11 74919) = some ⟨11, 2, 0, 998690, 74919, 3725, 262144⟩ := by
  decide +kernel

theorem context_11_74919_998690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74919 ⟨998690, by decide⟩ :=
  accepted_of_selected 11 74919 ⟨998690, by decide⟩ ⟨11, 2, 0, 998690, 74919, 3725, 262144⟩
    (by decide) selected_cut_37368

theorem unmarked_context_10_18729_998691 : frontier 11 ⟨998691, by decide⟩
    (prefixCache 10 18729) (prefixPartial 10 18729) = false := by
  decide +kernel

theorem node_context_10_18729_998691 : EJMOriginalGlobalDAGData.nodes 11 ⟨998691, by decide⟩ =
    .split (coordinate 10) (![⟨998534, by decide⟩,⟨998583, by decide⟩,⟨998631, by decide⟩,⟨998690, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18729_998691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18729 ⟨998691, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18729
    ⟨998691, by decide⟩ (by decide) (![⟨998534, by decide⟩,⟨998583, by decide⟩,⟨998631, by decide⟩,⟨998690, by decide⟩]) unmarked_context_10_18729_998691 node_context_10_18729_998691
  intro a
  fin_cases a
  · exact context_11_74916_998534
  · exact context_11_74917_998583
  · exact context_11_74918_998631
  · exact context_11_74919_998690

theorem selected_cut_37369 : selected 10 ⟨998724, by decide⟩
    (prefixPartial 11 74920) = some ⟨11, 2, 0, 998724, 74920, 2621, 262144⟩ := by
  decide +kernel

theorem context_11_74920_998724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74920 ⟨998724, by decide⟩ :=
  accepted_of_selected 11 74920 ⟨998724, by decide⟩ ⟨11, 2, 0, 998724, 74920, 2621, 262144⟩
    (by decide) selected_cut_37369

theorem selected_cut_37370 : selected 10 ⟨998756, by decide⟩
    (prefixPartial 11 74921) = some ⟨11, 2, 0, 998756, 74921, 2489, 262144⟩ := by
  decide +kernel

theorem context_11_74921_998756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74921 ⟨998756, by decide⟩ :=
  accepted_of_selected 11 74921 ⟨998756, by decide⟩ ⟨11, 2, 0, 998756, 74921, 2489, 262144⟩
    (by decide) selected_cut_37370

theorem selected_cut_37371 : selected 10 ⟨998766, by decide⟩
    (prefixPartial 11 74922) = some ⟨11, 2, 0, 998766, 74922, 809, 262144⟩ := by
  decide +kernel

theorem context_11_74922_998766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74922 ⟨998766, by decide⟩ :=
  accepted_of_selected 11 74922 ⟨998766, by decide⟩ ⟨11, 2, 0, 998766, 74922, 809, 262144⟩
    (by decide) selected_cut_37371

theorem selected_cut_37372 : selected 10 ⟨998800, by decide⟩
    (prefixPartial 11 74923) = some ⟨11, 2, 0, 998800, 74923, 2469, 262144⟩ := by
  decide +kernel

theorem context_11_74923_998800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74923 ⟨998800, by decide⟩ :=
  accepted_of_selected 11 74923 ⟨998800, by decide⟩ ⟨11, 2, 0, 998800, 74923, 2469, 262144⟩
    (by decide) selected_cut_37372

theorem unmarked_context_10_18730_998801 : frontier 11 ⟨998801, by decide⟩
    (prefixCache 10 18730) (prefixPartial 10 18730) = false := by
  decide +kernel

theorem node_context_10_18730_998801 : EJMOriginalGlobalDAGData.nodes 11 ⟨998801, by decide⟩ =
    .split (coordinate 10) (![⟨998724, by decide⟩,⟨998756, by decide⟩,⟨998766, by decide⟩,⟨998800, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18730_998801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18730 ⟨998801, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18730
    ⟨998801, by decide⟩ (by decide) (![⟨998724, by decide⟩,⟨998756, by decide⟩,⟨998766, by decide⟩,⟨998800, by decide⟩]) unmarked_context_10_18730_998801 node_context_10_18730_998801
  intro a
  fin_cases a
  · exact context_11_74920_998724
  · exact context_11_74921_998756
  · exact context_11_74922_998766
  · exact context_11_74923_998800

theorem selected_cut_37373 : selected 10 ⟨998830, by decide⟩
    (prefixPartial 11 74924) = some ⟨11, 2, 0, 998830, 74924, 2269, 262144⟩ := by
  decide +kernel

theorem context_11_74924_998830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74924 ⟨998830, by decide⟩ :=
  accepted_of_selected 11 74924 ⟨998830, by decide⟩ ⟨11, 2, 0, 998830, 74924, 2269, 262144⟩
    (by decide) selected_cut_37373

theorem selected_cut_37374 : selected 10 ⟨998861, by decide⟩
    (prefixPartial 11 74925) = some ⟨11, 2, 0, 998861, 74925, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_74925_998861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74925 ⟨998861, by decide⟩ :=
  accepted_of_selected 11 74925 ⟨998861, by decide⟩ ⟨11, 2, 0, 998861, 74925, 2173, 262144⟩
    (by decide) selected_cut_37374

theorem selected_cut_37375 : selected 10 ⟨998898, by decide⟩
    (prefixPartial 11 74926) = some ⟨11, 2, 0, 998898, 74926, 2253, 262144⟩ := by
  decide +kernel

theorem context_11_74926_998898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74926 ⟨998898, by decide⟩ :=
  accepted_of_selected 11 74926 ⟨998898, by decide⟩ ⟨11, 2, 0, 998898, 74926, 2253, 262144⟩
    (by decide) selected_cut_37375

theorem selected_cut_37376 : selected 10 ⟨998924, by decide⟩
    (prefixPartial 11 74927) = some ⟨11, 2, 0, 998924, 74927, 2097, 262144⟩ := by
  decide +kernel

theorem context_11_74927_998924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74927 ⟨998924, by decide⟩ :=
  accepted_of_selected 11 74927 ⟨998924, by decide⟩ ⟨11, 2, 0, 998924, 74927, 2097, 262144⟩
    (by decide) selected_cut_37376

theorem unmarked_context_10_18731_998925 : frontier 11 ⟨998925, by decide⟩
    (prefixCache 10 18731) (prefixPartial 10 18731) = false := by
  decide +kernel

theorem node_context_10_18731_998925 : EJMOriginalGlobalDAGData.nodes 11 ⟨998925, by decide⟩ =
    .split (coordinate 10) (![⟨998830, by decide⟩,⟨998861, by decide⟩,⟨998898, by decide⟩,⟨998924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18731_998925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18731 ⟨998925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18731
    ⟨998925, by decide⟩ (by decide) (![⟨998830, by decide⟩,⟨998861, by decide⟩,⟨998898, by decide⟩,⟨998924, by decide⟩]) unmarked_context_10_18731_998925 node_context_10_18731_998925
  intro a
  fin_cases a
  · exact context_11_74924_998830
  · exact context_11_74925_998861
  · exact context_11_74926_998898
  · exact context_11_74927_998924

theorem unmarked_context_9_4682_998926 : frontier 12 ⟨998926, by decide⟩
    (prefixCache 9 4682) (prefixPartial 9 4682) = false := by
  decide +kernel

theorem node_context_9_4682_998926 : EJMOriginalGlobalDAGData.nodes 12 ⟨998926, by decide⟩ =
    .split (coordinate 9) (![⟨998476, by decide⟩,⟨998691, by decide⟩,⟨998801, by decide⟩,⟨998925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4682_998926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4682 ⟨998926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4682
    ⟨998926, by decide⟩ (by decide) (![⟨998476, by decide⟩,⟨998691, by decide⟩,⟨998801, by decide⟩,⟨998925, by decide⟩]) unmarked_context_9_4682_998926 node_context_9_4682_998926
  intro a
  fin_cases a
  · exact context_10_18728_998476
  · exact context_10_18729_998691
  · exact context_10_18730_998801
  · exact context_10_18731_998925

theorem selected_cut_37377 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 74928) = some ⟨11, 1, 0, 907917, 74928, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74928_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74928 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 74928 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 74928, 1, 262144⟩
    (by decide) selected_cut_37377

theorem selected_cut_37378 : selected 10 ⟨998962, by decide⟩
    (prefixPartial 11 74929) = some ⟨11, 2, 0, 998962, 74929, 2541, 262144⟩ := by
  decide +kernel

theorem context_11_74929_998962 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74929 ⟨998962, by decide⟩ :=
  accepted_of_selected 11 74929 ⟨998962, by decide⟩ ⟨11, 2, 0, 998962, 74929, 2541, 262144⟩
    (by decide) selected_cut_37378

theorem selected_cut_37379 : selected 10 ⟨998983, by decide⟩
    (prefixPartial 11 74930) = some ⟨11, 2, 0, 998983, 74930, 1645, 262144⟩ := by
  decide +kernel

theorem context_11_74930_998983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74930 ⟨998983, by decide⟩ :=
  accepted_of_selected 11 74930 ⟨998983, by decide⟩ ⟨11, 2, 0, 998983, 74930, 1645, 262144⟩
    (by decide) selected_cut_37379

theorem selected_cut_37380 : selected 10 ⟨999009, by decide⟩
    (prefixPartial 11 74931) = some ⟨11, 2, 0, 999009, 74931, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_74931_999009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74931 ⟨999009, by decide⟩ :=
  accepted_of_selected 11 74931 ⟨999009, by decide⟩ ⟨11, 2, 0, 999009, 74931, 1805, 262144⟩
    (by decide) selected_cut_37380

theorem unmarked_context_10_18732_999010 : frontier 11 ⟨999010, by decide⟩
    (prefixCache 10 18732) (prefixPartial 10 18732) = false := by
  decide +kernel

theorem node_context_10_18732_999010 : EJMOriginalGlobalDAGData.nodes 11 ⟨999010, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨998962, by decide⟩,⟨998983, by decide⟩,⟨999009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18732_999010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18732 ⟨999010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18732
    ⟨999010, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨998962, by decide⟩,⟨998983, by decide⟩,⟨999009, by decide⟩]) unmarked_context_10_18732_999010 node_context_10_18732_999010
  intro a
  fin_cases a
  · exact context_11_74928_907917
  · exact context_11_74929_998962
  · exact context_11_74930_998983
  · exact context_11_74931_999009

theorem selected_cut_37381 : selected 10 ⟨999033, by decide⟩
    (prefixPartial 11 74932) = some ⟨11, 2, 0, 999033, 74932, 1781, 262144⟩ := by
  decide +kernel

theorem context_11_74932_999033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74932 ⟨999033, by decide⟩ :=
  accepted_of_selected 11 74932 ⟨999033, by decide⟩ ⟨11, 2, 0, 999033, 74932, 1781, 262144⟩
    (by decide) selected_cut_37381

theorem selected_cut_37382 : selected 10 ⟨999053, by decide⟩
    (prefixPartial 11 74933) = some ⟨11, 2, 0, 999053, 74933, 1581, 262144⟩ := by
  decide +kernel

theorem context_11_74933_999053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74933 ⟨999053, by decide⟩ :=
  accepted_of_selected 11 74933 ⟨999053, by decide⟩ ⟨11, 2, 0, 999053, 74933, 1581, 262144⟩
    (by decide) selected_cut_37382

theorem selected_cut_37383 : selected 10 ⟨999067, by decide⟩
    (prefixPartial 11 74934) = some ⟨11, 2, 0, 999067, 74934, 1097, 262144⟩ := by
  decide +kernel

theorem context_11_74934_999067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74934 ⟨999067, by decide⟩ :=
  accepted_of_selected 11 74934 ⟨999067, by decide⟩ ⟨11, 2, 0, 999067, 74934, 1097, 262144⟩
    (by decide) selected_cut_37383

theorem selected_cut_37384 : selected 10 ⟨999084, by decide⟩
    (prefixPartial 11 74935) = some ⟨11, 2, 0, 999084, 74935, 1233, 262144⟩ := by
  decide +kernel

theorem context_11_74935_999084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74935 ⟨999084, by decide⟩ :=
  accepted_of_selected 11 74935 ⟨999084, by decide⟩ ⟨11, 2, 0, 999084, 74935, 1233, 262144⟩
    (by decide) selected_cut_37384

theorem unmarked_context_10_18733_999085 : frontier 11 ⟨999085, by decide⟩
    (prefixCache 10 18733) (prefixPartial 10 18733) = false := by
  decide +kernel

theorem node_context_10_18733_999085 : EJMOriginalGlobalDAGData.nodes 11 ⟨999085, by decide⟩ =
    .split (coordinate 10) (![⟨999033, by decide⟩,⟨999053, by decide⟩,⟨999067, by decide⟩,⟨999084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18733_999085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18733 ⟨999085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18733
    ⟨999085, by decide⟩ (by decide) (![⟨999033, by decide⟩,⟨999053, by decide⟩,⟨999067, by decide⟩,⟨999084, by decide⟩]) unmarked_context_10_18733_999085 node_context_10_18733_999085
  intro a
  fin_cases a
  · exact context_11_74932_999033
  · exact context_11_74933_999053
  · exact context_11_74934_999067
  · exact context_11_74935_999084

theorem selected_cut_37385 : selected 11 ⟨999139, by decide⟩
    (prefixPartial 10 18734) = some ⟨10, 2, 0, 999139, 18734, 3209, 1048576⟩ := by
  decide +kernel

theorem context_10_18734_999139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18734 ⟨999139, by decide⟩ :=
  accepted_of_selected 10 18734 ⟨999139, by decide⟩ ⟨10, 2, 0, 999139, 18734, 3209, 1048576⟩
    (by decide) selected_cut_37385

theorem selected_cut_37386 : selected 11 ⟨999175, by decide⟩
    (prefixPartial 10 18735) = some ⟨10, 2, 0, 999175, 18735, 1177, 1048576⟩ := by
  decide +kernel

theorem context_10_18735_999175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18735 ⟨999175, by decide⟩ :=
  accepted_of_selected 10 18735 ⟨999175, by decide⟩ ⟨10, 2, 0, 999175, 18735, 1177, 1048576⟩
    (by decide) selected_cut_37386

theorem unmarked_context_9_4683_999176 : frontier 12 ⟨999176, by decide⟩
    (prefixCache 9 4683) (prefixPartial 9 4683) = false := by
  decide +kernel

theorem node_context_9_4683_999176 : EJMOriginalGlobalDAGData.nodes 12 ⟨999176, by decide⟩ =
    .split (coordinate 9) (![⟨999010, by decide⟩,⟨999085, by decide⟩,⟨999139, by decide⟩,⟨999175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4683_999176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4683 ⟨999176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4683
    ⟨999176, by decide⟩ (by decide) (![⟨999010, by decide⟩,⟨999085, by decide⟩,⟨999139, by decide⟩,⟨999175, by decide⟩]) unmarked_context_9_4683_999176 node_context_9_4683_999176
  intro a
  fin_cases a
  · exact context_10_18732_999010
  · exact context_10_18733_999085
  · exact context_10_18734_999139
  · exact context_10_18735_999175

theorem unmarked_context_8_1170_999177 : frontier 13 ⟨999177, by decide⟩
    (prefixCache 8 1170) (prefixPartial 8 1170) = false := by
  decide +kernel

theorem node_context_8_1170_999177 : EJMOriginalGlobalDAGData.nodes 13 ⟨999177, by decide⟩ =
    .split (coordinate 8) (![⟨997053, by decide⟩,⟨998292, by decide⟩,⟨998926, by decide⟩,⟨999176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1170_999177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1170 ⟨999177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1170
    ⟨999177, by decide⟩ (by decide) (![⟨997053, by decide⟩,⟨998292, by decide⟩,⟨998926, by decide⟩,⟨999176, by decide⟩]) unmarked_context_8_1170_999177 node_context_8_1170_999177
  intro a
  fin_cases a
  · exact context_9_4680_997053
  · exact context_9_4681_998292
  · exact context_9_4682_998926
  · exact context_9_4683_999176

theorem selected_cut_37387 : selected 10 ⟨167448, by decide⟩
    (prefixPartial 11 74944) = some ⟨11, 1, 0, 167448, 74944, 1, 262144⟩ := by
  decide +kernel

theorem context_11_74944_167448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74944 ⟨167448, by decide⟩ :=
  accepted_of_selected 11 74944 ⟨167448, by decide⟩ ⟨11, 1, 0, 167448, 74944, 1, 262144⟩
    (by decide) selected_cut_37387

theorem selected_cut_37388 : selected 8 ⟨999234, by decide⟩
    (prefixPartial 13 1199120) = some ⟨13, 2, 0, 999234, 1199120, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_1199120_999234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199120 ⟨999234, by decide⟩ :=
  accepted_of_selected 13 1199120 ⟨999234, by decide⟩ ⟨13, 2, 0, 999234, 1199120, 2233, 16384⟩
    (by decide) selected_cut_37388

theorem selected_cut_37389 : selected 8 ⟨999258, by decide⟩
    (prefixPartial 13 1199121) = some ⟨13, 2, 0, 999258, 1199121, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_1199121_999258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199121 ⟨999258, by decide⟩ :=
  accepted_of_selected 13 1199121 ⟨999258, by decide⟩ ⟨13, 2, 0, 999258, 1199121, 1361, 16384⟩
    (by decide) selected_cut_37389

theorem selected_cut_37390 : selected 8 ⟨999279, by decide⟩
    (prefixPartial 13 1199122) = some ⟨13, 2, 0, 999279, 1199122, 993, 16384⟩ := by
  decide +kernel

theorem context_13_1199122_999279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199122 ⟨999279, by decide⟩ :=
  accepted_of_selected 13 1199122 ⟨999279, by decide⟩ ⟨13, 2, 0, 999279, 1199122, 993, 16384⟩
    (by decide) selected_cut_37390

theorem selected_cut_37391 : selected 8 ⟨999283, by decide⟩
    (prefixPartial 13 1199123) = some ⟨13, 2, 0, 999283, 1199123, 521, 16384⟩ := by
  decide +kernel

theorem context_13_1199123_999283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199123 ⟨999283, by decide⟩ :=
  accepted_of_selected 13 1199123 ⟨999283, by decide⟩ ⟨13, 2, 0, 999283, 1199123, 521, 16384⟩
    (by decide) selected_cut_37391

theorem unmarked_context_12_299780_999284 : frontier 9 ⟨999284, by decide⟩
    (prefixCache 12 299780) (prefixPartial 12 299780) = false := by
  decide +kernel

theorem node_context_12_299780_999284 : EJMOriginalGlobalDAGData.nodes 9 ⟨999284, by decide⟩ =
    .split (coordinate 12) (![⟨999234, by decide⟩,⟨999258, by decide⟩,⟨999279, by decide⟩,⟨999283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299780_999284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299780 ⟨999284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299780
    ⟨999284, by decide⟩ (by decide) (![⟨999234, by decide⟩,⟨999258, by decide⟩,⟨999279, by decide⟩,⟨999283, by decide⟩]) unmarked_context_12_299780_999284 node_context_12_299780_999284
  intro a
  fin_cases a
  · exact context_13_1199120_999234
  · exact context_13_1199121_999258
  · exact context_13_1199122_999279
  · exact context_13_1199123_999283

theorem selected_cut_37392 : selected 8 ⟨999319, by decide⟩
    (prefixPartial 13 1199124) = some ⟨13, 2, 0, 999319, 1199124, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_1199124_999319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199124 ⟨999319, by decide⟩ :=
  accepted_of_selected 13 1199124 ⟨999319, by decide⟩ ⟨13, 2, 0, 999319, 1199124, 1797, 16384⟩
    (by decide) selected_cut_37392

theorem selected_cut_37393 : selected 8 ⟨999337, by decide⟩
    (prefixPartial 13 1199125) = some ⟨13, 2, 0, 999337, 1199125, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_1199125_999337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199125 ⟨999337, by decide⟩ :=
  accepted_of_selected 13 1199125 ⟨999337, by decide⟩ ⟨13, 2, 0, 999337, 1199125, 1333, 16384⟩
    (by decide) selected_cut_37393

theorem selected_cut_37394 : selected 8 ⟨999356, by decide⟩
    (prefixPartial 13 1199126) = some ⟨13, 2, 0, 999356, 1199126, 909, 16384⟩ := by
  decide +kernel

theorem context_13_1199126_999356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199126 ⟨999356, by decide⟩ :=
  accepted_of_selected 13 1199126 ⟨999356, by decide⟩ ⟨13, 2, 0, 999356, 1199126, 909, 16384⟩
    (by decide) selected_cut_37394

theorem selected_cut_37395 : selected 8 ⟨999359, by decide⟩
    (prefixPartial 13 1199127) = some ⟨13, 2, 0, 999359, 1199127, 509, 16384⟩ := by
  decide +kernel

theorem context_13_1199127_999359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199127 ⟨999359, by decide⟩ :=
  accepted_of_selected 13 1199127 ⟨999359, by decide⟩ ⟨13, 2, 0, 999359, 1199127, 509, 16384⟩
    (by decide) selected_cut_37395

theorem unmarked_context_12_299781_999360 : frontier 9 ⟨999360, by decide⟩
    (prefixCache 12 299781) (prefixPartial 12 299781) = false := by
  decide +kernel

theorem node_context_12_299781_999360 : EJMOriginalGlobalDAGData.nodes 9 ⟨999360, by decide⟩ =
    .split (coordinate 12) (![⟨999319, by decide⟩,⟨999337, by decide⟩,⟨999356, by decide⟩,⟨999359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299781_999360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299781 ⟨999360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299781
    ⟨999360, by decide⟩ (by decide) (![⟨999319, by decide⟩,⟨999337, by decide⟩,⟨999356, by decide⟩,⟨999359, by decide⟩]) unmarked_context_12_299781_999360 node_context_12_299781_999360
  intro a
  fin_cases a
  · exact context_13_1199124_999319
  · exact context_13_1199125_999337
  · exact context_13_1199126_999356
  · exact context_13_1199127_999359

theorem selected_cut_37396 : selected 8 ⟨999396, by decide⟩
    (prefixPartial 13 1199128) = some ⟨13, 2, 0, 999396, 1199128, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_1199128_999396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199128 ⟨999396, by decide⟩ :=
  accepted_of_selected 13 1199128 ⟨999396, by decide⟩ ⟨13, 2, 0, 999396, 1199128, 1625, 16384⟩
    (by decide) selected_cut_37396

theorem selected_cut_37397 : selected 8 ⟨999412, by decide⟩
    (prefixPartial 13 1199129) = some ⟨13, 2, 0, 999412, 1199129, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_1199129_999412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199129 ⟨999412, by decide⟩ :=
  accepted_of_selected 13 1199129 ⟨999412, by decide⟩ ⟨13, 2, 0, 999412, 1199129, 1153, 16384⟩
    (by decide) selected_cut_37397

theorem selected_cut_37398 : selected 8 ⟨999434, by decide⟩
    (prefixPartial 13 1199130) = some ⟨13, 2, 0, 999434, 1199130, 885, 16384⟩ := by
  decide +kernel

theorem context_13_1199130_999434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199130 ⟨999434, by decide⟩ :=
  accepted_of_selected 13 1199130 ⟨999434, by decide⟩ ⟨13, 2, 0, 999434, 1199130, 885, 16384⟩
    (by decide) selected_cut_37398

theorem selected_cut_37399 : selected 8 ⟨999439, by decide⟩
    (prefixPartial 13 1199131) = some ⟨13, 2, 0, 999439, 1199131, 521, 16384⟩ := by
  decide +kernel

theorem context_13_1199131_999439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199131 ⟨999439, by decide⟩ :=
  accepted_of_selected 13 1199131 ⟨999439, by decide⟩ ⟨13, 2, 0, 999439, 1199131, 521, 16384⟩
    (by decide) selected_cut_37399

theorem unmarked_context_12_299782_999440 : frontier 9 ⟨999440, by decide⟩
    (prefixCache 12 299782) (prefixPartial 12 299782) = false := by
  decide +kernel

theorem node_context_12_299782_999440 : EJMOriginalGlobalDAGData.nodes 9 ⟨999440, by decide⟩ =
    .split (coordinate 12) (![⟨999396, by decide⟩,⟨999412, by decide⟩,⟨999434, by decide⟩,⟨999439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299782_999440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299782 ⟨999440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299782
    ⟨999440, by decide⟩ (by decide) (![⟨999396, by decide⟩,⟨999412, by decide⟩,⟨999434, by decide⟩,⟨999439, by decide⟩]) unmarked_context_12_299782_999440 node_context_12_299782_999440
  intro a
  fin_cases a
  · exact context_13_1199128_999396
  · exact context_13_1199129_999412
  · exact context_13_1199130_999434
  · exact context_13_1199131_999439

theorem selected_cut_37400 : selected 8 ⟨999473, by decide⟩
    (prefixPartial 13 1199132) = some ⟨13, 2, 0, 999473, 1199132, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_1199132_999473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199132 ⟨999473, by decide⟩ :=
  accepted_of_selected 13 1199132 ⟨999473, by decide⟩ ⟨13, 2, 0, 999473, 1199132, 1653, 16384⟩
    (by decide) selected_cut_37400

theorem selected_cut_37401 : selected 8 ⟨999487, by decide⟩
    (prefixPartial 13 1199133) = some ⟨13, 2, 0, 999487, 1199133, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_1199133_999487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199133 ⟨999487, by decide⟩ :=
  accepted_of_selected 13 1199133 ⟨999487, by decide⟩ ⟨13, 2, 0, 999487, 1199133, 1181, 16384⟩
    (by decide) selected_cut_37401

theorem selected_cut_37402 : selected 8 ⟨999500, by decide⟩
    (prefixPartial 13 1199134) = some ⟨13, 2, 0, 999500, 1199134, 853, 16384⟩ := by
  decide +kernel

theorem context_13_1199134_999500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199134 ⟨999500, by decide⟩ :=
  accepted_of_selected 13 1199134 ⟨999500, by decide⟩ ⟨13, 2, 0, 999500, 1199134, 853, 16384⟩
    (by decide) selected_cut_37402

theorem selected_cut_37403 : selected 8 ⟨999504, by decide⟩
    (prefixPartial 13 1199135) = some ⟨13, 2, 0, 999504, 1199135, 509, 16384⟩ := by
  decide +kernel

theorem context_13_1199135_999504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199135 ⟨999504, by decide⟩ :=
  accepted_of_selected 13 1199135 ⟨999504, by decide⟩ ⟨13, 2, 0, 999504, 1199135, 509, 16384⟩
    (by decide) selected_cut_37403

theorem unmarked_context_12_299783_999505 : frontier 9 ⟨999505, by decide⟩
    (prefixCache 12 299783) (prefixPartial 12 299783) = false := by
  decide +kernel

theorem node_context_12_299783_999505 : EJMOriginalGlobalDAGData.nodes 9 ⟨999505, by decide⟩ =
    .split (coordinate 12) (![⟨999473, by decide⟩,⟨999487, by decide⟩,⟨999500, by decide⟩,⟨999504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299783_999505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299783 ⟨999505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299783
    ⟨999505, by decide⟩ (by decide) (![⟨999473, by decide⟩,⟨999487, by decide⟩,⟨999500, by decide⟩,⟨999504, by decide⟩]) unmarked_context_12_299783_999505 node_context_12_299783_999505
  intro a
  fin_cases a
  · exact context_13_1199132_999473
  · exact context_13_1199133_999487
  · exact context_13_1199134_999500
  · exact context_13_1199135_999504

theorem unmarked_context_11_74945_999506 : frontier 10 ⟨999506, by decide⟩
    (prefixCache 11 74945) (prefixPartial 11 74945) = false := by
  decide +kernel

theorem node_context_11_74945_999506 : EJMOriginalGlobalDAGData.nodes 10 ⟨999506, by decide⟩ =
    .split (coordinate 11) (![⟨999284, by decide⟩,⟨999360, by decide⟩,⟨999440, by decide⟩,⟨999505, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74945_999506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74945 ⟨999506, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74945
    ⟨999506, by decide⟩ (by decide) (![⟨999284, by decide⟩,⟨999360, by decide⟩,⟨999440, by decide⟩,⟨999505, by decide⟩]) unmarked_context_11_74945_999506 node_context_11_74945_999506
  intro a
  fin_cases a
  · exact context_12_299780_999284
  · exact context_12_299781_999360
  · exact context_12_299782_999440
  · exact context_12_299783_999505

theorem selected_cut_37404 : selected 8 ⟨999556, by decide⟩
    (prefixPartial 13 1199136) = some ⟨13, 2, 0, 999556, 1199136, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_1199136_999556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199136 ⟨999556, by decide⟩ :=
  accepted_of_selected 13 1199136 ⟨999556, by decide⟩ ⟨13, 2, 0, 999556, 1199136, 2221, 16384⟩
    (by decide) selected_cut_37404

theorem selected_cut_37405 : selected 8 ⟨999578, by decide⟩
    (prefixPartial 13 1199137) = some ⟨13, 2, 0, 999578, 1199137, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_1199137_999578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199137 ⟨999578, by decide⟩ :=
  accepted_of_selected 13 1199137 ⟨999578, by decide⟩ ⟨13, 2, 0, 999578, 1199137, 1485, 16384⟩
    (by decide) selected_cut_37405

theorem selected_cut_37406 : selected 8 ⟨999597, by decide⟩
    (prefixPartial 13 1199138) = some ⟨13, 2, 0, 999597, 1199138, 945, 16384⟩ := by
  decide +kernel

theorem context_13_1199138_999597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199138 ⟨999597, by decide⟩ :=
  accepted_of_selected 13 1199138 ⟨999597, by decide⟩ ⟨13, 2, 0, 999597, 1199138, 945, 16384⟩
    (by decide) selected_cut_37406

theorem selected_cut_37407 : selected 8 ⟨999602, by decide⟩
    (prefixPartial 13 1199139) = some ⟨13, 2, 0, 999602, 1199139, 565, 16384⟩ := by
  decide +kernel

theorem context_13_1199139_999602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199139 ⟨999602, by decide⟩ :=
  accepted_of_selected 13 1199139 ⟨999602, by decide⟩ ⟨13, 2, 0, 999602, 1199139, 565, 16384⟩
    (by decide) selected_cut_37407

theorem unmarked_context_12_299784_999603 : frontier 9 ⟨999603, by decide⟩
    (prefixCache 12 299784) (prefixPartial 12 299784) = false := by
  decide +kernel

theorem node_context_12_299784_999603 : EJMOriginalGlobalDAGData.nodes 9 ⟨999603, by decide⟩ =
    .split (coordinate 12) (![⟨999556, by decide⟩,⟨999578, by decide⟩,⟨999597, by decide⟩,⟨999602, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299784_999603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299784 ⟨999603, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299784
    ⟨999603, by decide⟩ (by decide) (![⟨999556, by decide⟩,⟨999578, by decide⟩,⟨999597, by decide⟩,⟨999602, by decide⟩]) unmarked_context_12_299784_999603 node_context_12_299784_999603
  intro a
  fin_cases a
  · exact context_13_1199136_999556
  · exact context_13_1199137_999578
  · exact context_13_1199138_999597
  · exact context_13_1199139_999602

theorem selected_cut_37408 : selected 8 ⟨999651, by decide⟩
    (prefixPartial 13 1199140) = some ⟨13, 2, 0, 999651, 1199140, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_1199140_999651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199140 ⟨999651, by decide⟩ :=
  accepted_of_selected 13 1199140 ⟨999651, by decide⟩ ⟨13, 2, 0, 999651, 1199140, 1909, 16384⟩
    (by decide) selected_cut_37408

theorem selected_cut_37409 : selected 8 ⟨999674, by decide⟩
    (prefixPartial 13 1199141) = some ⟨13, 2, 0, 999674, 1199141, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_1199141_999674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199141 ⟨999674, by decide⟩ :=
  accepted_of_selected 13 1199141 ⟨999674, by decide⟩ ⟨13, 2, 0, 999674, 1199141, 1441, 16384⟩
    (by decide) selected_cut_37409

theorem selected_cut_37410 : selected 8 ⟨999691, by decide⟩
    (prefixPartial 13 1199142) = some ⟨13, 2, 0, 999691, 1199142, 841, 16384⟩ := by
  decide +kernel

theorem context_13_1199142_999691 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199142 ⟨999691, by decide⟩ :=
  accepted_of_selected 13 1199142 ⟨999691, by decide⟩ ⟨13, 2, 0, 999691, 1199142, 841, 16384⟩
    (by decide) selected_cut_37410

theorem selected_cut_37411 : selected 8 ⟨999695, by decide⟩
    (prefixPartial 13 1199143) = some ⟨13, 2, 0, 999695, 1199143, 553, 16384⟩ := by
  decide +kernel

theorem context_13_1199143_999695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199143 ⟨999695, by decide⟩ :=
  accepted_of_selected 13 1199143 ⟨999695, by decide⟩ ⟨13, 2, 0, 999695, 1199143, 553, 16384⟩
    (by decide) selected_cut_37411

theorem unmarked_context_12_299785_999696 : frontier 9 ⟨999696, by decide⟩
    (prefixCache 12 299785) (prefixPartial 12 299785) = false := by
  decide +kernel

theorem node_context_12_299785_999696 : EJMOriginalGlobalDAGData.nodes 9 ⟨999696, by decide⟩ =
    .split (coordinate 12) (![⟨999651, by decide⟩,⟨999674, by decide⟩,⟨999691, by decide⟩,⟨999695, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299785_999696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299785 ⟨999696, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299785
    ⟨999696, by decide⟩ (by decide) (![⟨999651, by decide⟩,⟨999674, by decide⟩,⟨999691, by decide⟩,⟨999695, by decide⟩]) unmarked_context_12_299785_999696 node_context_12_299785_999696
  intro a
  fin_cases a
  · exact context_13_1199140_999651
  · exact context_13_1199141_999674
  · exact context_13_1199142_999691
  · exact context_13_1199143_999695

theorem selected_cut_37412 : selected 9 ⟨999765, by decide⟩
    (prefixPartial 12 299786) = some ⟨12, 2, 0, 999765, 299786, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_299786_999765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299786 ⟨999765, by decide⟩ :=
  accepted_of_selected 12 299786 ⟨999765, by decide⟩ ⟨12, 2, 0, 999765, 299786, 4077, 65536⟩
    (by decide) selected_cut_37412

theorem selected_cut_37413 : selected 8 ⟨999807, by decide⟩
    (prefixPartial 13 1199148) = some ⟨13, 2, 0, 999807, 1199148, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_1199148_999807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199148 ⟨999807, by decide⟩ :=
  accepted_of_selected 13 1199148 ⟨999807, by decide⟩ ⟨13, 2, 0, 999807, 1199148, 1897, 16384⟩
    (by decide) selected_cut_37413

theorem selected_cut_37414 : selected 8 ⟨999825, by decide⟩
    (prefixPartial 13 1199149) = some ⟨13, 2, 0, 999825, 1199149, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_1199149_999825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199149 ⟨999825, by decide⟩ :=
  accepted_of_selected 13 1199149 ⟨999825, by decide⟩ ⟨13, 2, 0, 999825, 1199149, 1317, 16384⟩
    (by decide) selected_cut_37414

theorem selected_cut_37415 : selected 8 ⟨999843, by decide⟩
    (prefixPartial 13 1199150) = some ⟨13, 2, 0, 999843, 1199150, 801, 16384⟩ := by
  decide +kernel

theorem context_13_1199150_999843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199150 ⟨999843, by decide⟩ :=
  accepted_of_selected 13 1199150 ⟨999843, by decide⟩ ⟨13, 2, 0, 999843, 1199150, 801, 16384⟩
    (by decide) selected_cut_37415

theorem selected_cut_37416 : selected 8 ⟨999848, by decide⟩
    (prefixPartial 13 1199151) = some ⟨13, 2, 0, 999848, 1199151, 569, 16384⟩ := by
  decide +kernel

theorem context_13_1199151_999848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199151 ⟨999848, by decide⟩ :=
  accepted_of_selected 13 1199151 ⟨999848, by decide⟩ ⟨13, 2, 0, 999848, 1199151, 569, 16384⟩
    (by decide) selected_cut_37416

theorem unmarked_context_12_299787_999849 : frontier 9 ⟨999849, by decide⟩
    (prefixCache 12 299787) (prefixPartial 12 299787) = false := by
  decide +kernel

theorem node_context_12_299787_999849 : EJMOriginalGlobalDAGData.nodes 9 ⟨999849, by decide⟩ =
    .split (coordinate 12) (![⟨999807, by decide⟩,⟨999825, by decide⟩,⟨999843, by decide⟩,⟨999848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299787_999849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299787 ⟨999849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299787
    ⟨999849, by decide⟩ (by decide) (![⟨999807, by decide⟩,⟨999825, by decide⟩,⟨999843, by decide⟩,⟨999848, by decide⟩]) unmarked_context_12_299787_999849 node_context_12_299787_999849
  intro a
  fin_cases a
  · exact context_13_1199148_999807
  · exact context_13_1199149_999825
  · exact context_13_1199150_999843
  · exact context_13_1199151_999848

theorem unmarked_context_11_74946_999850 : frontier 10 ⟨999850, by decide⟩
    (prefixCache 11 74946) (prefixPartial 11 74946) = false := by
  decide +kernel

theorem node_context_11_74946_999850 : EJMOriginalGlobalDAGData.nodes 10 ⟨999850, by decide⟩ =
    .split (coordinate 11) (![⟨999603, by decide⟩,⟨999696, by decide⟩,⟨999765, by decide⟩,⟨999849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74946_999850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74946 ⟨999850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74946
    ⟨999850, by decide⟩ (by decide) (![⟨999603, by decide⟩,⟨999696, by decide⟩,⟨999765, by decide⟩,⟨999849, by decide⟩]) unmarked_context_11_74946_999850 node_context_11_74946_999850
  intro a
  fin_cases a
  · exact context_12_299784_999603
  · exact context_12_299785_999696
  · exact context_12_299786_999765
  · exact context_12_299787_999849

theorem selected_cut_37417 : selected 8 ⟨999894, by decide⟩
    (prefixPartial 13 1199152) = some ⟨13, 2, 0, 999894, 1199152, 1921, 16384⟩ := by
  decide +kernel

theorem context_13_1199152_999894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199152 ⟨999894, by decide⟩ :=
  accepted_of_selected 13 1199152 ⟨999894, by decide⟩ ⟨13, 2, 0, 999894, 1199152, 1921, 16384⟩
    (by decide) selected_cut_37417

theorem selected_cut_37418 : selected 8 ⟨999916, by decide⟩
    (prefixPartial 13 1199153) = some ⟨13, 2, 0, 999916, 1199153, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_1199153_999916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199153 ⟨999916, by decide⟩ :=
  accepted_of_selected 13 1199153 ⟨999916, by decide⟩ ⟨13, 2, 0, 999916, 1199153, 1377, 16384⟩
    (by decide) selected_cut_37418

theorem selected_cut_37419 : selected 8 ⟨999930, by decide⟩
    (prefixPartial 13 1199154) = some ⟨13, 2, 0, 999930, 1199154, 837, 16384⟩ := by
  decide +kernel

theorem context_13_1199154_999930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199154 ⟨999930, by decide⟩ :=
  accepted_of_selected 13 1199154 ⟨999930, by decide⟩ ⟨13, 2, 0, 999930, 1199154, 837, 16384⟩
    (by decide) selected_cut_37419

theorem selected_cut_37420 : selected 8 ⟨999936, by decide⟩
    (prefixPartial 13 1199155) = some ⟨13, 2, 0, 999936, 1199155, 597, 16384⟩ := by
  decide +kernel

theorem context_13_1199155_999936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199155 ⟨999936, by decide⟩ :=
  accepted_of_selected 13 1199155 ⟨999936, by decide⟩ ⟨13, 2, 0, 999936, 1199155, 597, 16384⟩
    (by decide) selected_cut_37420

theorem unmarked_context_12_299788_999937 : frontier 9 ⟨999937, by decide⟩
    (prefixCache 12 299788) (prefixPartial 12 299788) = false := by
  decide +kernel

theorem node_context_12_299788_999937 : EJMOriginalGlobalDAGData.nodes 9 ⟨999937, by decide⟩ =
    .split (coordinate 12) (![⟨999894, by decide⟩,⟨999916, by decide⟩,⟨999930, by decide⟩,⟨999936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299788_999937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299788 ⟨999937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299788
    ⟨999937, by decide⟩ (by decide) (![⟨999894, by decide⟩,⟨999916, by decide⟩,⟨999930, by decide⟩,⟨999936, by decide⟩]) unmarked_context_12_299788_999937 node_context_12_299788_999937
  intro a
  fin_cases a
  · exact context_13_1199152_999894
  · exact context_13_1199153_999916
  · exact context_13_1199154_999930
  · exact context_13_1199155_999936

theorem selected_cut_37421 : selected 8 ⟨999972, by decide⟩
    (prefixPartial 13 1199156) = some ⟨13, 2, 0, 999972, 1199156, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_1199156_999972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199156 ⟨999972, by decide⟩ :=
  accepted_of_selected 13 1199156 ⟨999972, by decide⟩ ⟨13, 2, 0, 999972, 1199156, 1785, 16384⟩
    (by decide) selected_cut_37421

theorem selected_cut_37422 : selected 8 ⟨999992, by decide⟩
    (prefixPartial 13 1199157) = some ⟨13, 2, 0, 999992, 1199157, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_1199157_999992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199157 ⟨999992, by decide⟩ :=
  accepted_of_selected 13 1199157 ⟨999992, by decide⟩ ⟨13, 2, 0, 999992, 1199157, 1457, 16384⟩
    (by decide) selected_cut_37422

theorem selected_cut_37423 : selected 8 ⟨1000010, by decide⟩
    (prefixPartial 13 1199158) = some ⟨13, 2, 0, 1000010, 1199158, 873, 16384⟩ := by
  decide +kernel

theorem context_13_1199158_1000010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199158 ⟨1000010, by decide⟩ :=
  accepted_of_selected 13 1199158 ⟨1000010, by decide⟩ ⟨13, 2, 0, 1000010, 1199158, 873, 16384⟩
    (by decide) selected_cut_37423

theorem selected_cut_37424 : selected 8 ⟨1000015, by decide⟩
    (prefixPartial 13 1199159) = some ⟨13, 2, 0, 1000015, 1199159, 585, 16384⟩ := by
  decide +kernel

theorem context_13_1199159_1000015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199159 ⟨1000015, by decide⟩ :=
  accepted_of_selected 13 1199159 ⟨1000015, by decide⟩ ⟨13, 2, 0, 1000015, 1199159, 585, 16384⟩
    (by decide) selected_cut_37424

theorem unmarked_context_12_299789_1000016 : frontier 9 ⟨1000016, by decide⟩
    (prefixCache 12 299789) (prefixPartial 12 299789) = false := by
  decide +kernel

theorem node_context_12_299789_1000016 : EJMOriginalGlobalDAGData.nodes 9 ⟨1000016, by decide⟩ =
    .split (coordinate 12) (![⟨999972, by decide⟩,⟨999992, by decide⟩,⟨1000010, by decide⟩,⟨1000015, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299789_1000016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299789 ⟨1000016, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299789
    ⟨1000016, by decide⟩ (by decide) (![⟨999972, by decide⟩,⟨999992, by decide⟩,⟨1000010, by decide⟩,⟨1000015, by decide⟩]) unmarked_context_12_299789_1000016 node_context_12_299789_1000016
  intro a
  fin_cases a
  · exact context_13_1199156_999972
  · exact context_13_1199157_999992
  · exact context_13_1199158_1000010
  · exact context_13_1199159_1000015

theorem selected_cut_37425 : selected 8 ⟨1000045, by decide⟩
    (prefixPartial 13 1199160) = some ⟨13, 2, 0, 1000045, 1199160, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_1199160_1000045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199160 ⟨1000045, by decide⟩ :=
  accepted_of_selected 13 1199160 ⟨1000045, by decide⟩ ⟨13, 2, 0, 1000045, 1199160, 1517, 16384⟩
    (by decide) selected_cut_37425

theorem selected_cut_37426 : selected 8 ⟨1000063, by decide⟩
    (prefixPartial 13 1199161) = some ⟨13, 2, 0, 1000063, 1199161, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_1199161_1000063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199161 ⟨1000063, by decide⟩ :=
  accepted_of_selected 13 1199161 ⟨1000063, by decide⟩ ⟨13, 2, 0, 1000063, 1199161, 1177, 16384⟩
    (by decide) selected_cut_37426

theorem selected_cut_37427 : selected 8 ⟨1000079, by decide⟩
    (prefixPartial 13 1199162) = some ⟨13, 2, 0, 1000079, 1199162, 909, 16384⟩ := by
  decide +kernel

theorem context_13_1199162_1000079 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199162 ⟨1000079, by decide⟩ :=
  accepted_of_selected 13 1199162 ⟨1000079, by decide⟩ ⟨13, 2, 0, 1000079, 1199162, 909, 16384⟩
    (by decide) selected_cut_37427

theorem selected_cut_37428 : selected 8 ⟨1000085, by decide⟩
    (prefixPartial 13 1199163) = some ⟨13, 2, 0, 1000085, 1199163, 597, 16384⟩ := by
  decide +kernel

theorem context_13_1199163_1000085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199163 ⟨1000085, by decide⟩ :=
  accepted_of_selected 13 1199163 ⟨1000085, by decide⟩ ⟨13, 2, 0, 1000085, 1199163, 597, 16384⟩
    (by decide) selected_cut_37428

theorem unmarked_context_12_299790_1000086 : frontier 9 ⟨1000086, by decide⟩
    (prefixCache 12 299790) (prefixPartial 12 299790) = false := by
  decide +kernel

theorem node_context_12_299790_1000086 : EJMOriginalGlobalDAGData.nodes 9 ⟨1000086, by decide⟩ =
    .split (coordinate 12) (![⟨1000045, by decide⟩,⟨1000063, by decide⟩,⟨1000079, by decide⟩,⟨1000085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299790_1000086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299790 ⟨1000086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299790
    ⟨1000086, by decide⟩ (by decide) (![⟨1000045, by decide⟩,⟨1000063, by decide⟩,⟨1000079, by decide⟩,⟨1000085, by decide⟩]) unmarked_context_12_299790_1000086 node_context_12_299790_1000086
  intro a
  fin_cases a
  · exact context_13_1199160_1000045
  · exact context_13_1199161_1000063
  · exact context_13_1199162_1000079
  · exact context_13_1199163_1000085

theorem selected_cut_37429 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 299791) = some ⟨12, 1, 0, 903806, 299791, 1, 65536⟩ := by
  decide +kernel

theorem context_12_299791_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299791 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 299791 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 299791, 1, 65536⟩
    (by decide) selected_cut_37429

theorem unmarked_context_11_74947_1000087 : frontier 10 ⟨1000087, by decide⟩
    (prefixCache 11 74947) (prefixPartial 11 74947) = false := by
  decide +kernel

theorem node_context_11_74947_1000087 : EJMOriginalGlobalDAGData.nodes 10 ⟨1000087, by decide⟩ =
    .split (coordinate 11) (![⟨999937, by decide⟩,⟨1000016, by decide⟩,⟨1000086, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74947_1000087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74947 ⟨1000087, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74947
    ⟨1000087, by decide⟩ (by decide) (![⟨999937, by decide⟩,⟨1000016, by decide⟩,⟨1000086, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_74947_1000087 node_context_11_74947_1000087
  intro a
  fin_cases a
  · exact context_12_299788_999937
  · exact context_12_299789_1000016
  · exact context_12_299790_1000086
  · exact context_12_299791_903806

theorem unmarked_context_10_18736_1000088 : frontier 11 ⟨1000088, by decide⟩
    (prefixCache 10 18736) (prefixPartial 10 18736) = false := by
  decide +kernel

theorem node_context_10_18736_1000088 : EJMOriginalGlobalDAGData.nodes 11 ⟨1000088, by decide⟩ =
    .split (coordinate 10) (![⟨167448, by decide⟩,⟨999506, by decide⟩,⟨999850, by decide⟩,⟨1000087, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18736_1000088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18736 ⟨1000088, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18736
    ⟨1000088, by decide⟩ (by decide) (![⟨167448, by decide⟩,⟨999506, by decide⟩,⟨999850, by decide⟩,⟨1000087, by decide⟩]) unmarked_context_10_18736_1000088 node_context_10_18736_1000088
  intro a
  fin_cases a
  · exact context_11_74944_167448
  · exact context_11_74945_999506
  · exact context_11_74946_999850
  · exact context_11_74947_1000087

theorem selected_cut_37430 : selected 9 ⟨1000153, by decide⟩
    (prefixPartial 12 299792) = some ⟨12, 2, 0, 1000153, 299792, 3297, 65536⟩ := by
  decide +kernel

theorem context_12_299792_1000153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299792 ⟨1000153, by decide⟩ :=
  accepted_of_selected 12 299792 ⟨1000153, by decide⟩ ⟨12, 2, 0, 1000153, 299792, 3297, 65536⟩
    (by decide) selected_cut_37430

theorem selected_cut_37431 : selected 9 ⟨1000203, by decide⟩
    (prefixPartial 12 299793) = some ⟨12, 2, 0, 1000203, 299793, 3117, 65536⟩ := by
  decide +kernel

theorem context_12_299793_1000203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299793 ⟨1000203, by decide⟩ :=
  accepted_of_selected 12 299793 ⟨1000203, by decide⟩ ⟨12, 2, 0, 1000203, 299793, 3117, 65536⟩
    (by decide) selected_cut_37431

theorem selected_cut_37432 : selected 9 ⟨1000244, by decide⟩
    (prefixPartial 12 299794) = some ⟨12, 2, 0, 1000244, 299794, 3061, 65536⟩ := by
  decide +kernel

theorem context_12_299794_1000244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299794 ⟨1000244, by decide⟩ :=
  accepted_of_selected 12 299794 ⟨1000244, by decide⟩ ⟨12, 2, 0, 1000244, 299794, 3061, 65536⟩
    (by decide) selected_cut_37432

theorem selected_cut_37433 : selected 9 ⟨1000282, by decide⟩
    (prefixPartial 12 299795) = some ⟨12, 2, 0, 1000282, 299795, 2977, 65536⟩ := by
  decide +kernel

theorem context_12_299795_1000282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299795 ⟨1000282, by decide⟩ :=
  accepted_of_selected 12 299795 ⟨1000282, by decide⟩ ⟨12, 2, 0, 1000282, 299795, 2977, 65536⟩
    (by decide) selected_cut_37433

theorem unmarked_context_11_74948_1000283 : frontier 10 ⟨1000283, by decide⟩
    (prefixCache 11 74948) (prefixPartial 11 74948) = false := by
  decide +kernel

theorem node_context_11_74948_1000283 : EJMOriginalGlobalDAGData.nodes 10 ⟨1000283, by decide⟩ =
    .split (coordinate 11) (![⟨1000153, by decide⟩,⟨1000203, by decide⟩,⟨1000244, by decide⟩,⟨1000282, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74948_1000283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74948 ⟨1000283, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74948
    ⟨1000283, by decide⟩ (by decide) (![⟨1000153, by decide⟩,⟨1000203, by decide⟩,⟨1000244, by decide⟩,⟨1000282, by decide⟩]) unmarked_context_11_74948_1000283 node_context_11_74948_1000283
  intro a
  fin_cases a
  · exact context_12_299792_1000153
  · exact context_12_299793_1000203
  · exact context_12_299794_1000244
  · exact context_12_299795_1000282

theorem selected_cut_37434 : selected 8 ⟨1000330, by decide⟩
    (prefixPartial 13 1199184) = some ⟨13, 2, 0, 1000330, 1199184, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_1199184_1000330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199184 ⟨1000330, by decide⟩ :=
  accepted_of_selected 13 1199184 ⟨1000330, by decide⟩ ⟨13, 2, 0, 1000330, 1199184, 1897, 16384⟩
    (by decide) selected_cut_37434

theorem selected_cut_37435 : selected 8 ⟨1000346, by decide⟩
    (prefixPartial 13 1199185) = some ⟨13, 2, 0, 1000346, 1199185, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_1199185_1000346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199185 ⟨1000346, by decide⟩ :=
  accepted_of_selected 13 1199185 ⟨1000346, by decide⟩ ⟨13, 2, 0, 1000346, 1199185, 1125, 16384⟩
    (by decide) selected_cut_37435

theorem selected_cut_37436 : selected 8 ⟨1000364, by decide⟩
    (prefixPartial 13 1199186) = some ⟨13, 2, 0, 1000364, 1199186, 837, 16384⟩ := by
  decide +kernel

theorem context_13_1199186_1000364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199186 ⟨1000364, by decide⟩ :=
  accepted_of_selected 13 1199186 ⟨1000364, by decide⟩ ⟨13, 2, 0, 1000364, 1199186, 837, 16384⟩
    (by decide) selected_cut_37436

theorem selected_cut_37437 : selected 8 ⟨1000369, by decide⟩
    (prefixPartial 13 1199187) = some ⟨13, 2, 0, 1000369, 1199187, 477, 16384⟩ := by
  decide +kernel

theorem context_13_1199187_1000369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199187 ⟨1000369, by decide⟩ :=
  accepted_of_selected 13 1199187 ⟨1000369, by decide⟩ ⟨13, 2, 0, 1000369, 1199187, 477, 16384⟩
    (by decide) selected_cut_37437

theorem unmarked_context_12_299796_1000370 : frontier 9 ⟨1000370, by decide⟩
    (prefixCache 12 299796) (prefixPartial 12 299796) = false := by
  decide +kernel

theorem node_context_12_299796_1000370 : EJMOriginalGlobalDAGData.nodes 9 ⟨1000370, by decide⟩ =
    .split (coordinate 12) (![⟨1000330, by decide⟩,⟨1000346, by decide⟩,⟨1000364, by decide⟩,⟨1000369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_299796_1000370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299796 ⟨1000370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 299796
    ⟨1000370, by decide⟩ (by decide) (![⟨1000330, by decide⟩,⟨1000346, by decide⟩,⟨1000364, by decide⟩,⟨1000369, by decide⟩]) unmarked_context_12_299796_1000370 node_context_12_299796_1000370
  intro a
  fin_cases a
  · exact context_13_1199184_1000330
  · exact context_13_1199185_1000346
  · exact context_13_1199186_1000364
  · exact context_13_1199187_1000369

theorem selected_cut_37438 : selected 9 ⟨1000516, by decide⟩
    (prefixPartial 12 299797) = some ⟨12, 2, 0, 1000516, 299797, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_299797_1000516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299797 ⟨1000516, by decide⟩ :=
  accepted_of_selected 12 299797 ⟨1000516, by decide⟩ ⟨12, 2, 0, 1000516, 299797, 2405, 65536⟩
    (by decide) selected_cut_37438

theorem selected_cut_37439 : selected 9 ⟨1000572, by decide⟩
    (prefixPartial 12 299798) = some ⟨12, 2, 0, 1000572, 299798, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_299798_1000572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299798 ⟨1000572, by decide⟩ :=
  accepted_of_selected 12 299798 ⟨1000572, by decide⟩ ⟨12, 2, 0, 1000572, 299798, 3637, 65536⟩
    (by decide) selected_cut_37439

theorem selected_cut_37440 : selected 9 ⟨1000622, by decide⟩
    (prefixPartial 12 299799) = some ⟨12, 2, 0, 1000622, 299799, 3601, 65536⟩ := by
  decide +kernel

theorem context_12_299799_1000622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 299799 ⟨1000622, by decide⟩ :=
  accepted_of_selected 12 299799 ⟨1000622, by decide⟩ ⟨12, 2, 0, 1000622, 299799, 3601, 65536⟩
    (by decide) selected_cut_37440

theorem unmarked_context_11_74949_1000623 : frontier 10 ⟨1000623, by decide⟩
    (prefixCache 11 74949) (prefixPartial 11 74949) = false := by
  decide +kernel

theorem node_context_11_74949_1000623 : EJMOriginalGlobalDAGData.nodes 10 ⟨1000623, by decide⟩ =
    .split (coordinate 11) (![⟨1000370, by decide⟩,⟨1000516, by decide⟩,⟨1000572, by decide⟩,⟨1000622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_74949_1000623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 74949 ⟨1000623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 74949
    ⟨1000623, by decide⟩ (by decide) (![⟨1000370, by decide⟩,⟨1000516, by decide⟩,⟨1000572, by decide⟩,⟨1000622, by decide⟩]) unmarked_context_11_74949_1000623 node_context_11_74949_1000623
  intro a
  fin_cases a
  · exact context_12_299796_1000370
  · exact context_12_299797_1000516
  · exact context_12_299798_1000572
  · exact context_12_299799_1000622

theorem selected_cut_37441 : selected 8 ⟨1000655, by decide⟩
    (prefixPartial 13 1199200) = some ⟨13, 2, 0, 1000655, 1199200, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_1199200_1000655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199200 ⟨1000655, by decide⟩ :=
  accepted_of_selected 13 1199200 ⟨1000655, by decide⟩ ⟨13, 2, 0, 1000655, 1199200, 1617, 16384⟩
    (by decide) selected_cut_37441

theorem selected_cut_37442 : selected 8 ⟨1000673, by decide⟩
    (prefixPartial 13 1199201) = some ⟨13, 2, 0, 1000673, 1199201, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_1199201_1000673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 1199201 ⟨1000673, by decide⟩ :=
  accepted_of_selected 13 1199201 ⟨1000673, by decide⟩ ⟨13, 2, 0, 1000673, 1199201, 1297, 16384⟩
    (by decide) selected_cut_37442

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
