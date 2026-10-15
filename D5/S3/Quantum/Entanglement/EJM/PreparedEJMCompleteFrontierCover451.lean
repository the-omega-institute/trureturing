/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover450
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_43300 : selected 9 ⟨1184829, by decide⟩
    (prefixPartial 12 339766) = some ⟨12, 2, 0, 1184829, 339766, 2561, 65536⟩ := by
  decide +kernel

theorem context_12_339766_1184829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339766 ⟨1184829, by decide⟩ :=
  accepted_of_selected 12 339766 ⟨1184829, by decide⟩ ⟨12, 2, 0, 1184829, 339766, 2561, 65536⟩
    (by decide) selected_cut_43300

theorem selected_cut_43301 : selected 9 ⟨1184878, by decide⟩
    (prefixPartial 12 339767) = some ⟨12, 2, 0, 1184878, 339767, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_339767_1184878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339767 ⟨1184878, by decide⟩ :=
  accepted_of_selected 12 339767 ⟨1184878, by decide⟩ ⟨12, 2, 0, 1184878, 339767, 2853, 65536⟩
    (by decide) selected_cut_43301

theorem unmarked_context_11_84941_1184879 : frontier 10 ⟨1184879, by decide⟩
    (prefixCache 11 84941) (prefixPartial 11 84941) = false := by
  decide +kernel

theorem node_context_11_84941_1184879 : EJMOriginalGlobalDAGData.nodes 10 ⟨1184879, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1184778, by decide⟩,⟨1184829, by decide⟩,⟨1184878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84941_1184879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84941 ⟨1184879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84941
    ⟨1184879, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1184778, by decide⟩,⟨1184829, by decide⟩,⟨1184878, by decide⟩]) unmarked_context_11_84941_1184879 node_context_11_84941_1184879
  intro a
  fin_cases a
  · exact context_12_339764_1108174
  · exact context_12_339765_1184778
  · exact context_12_339766_1184829
  · exact context_12_339767_1184878

theorem selected_cut_43302 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339768) = some ⟨12, 1, 0, 1108174, 339768, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339768_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339768 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339768 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339768, 1, 65536⟩
    (by decide) selected_cut_43302

theorem selected_cut_43303 : selected 9 ⟨1184926, by decide⟩
    (prefixPartial 12 339769) = some ⟨12, 2, 0, 1184926, 339769, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_339769_1184926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339769 ⟨1184926, by decide⟩ :=
  accepted_of_selected 12 339769 ⟨1184926, by decide⟩ ⟨12, 2, 0, 1184926, 339769, 2505, 65536⟩
    (by decide) selected_cut_43303

theorem selected_cut_43304 : selected 9 ⟨1184964, by decide⟩
    (prefixPartial 12 339770) = some ⟨12, 2, 0, 1184964, 339770, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_339770_1184964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339770 ⟨1184964, by decide⟩ :=
  accepted_of_selected 12 339770 ⟨1184964, by decide⟩ ⟨12, 2, 0, 1184964, 339770, 2185, 65536⟩
    (by decide) selected_cut_43304

theorem selected_cut_43305 : selected 9 ⟨1185005, by decide⟩
    (prefixPartial 12 339771) = some ⟨12, 2, 0, 1185005, 339771, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_339771_1185005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339771 ⟨1185005, by decide⟩ :=
  accepted_of_selected 12 339771 ⟨1185005, by decide⟩ ⟨12, 2, 0, 1185005, 339771, 2497, 65536⟩
    (by decide) selected_cut_43305

theorem unmarked_context_11_84942_1185006 : frontier 10 ⟨1185006, by decide⟩
    (prefixCache 11 84942) (prefixPartial 11 84942) = false := by
  decide +kernel

theorem node_context_11_84942_1185006 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185006, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1184926, by decide⟩,⟨1184964, by decide⟩,⟨1185005, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84942_1185006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84942 ⟨1185006, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84942
    ⟨1185006, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1184926, by decide⟩,⟨1184964, by decide⟩,⟨1185005, by decide⟩]) unmarked_context_11_84942_1185006 node_context_11_84942_1185006
  intro a
  fin_cases a
  · exact context_12_339768_1108174
  · exact context_12_339769_1184926
  · exact context_12_339770_1184964
  · exact context_12_339771_1185005

theorem selected_cut_43306 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84943) = some ⟨11, 1, 0, 977886, 84943, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84943_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84943 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84943 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84943, 1, 262144⟩
    (by decide) selected_cut_43306

theorem unmarked_context_10_21235_1185007 : frontier 11 ⟨1185007, by decide⟩
    (prefixCache 10 21235) (prefixPartial 10 21235) = false := by
  decide +kernel

theorem node_context_10_21235_1185007 : EJMOriginalGlobalDAGData.nodes 11 ⟨1185007, by decide⟩ =
    .split (coordinate 10) (![⟨1184731, by decide⟩,⟨1184879, by decide⟩,⟨1185006, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21235_1185007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21235 ⟨1185007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21235
    ⟨1185007, by decide⟩ (by decide) (![⟨1184731, by decide⟩,⟨1184879, by decide⟩,⟨1185006, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21235_1185007 node_context_10_21235_1185007
  intro a
  fin_cases a
  · exact context_11_84940_1184731
  · exact context_11_84941_1184879
  · exact context_11_84942_1185006
  · exact context_11_84943_977886

theorem unmarked_context_9_5308_1185008 : frontier 12 ⟨1185008, by decide⟩
    (prefixCache 9 5308) (prefixPartial 9 5308) = false := by
  decide +kernel

theorem node_context_9_5308_1185008 : EJMOriginalGlobalDAGData.nodes 12 ⟨1185008, by decide⟩ =
    .split (coordinate 9) (![⟨1183266, by decide⟩,⟨1183925, by decide⟩,⟨1184546, by decide⟩,⟨1185007, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5308_1185008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5308 ⟨1185008, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5308
    ⟨1185008, by decide⟩ (by decide) (![⟨1183266, by decide⟩,⟨1183925, by decide⟩,⟨1184546, by decide⟩,⟨1185007, by decide⟩]) unmarked_context_9_5308_1185008 node_context_9_5308_1185008
  intro a
  fin_cases a
  · exact context_10_21232_1183266
  · exact context_10_21233_1183925
  · exact context_10_21234_1184546
  · exact context_10_21235_1185007

theorem selected_cut_43307 : selected 9 ⟨1173556, by decide⟩
    (prefixPartial 12 339776) = some ⟨12, 1, 0, 1173556, 339776, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339776_1173556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339776 ⟨1173556, by decide⟩ :=
  accepted_of_selected 12 339776 ⟨1173556, by decide⟩ ⟨12, 1, 0, 1173556, 339776, 1, 65536⟩
    (by decide) selected_cut_43307

theorem selected_cut_43308 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 339777) = some ⟨12, 1, 0, 170504, 339777, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339777_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339777 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 339777 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 339777, 1, 65536⟩
    (by decide) selected_cut_43308

theorem selected_cut_43309 : selected 9 ⟨1185053, by decide⟩
    (prefixPartial 12 339778) = some ⟨12, 2, 0, 1185053, 339778, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_339778_1185053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339778 ⟨1185053, by decide⟩ :=
  accepted_of_selected 12 339778 ⟨1185053, by decide⟩ ⟨12, 2, 0, 1185053, 339778, 2613, 65536⟩
    (by decide) selected_cut_43309

theorem selected_cut_43310 : selected 9 ⟨1185092, by decide⟩
    (prefixPartial 12 339779) = some ⟨12, 2, 0, 1185092, 339779, 2593, 65536⟩ := by
  decide +kernel

theorem context_12_339779_1185092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339779 ⟨1185092, by decide⟩ :=
  accepted_of_selected 12 339779 ⟨1185092, by decide⟩ ⟨12, 2, 0, 1185092, 339779, 2593, 65536⟩
    (by decide) selected_cut_43310

theorem unmarked_context_11_84944_1185093 : frontier 10 ⟨1185093, by decide⟩
    (prefixCache 11 84944) (prefixPartial 11 84944) = false := by
  decide +kernel

theorem node_context_11_84944_1185093 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185093, by decide⟩ =
    .split (coordinate 11) (![⟨1173556, by decide⟩,⟨170504, by decide⟩,⟨1185053, by decide⟩,⟨1185092, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84944_1185093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84944 ⟨1185093, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84944
    ⟨1185093, by decide⟩ (by decide) (![⟨1173556, by decide⟩,⟨170504, by decide⟩,⟨1185053, by decide⟩,⟨1185092, by decide⟩]) unmarked_context_11_84944_1185093 node_context_11_84944_1185093
  intro a
  fin_cases a
  · exact context_12_339776_1173556
  · exact context_12_339777_170504
  · exact context_12_339778_1185053
  · exact context_12_339779_1185092

theorem selected_cut_43311 : selected 9 ⟨1185122, by decide⟩
    (prefixPartial 12 339780) = some ⟨12, 2, 0, 1185122, 339780, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_339780_1185122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339780 ⟨1185122, by decide⟩ :=
  accepted_of_selected 12 339780 ⟨1185122, by decide⟩ ⟨12, 2, 0, 1185122, 339780, 2029, 65536⟩
    (by decide) selected_cut_43311

theorem selected_cut_43312 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 339781) = some ⟨12, 1, 0, 170504, 339781, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339781_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339781 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 339781 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 339781, 1, 65536⟩
    (by decide) selected_cut_43312

theorem selected_cut_43313 : selected 9 ⟨1185160, by decide⟩
    (prefixPartial 12 339782) = some ⟨12, 2, 0, 1185160, 339782, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_339782_1185160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339782 ⟨1185160, by decide⟩ :=
  accepted_of_selected 12 339782 ⟨1185160, by decide⟩ ⟨12, 2, 0, 1185160, 339782, 2265, 65536⟩
    (by decide) selected_cut_43313

theorem selected_cut_43314 : selected 9 ⟨1185207, by decide⟩
    (prefixPartial 12 339783) = some ⟨12, 2, 0, 1185207, 339783, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_339783_1185207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339783 ⟨1185207, by decide⟩ :=
  accepted_of_selected 12 339783 ⟨1185207, by decide⟩ ⟨12, 2, 0, 1185207, 339783, 2445, 65536⟩
    (by decide) selected_cut_43314

theorem unmarked_context_11_84945_1185208 : frontier 10 ⟨1185208, by decide⟩
    (prefixCache 11 84945) (prefixPartial 11 84945) = false := by
  decide +kernel

theorem node_context_11_84945_1185208 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185208, by decide⟩ =
    .split (coordinate 11) (![⟨1185122, by decide⟩,⟨170504, by decide⟩,⟨1185160, by decide⟩,⟨1185207, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84945_1185208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84945 ⟨1185208, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84945
    ⟨1185208, by decide⟩ (by decide) (![⟨1185122, by decide⟩,⟨170504, by decide⟩,⟨1185160, by decide⟩,⟨1185207, by decide⟩]) unmarked_context_11_84945_1185208 node_context_11_84945_1185208
  intro a
  fin_cases a
  · exact context_12_339780_1185122
  · exact context_12_339781_170504
  · exact context_12_339782_1185160
  · exact context_12_339783_1185207

theorem selected_cut_43315 : selected 9 ⟨1185230, by decide⟩
    (prefixPartial 12 339784) = some ⟨12, 2, 0, 1185230, 339784, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_339784_1185230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339784 ⟨1185230, by decide⟩ :=
  accepted_of_selected 12 339784 ⟨1185230, by decide⟩ ⟨12, 2, 0, 1185230, 339784, 1869, 65536⟩
    (by decide) selected_cut_43315

theorem selected_cut_43316 : selected 9 ⟨1185259, by decide⟩
    (prefixPartial 12 339785) = some ⟨12, 2, 0, 1185259, 339785, 797, 65536⟩ := by
  decide +kernel

theorem context_12_339785_1185259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339785 ⟨1185259, by decide⟩ :=
  accepted_of_selected 12 339785 ⟨1185259, by decide⟩ ⟨12, 2, 0, 1185259, 339785, 797, 65536⟩
    (by decide) selected_cut_43316

theorem selected_cut_43317 : selected 9 ⟨1185290, by decide⟩
    (prefixPartial 12 339786) = some ⟨12, 2, 0, 1185290, 339786, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_339786_1185290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339786 ⟨1185290, by decide⟩ :=
  accepted_of_selected 12 339786 ⟨1185290, by decide⟩ ⟨12, 2, 0, 1185290, 339786, 2057, 65536⟩
    (by decide) selected_cut_43317

theorem selected_cut_43318 : selected 9 ⟨1185319, by decide⟩
    (prefixPartial 12 339787) = some ⟨12, 2, 0, 1185319, 339787, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_339787_1185319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339787 ⟨1185319, by decide⟩ :=
  accepted_of_selected 12 339787 ⟨1185319, by decide⟩ ⟨12, 2, 0, 1185319, 339787, 2149, 65536⟩
    (by decide) selected_cut_43318

theorem unmarked_context_11_84946_1185320 : frontier 10 ⟨1185320, by decide⟩
    (prefixCache 11 84946) (prefixPartial 11 84946) = false := by
  decide +kernel

theorem node_context_11_84946_1185320 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185320, by decide⟩ =
    .split (coordinate 11) (![⟨1185230, by decide⟩,⟨1185259, by decide⟩,⟨1185290, by decide⟩,⟨1185319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84946_1185320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84946 ⟨1185320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84946
    ⟨1185320, by decide⟩ (by decide) (![⟨1185230, by decide⟩,⟨1185259, by decide⟩,⟨1185290, by decide⟩,⟨1185319, by decide⟩]) unmarked_context_11_84946_1185320 node_context_11_84946_1185320
  intro a
  fin_cases a
  · exact context_12_339784_1185230
  · exact context_12_339785_1185259
  · exact context_12_339786_1185290
  · exact context_12_339787_1185319

theorem selected_cut_43319 : selected 10 ⟨1185369, by decide⟩
    (prefixPartial 11 84947) = some ⟨11, 2, 0, 1185369, 84947, 3377, 262144⟩ := by
  decide +kernel

theorem context_11_84947_1185369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84947 ⟨1185369, by decide⟩ :=
  accepted_of_selected 11 84947 ⟨1185369, by decide⟩ ⟨11, 2, 0, 1185369, 84947, 3377, 262144⟩
    (by decide) selected_cut_43319

theorem unmarked_context_10_21236_1185370 : frontier 11 ⟨1185370, by decide⟩
    (prefixCache 10 21236) (prefixPartial 10 21236) = false := by
  decide +kernel

theorem node_context_10_21236_1185370 : EJMOriginalGlobalDAGData.nodes 11 ⟨1185370, by decide⟩ =
    .split (coordinate 10) (![⟨1185093, by decide⟩,⟨1185208, by decide⟩,⟨1185320, by decide⟩,⟨1185369, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21236_1185370 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21236 ⟨1185370, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21236
    ⟨1185370, by decide⟩ (by decide) (![⟨1185093, by decide⟩,⟨1185208, by decide⟩,⟨1185320, by decide⟩,⟨1185369, by decide⟩]) unmarked_context_10_21236_1185370 node_context_10_21236_1185370
  intro a
  fin_cases a
  · exact context_11_84944_1185093
  · exact context_11_84945_1185208
  · exact context_11_84946_1185320
  · exact context_11_84947_1185369

theorem selected_cut_43320 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21237) = some ⟨10, 1, 0, 893098, 21237, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21237_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21237 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21237 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21237, 1, 1048576⟩
    (by decide) selected_cut_43320

theorem selected_cut_43321 : selected 9 ⟨1185403, by decide⟩
    (prefixPartial 12 339808) = some ⟨12, 2, 0, 1185403, 339808, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_339808_1185403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339808 ⟨1185403, by decide⟩ :=
  accepted_of_selected 12 339808 ⟨1185403, by decide⟩ ⟨12, 2, 0, 1185403, 339808, 1977, 65536⟩
    (by decide) selected_cut_43321

theorem selected_cut_43322 : selected 9 ⟨1185438, by decide⟩
    (prefixPartial 12 339809) = some ⟨12, 2, 0, 1185438, 339809, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_339809_1185438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339809 ⟨1185438, by decide⟩ :=
  accepted_of_selected 12 339809 ⟨1185438, by decide⟩ ⟨12, 2, 0, 1185438, 339809, 1865, 65536⟩
    (by decide) selected_cut_43322

theorem selected_cut_43323 : selected 9 ⟨1185473, by decide⟩
    (prefixPartial 12 339810) = some ⟨12, 2, 0, 1185473, 339810, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_339810_1185473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339810 ⟨1185473, by decide⟩ :=
  accepted_of_selected 12 339810 ⟨1185473, by decide⟩ ⟨12, 2, 0, 1185473, 339810, 2101, 65536⟩
    (by decide) selected_cut_43323

theorem selected_cut_43324 : selected 9 ⟨1185503, by decide⟩
    (prefixPartial 12 339811) = some ⟨12, 2, 0, 1185503, 339811, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_339811_1185503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339811 ⟨1185503, by decide⟩ :=
  accepted_of_selected 12 339811 ⟨1185503, by decide⟩ ⟨12, 2, 0, 1185503, 339811, 2129, 65536⟩
    (by decide) selected_cut_43324

theorem unmarked_context_11_84952_1185504 : frontier 10 ⟨1185504, by decide⟩
    (prefixCache 11 84952) (prefixPartial 11 84952) = false := by
  decide +kernel

theorem node_context_11_84952_1185504 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185504, by decide⟩ =
    .split (coordinate 11) (![⟨1185403, by decide⟩,⟨1185438, by decide⟩,⟨1185473, by decide⟩,⟨1185503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84952_1185504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84952 ⟨1185504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84952
    ⟨1185504, by decide⟩ (by decide) (![⟨1185403, by decide⟩,⟨1185438, by decide⟩,⟨1185473, by decide⟩,⟨1185503, by decide⟩]) unmarked_context_11_84952_1185504 node_context_11_84952_1185504
  intro a
  fin_cases a
  · exact context_12_339808_1185403
  · exact context_12_339809_1185438
  · exact context_12_339810_1185473
  · exact context_12_339811_1185503

theorem selected_cut_43325 : selected 9 ⟨1185537, by decide⟩
    (prefixPartial 12 339812) = some ⟨12, 2, 0, 1185537, 339812, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_339812_1185537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339812 ⟨1185537, by decide⟩ :=
  accepted_of_selected 12 339812 ⟨1185537, by decide⟩ ⟨12, 2, 0, 1185537, 339812, 1757, 65536⟩
    (by decide) selected_cut_43325

theorem selected_cut_43326 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 339813) = some ⟨12, 1, 0, 642794, 339813, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339813_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339813 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 339813 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 339813, 1, 65536⟩
    (by decide) selected_cut_43326

theorem selected_cut_43327 : selected 9 ⟨1185568, by decide⟩
    (prefixPartial 12 339814) = some ⟨12, 2, 0, 1185568, 339814, 1877, 65536⟩ := by
  decide +kernel

theorem context_12_339814_1185568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339814 ⟨1185568, by decide⟩ :=
  accepted_of_selected 12 339814 ⟨1185568, by decide⟩ ⟨12, 2, 0, 1185568, 339814, 1877, 65536⟩
    (by decide) selected_cut_43327

theorem selected_cut_43328 : selected 9 ⟨1185597, by decide⟩
    (prefixPartial 12 339815) = some ⟨12, 2, 0, 1185597, 339815, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_339815_1185597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339815 ⟨1185597, by decide⟩ :=
  accepted_of_selected 12 339815 ⟨1185597, by decide⟩ ⟨12, 2, 0, 1185597, 339815, 1997, 65536⟩
    (by decide) selected_cut_43328

theorem unmarked_context_11_84953_1185598 : frontier 10 ⟨1185598, by decide⟩
    (prefixCache 11 84953) (prefixPartial 11 84953) = false := by
  decide +kernel

theorem node_context_11_84953_1185598 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185598, by decide⟩ =
    .split (coordinate 11) (![⟨1185537, by decide⟩,⟨642794, by decide⟩,⟨1185568, by decide⟩,⟨1185597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84953_1185598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84953 ⟨1185598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84953
    ⟨1185598, by decide⟩ (by decide) (![⟨1185537, by decide⟩,⟨642794, by decide⟩,⟨1185568, by decide⟩,⟨1185597, by decide⟩]) unmarked_context_11_84953_1185598 node_context_11_84953_1185598
  intro a
  fin_cases a
  · exact context_12_339812_1185537
  · exact context_12_339813_642794
  · exact context_12_339814_1185568
  · exact context_12_339815_1185597

theorem selected_cut_43329 : selected 9 ⟨1185620, by decide⟩
    (prefixPartial 12 339816) = some ⟨12, 2, 0, 1185620, 339816, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_339816_1185620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339816 ⟨1185620, by decide⟩ :=
  accepted_of_selected 12 339816 ⟨1185620, by decide⟩ ⟨12, 2, 0, 1185620, 339816, 1561, 65536⟩
    (by decide) selected_cut_43329

theorem selected_cut_43330 : selected 9 ⟨1185647, by decide⟩
    (prefixPartial 12 339817) = some ⟨12, 2, 0, 1185647, 339817, 1549, 65536⟩ := by
  decide +kernel

theorem context_12_339817_1185647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339817 ⟨1185647, by decide⟩ :=
  accepted_of_selected 12 339817 ⟨1185647, by decide⟩ ⟨12, 2, 0, 1185647, 339817, 1549, 65536⟩
    (by decide) selected_cut_43330

theorem selected_cut_43331 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 339818) = some ⟨12, 1, 0, 1172910, 339818, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339818_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339818 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 339818 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 339818, 1, 65536⟩
    (by decide) selected_cut_43331

theorem selected_cut_43332 : selected 9 ⟨1185671, by decide⟩
    (prefixPartial 12 339819) = some ⟨12, 2, 0, 1185671, 339819, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_339819_1185671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339819 ⟨1185671, by decide⟩ :=
  accepted_of_selected 12 339819 ⟨1185671, by decide⟩ ⟨12, 2, 0, 1185671, 339819, 1777, 65536⟩
    (by decide) selected_cut_43332

theorem unmarked_context_11_84954_1185672 : frontier 10 ⟨1185672, by decide⟩
    (prefixCache 11 84954) (prefixPartial 11 84954) = false := by
  decide +kernel

theorem node_context_11_84954_1185672 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185672, by decide⟩ =
    .split (coordinate 11) (![⟨1185620, by decide⟩,⟨1185647, by decide⟩,⟨1172910, by decide⟩,⟨1185671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84954_1185672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84954 ⟨1185672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84954
    ⟨1185672, by decide⟩ (by decide) (![⟨1185620, by decide⟩,⟨1185647, by decide⟩,⟨1172910, by decide⟩,⟨1185671, by decide⟩]) unmarked_context_11_84954_1185672 node_context_11_84954_1185672
  intro a
  fin_cases a
  · exact context_12_339816_1185620
  · exact context_12_339817_1185647
  · exact context_12_339818_1172910
  · exact context_12_339819_1185671

theorem selected_cut_43333 : selected 9 ⟨1185692, by decide⟩
    (prefixPartial 12 339820) = some ⟨12, 2, 0, 1185692, 339820, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_339820_1185692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339820 ⟨1185692, by decide⟩ :=
  accepted_of_selected 12 339820 ⟨1185692, by decide⟩ ⟨12, 2, 0, 1185692, 339820, 1349, 65536⟩
    (by decide) selected_cut_43333

theorem selected_cut_43334 : selected 9 ⟨1185713, by decide⟩
    (prefixPartial 12 339821) = some ⟨12, 2, 0, 1185713, 339821, 1329, 65536⟩ := by
  decide +kernel

theorem context_12_339821_1185713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339821 ⟨1185713, by decide⟩ :=
  accepted_of_selected 12 339821 ⟨1185713, by decide⟩ ⟨12, 2, 0, 1185713, 339821, 1329, 65536⟩
    (by decide) selected_cut_43334

theorem selected_cut_43335 : selected 9 ⟨1185738, by decide⟩
    (prefixPartial 12 339822) = some ⟨12, 2, 0, 1185738, 339822, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_339822_1185738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339822 ⟨1185738, by decide⟩ :=
  accepted_of_selected 12 339822 ⟨1185738, by decide⟩ ⟨12, 2, 0, 1185738, 339822, 1509, 65536⟩
    (by decide) selected_cut_43335

theorem selected_cut_43336 : selected 9 ⟨903806, by decide⟩
    (prefixPartial 12 339823) = some ⟨12, 1, 0, 903806, 339823, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339823_903806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339823 ⟨903806, by decide⟩ :=
  accepted_of_selected 12 339823 ⟨903806, by decide⟩ ⟨12, 1, 0, 903806, 339823, 1, 65536⟩
    (by decide) selected_cut_43336

theorem unmarked_context_11_84955_1185739 : frontier 10 ⟨1185739, by decide⟩
    (prefixCache 11 84955) (prefixPartial 11 84955) = false := by
  decide +kernel

theorem node_context_11_84955_1185739 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185739, by decide⟩ =
    .split (coordinate 11) (![⟨1185692, by decide⟩,⟨1185713, by decide⟩,⟨1185738, by decide⟩,⟨903806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84955_1185739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84955 ⟨1185739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84955
    ⟨1185739, by decide⟩ (by decide) (![⟨1185692, by decide⟩,⟨1185713, by decide⟩,⟨1185738, by decide⟩,⟨903806, by decide⟩]) unmarked_context_11_84955_1185739 node_context_11_84955_1185739
  intro a
  fin_cases a
  · exact context_12_339820_1185692
  · exact context_12_339821_1185713
  · exact context_12_339822_1185738
  · exact context_12_339823_903806

theorem unmarked_context_10_21238_1185740 : frontier 11 ⟨1185740, by decide⟩
    (prefixCache 10 21238) (prefixPartial 10 21238) = false := by
  decide +kernel

theorem node_context_10_21238_1185740 : EJMOriginalGlobalDAGData.nodes 11 ⟨1185740, by decide⟩ =
    .split (coordinate 10) (![⟨1185504, by decide⟩,⟨1185598, by decide⟩,⟨1185672, by decide⟩,⟨1185739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21238_1185740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21238 ⟨1185740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21238
    ⟨1185740, by decide⟩ (by decide) (![⟨1185504, by decide⟩,⟨1185598, by decide⟩,⟨1185672, by decide⟩,⟨1185739, by decide⟩]) unmarked_context_10_21238_1185740 node_context_10_21238_1185740
  intro a
  fin_cases a
  · exact context_11_84952_1185504
  · exact context_11_84953_1185598
  · exact context_11_84954_1185672
  · exact context_11_84955_1185739

theorem selected_cut_43337 : selected 9 ⟨1185770, by decide⟩
    (prefixPartial 12 339824) = some ⟨12, 2, 0, 1185770, 339824, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_339824_1185770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339824 ⟨1185770, by decide⟩ :=
  accepted_of_selected 12 339824 ⟨1185770, by decide⟩ ⟨12, 2, 0, 1185770, 339824, 1893, 65536⟩
    (by decide) selected_cut_43337

theorem selected_cut_43338 : selected 9 ⟨1185801, by decide⟩
    (prefixPartial 12 339825) = some ⟨12, 2, 0, 1185801, 339825, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_339825_1185801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339825 ⟨1185801, by decide⟩ :=
  accepted_of_selected 12 339825 ⟨1185801, by decide⟩ ⟨12, 2, 0, 1185801, 339825, 1833, 65536⟩
    (by decide) selected_cut_43338

theorem selected_cut_43339 : selected 9 ⟨1185833, by decide⟩
    (prefixPartial 12 339826) = some ⟨12, 2, 0, 1185833, 339826, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_339826_1185833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339826 ⟨1185833, by decide⟩ :=
  accepted_of_selected 12 339826 ⟨1185833, by decide⟩ ⟨12, 2, 0, 1185833, 339826, 2097, 65536⟩
    (by decide) selected_cut_43339

theorem selected_cut_43340 : selected 9 ⟨1185860, by decide⟩
    (prefixPartial 12 339827) = some ⟨12, 2, 0, 1185860, 339827, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_339827_1185860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339827 ⟨1185860, by decide⟩ :=
  accepted_of_selected 12 339827 ⟨1185860, by decide⟩ ⟨12, 2, 0, 1185860, 339827, 1849, 65536⟩
    (by decide) selected_cut_43340

theorem unmarked_context_11_84956_1185861 : frontier 10 ⟨1185861, by decide⟩
    (prefixCache 11 84956) (prefixPartial 11 84956) = false := by
  decide +kernel

theorem node_context_11_84956_1185861 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185861, by decide⟩ =
    .split (coordinate 11) (![⟨1185770, by decide⟩,⟨1185801, by decide⟩,⟨1185833, by decide⟩,⟨1185860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84956_1185861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84956 ⟨1185861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84956
    ⟨1185861, by decide⟩ (by decide) (![⟨1185770, by decide⟩,⟨1185801, by decide⟩,⟨1185833, by decide⟩,⟨1185860, by decide⟩]) unmarked_context_11_84956_1185861 node_context_11_84956_1185861
  intro a
  fin_cases a
  · exact context_12_339824_1185770
  · exact context_12_339825_1185801
  · exact context_12_339826_1185833
  · exact context_12_339827_1185860

theorem selected_cut_43341 : selected 9 ⟨1185896, by decide⟩
    (prefixPartial 12 339828) = some ⟨12, 2, 0, 1185896, 339828, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_339828_1185896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339828 ⟨1185896, by decide⟩ :=
  accepted_of_selected 12 339828 ⟨1185896, by decide⟩ ⟨12, 2, 0, 1185896, 339828, 1633, 65536⟩
    (by decide) selected_cut_43341

theorem selected_cut_43342 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 339829) = some ⟨12, 1, 0, 642794, 339829, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339829_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339829 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 339829 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 339829, 1, 65536⟩
    (by decide) selected_cut_43342

theorem selected_cut_43343 : selected 9 ⟨1185934, by decide⟩
    (prefixPartial 12 339830) = some ⟨12, 2, 0, 1185934, 339830, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_339830_1185934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339830 ⟨1185934, by decide⟩ :=
  accepted_of_selected 12 339830 ⟨1185934, by decide⟩ ⟨12, 2, 0, 1185934, 339830, 1721, 65536⟩
    (by decide) selected_cut_43343

theorem selected_cut_43344 : selected 9 ⟨1185964, by decide⟩
    (prefixPartial 12 339831) = some ⟨12, 2, 0, 1185964, 339831, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_339831_1185964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339831 ⟨1185964, by decide⟩ :=
  accepted_of_selected 12 339831 ⟨1185964, by decide⟩ ⟨12, 2, 0, 1185964, 339831, 1665, 65536⟩
    (by decide) selected_cut_43344

theorem unmarked_context_11_84957_1185965 : frontier 10 ⟨1185965, by decide⟩
    (prefixCache 11 84957) (prefixPartial 11 84957) = false := by
  decide +kernel

theorem node_context_11_84957_1185965 : EJMOriginalGlobalDAGData.nodes 10 ⟨1185965, by decide⟩ =
    .split (coordinate 11) (![⟨1185896, by decide⟩,⟨642794, by decide⟩,⟨1185934, by decide⟩,⟨1185964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84957_1185965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84957 ⟨1185965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84957
    ⟨1185965, by decide⟩ (by decide) (![⟨1185896, by decide⟩,⟨642794, by decide⟩,⟨1185934, by decide⟩,⟨1185964, by decide⟩]) unmarked_context_11_84957_1185965 node_context_11_84957_1185965
  intro a
  fin_cases a
  · exact context_12_339828_1185896
  · exact context_12_339829_642794
  · exact context_12_339830_1185934
  · exact context_12_339831_1185964

theorem selected_cut_43345 : selected 9 ⟨1185985, by decide⟩
    (prefixPartial 12 339832) = some ⟨12, 2, 0, 1185985, 339832, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_339832_1185985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339832 ⟨1185985, by decide⟩ :=
  accepted_of_selected 12 339832 ⟨1185985, by decide⟩ ⟨12, 2, 0, 1185985, 339832, 1289, 65536⟩
    (by decide) selected_cut_43345

theorem selected_cut_43346 : selected 9 ⟨1186005, by decide⟩
    (prefixPartial 12 339833) = some ⟨12, 2, 0, 1186005, 339833, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_339833_1186005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339833 ⟨1186005, by decide⟩ :=
  accepted_of_selected 12 339833 ⟨1186005, by decide⟩ ⟨12, 2, 0, 1186005, 339833, 1309, 65536⟩
    (by decide) selected_cut_43346

theorem selected_cut_43347 : selected 9 ⟨1186027, by decide⟩
    (prefixPartial 12 339834) = some ⟨12, 2, 0, 1186027, 339834, 1289, 65536⟩ := by
  decide +kernel

theorem context_12_339834_1186027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339834 ⟨1186027, by decide⟩ :=
  accepted_of_selected 12 339834 ⟨1186027, by decide⟩ ⟨12, 2, 0, 1186027, 339834, 1289, 65536⟩
    (by decide) selected_cut_43347

theorem selected_cut_43348 : selected 9 ⟨1186042, by decide⟩
    (prefixPartial 12 339835) = some ⟨12, 2, 0, 1186042, 339835, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_339835_1186042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339835 ⟨1186042, by decide⟩ :=
  accepted_of_selected 12 339835 ⟨1186042, by decide⟩ ⟨12, 2, 0, 1186042, 339835, 1253, 65536⟩
    (by decide) selected_cut_43348

theorem unmarked_context_11_84958_1186043 : frontier 10 ⟨1186043, by decide⟩
    (prefixCache 11 84958) (prefixPartial 11 84958) = false := by
  decide +kernel

theorem node_context_11_84958_1186043 : EJMOriginalGlobalDAGData.nodes 10 ⟨1186043, by decide⟩ =
    .split (coordinate 11) (![⟨1185985, by decide⟩,⟨1186005, by decide⟩,⟨1186027, by decide⟩,⟨1186042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84958_1186043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84958 ⟨1186043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84958
    ⟨1186043, by decide⟩ (by decide) (![⟨1185985, by decide⟩,⟨1186005, by decide⟩,⟨1186027, by decide⟩,⟨1186042, by decide⟩]) unmarked_context_11_84958_1186043 node_context_11_84958_1186043
  intro a
  fin_cases a
  · exact context_12_339832_1185985
  · exact context_12_339833_1186005
  · exact context_12_339834_1186027
  · exact context_12_339835_1186042

theorem selected_cut_43349 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84959) = some ⟨11, 1, 0, 977886, 84959, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84959_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84959 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84959 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84959, 1, 262144⟩
    (by decide) selected_cut_43349

theorem unmarked_context_10_21239_1186044 : frontier 11 ⟨1186044, by decide⟩
    (prefixCache 10 21239) (prefixPartial 10 21239) = false := by
  decide +kernel

theorem node_context_10_21239_1186044 : EJMOriginalGlobalDAGData.nodes 11 ⟨1186044, by decide⟩ =
    .split (coordinate 10) (![⟨1185861, by decide⟩,⟨1185965, by decide⟩,⟨1186043, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21239_1186044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21239 ⟨1186044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21239
    ⟨1186044, by decide⟩ (by decide) (![⟨1185861, by decide⟩,⟨1185965, by decide⟩,⟨1186043, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21239_1186044 node_context_10_21239_1186044
  intro a
  fin_cases a
  · exact context_11_84956_1185861
  · exact context_11_84957_1185965
  · exact context_11_84958_1186043
  · exact context_11_84959_977886

theorem unmarked_context_9_5309_1186045 : frontier 12 ⟨1186045, by decide⟩
    (prefixCache 9 5309) (prefixPartial 9 5309) = false := by
  decide +kernel

theorem node_context_9_5309_1186045 : EJMOriginalGlobalDAGData.nodes 12 ⟨1186045, by decide⟩ =
    .split (coordinate 9) (![⟨1185370, by decide⟩,⟨893098, by decide⟩,⟨1185740, by decide⟩,⟨1186044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5309_1186045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5309 ⟨1186045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5309
    ⟨1186045, by decide⟩ (by decide) (![⟨1185370, by decide⟩,⟨893098, by decide⟩,⟨1185740, by decide⟩,⟨1186044, by decide⟩]) unmarked_context_9_5309_1186045 node_context_9_5309_1186045
  intro a
  fin_cases a
  · exact context_10_21236_1185370
  · exact context_10_21237_893098
  · exact context_10_21238_1185740
  · exact context_10_21239_1186044

theorem selected_cut_43350 : selected 9 ⟨1173556, by decide⟩
    (prefixPartial 12 339840) = some ⟨12, 1, 0, 1173556, 339840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339840_1173556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339840 ⟨1173556, by decide⟩ :=
  accepted_of_selected 12 339840 ⟨1173556, by decide⟩ ⟨12, 1, 0, 1173556, 339840, 1, 65536⟩
    (by decide) selected_cut_43350

theorem selected_cut_43351 : selected 9 ⟨1186071, by decide⟩
    (prefixPartial 12 339841) = some ⟨12, 2, 0, 1186071, 339841, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_339841_1186071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339841 ⟨1186071, by decide⟩ :=
  accepted_of_selected 12 339841 ⟨1186071, by decide⟩ ⟨12, 2, 0, 1186071, 339841, 1581, 65536⟩
    (by decide) selected_cut_43351

theorem selected_cut_43352 : selected 9 ⟨1186087, by decide⟩
    (prefixPartial 12 339842) = some ⟨12, 2, 0, 1186087, 339842, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_339842_1186087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339842 ⟨1186087, by decide⟩ :=
  accepted_of_selected 12 339842 ⟨1186087, by decide⟩ ⟨12, 2, 0, 1186087, 339842, 1305, 65536⟩
    (by decide) selected_cut_43352

theorem selected_cut_43353 : selected 9 ⟨1186110, by decide⟩
    (prefixPartial 12 339843) = some ⟨12, 2, 0, 1186110, 339843, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_339843_1186110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339843 ⟨1186110, by decide⟩ :=
  accepted_of_selected 12 339843 ⟨1186110, by decide⟩ ⟨12, 2, 0, 1186110, 339843, 1497, 65536⟩
    (by decide) selected_cut_43353

theorem unmarked_context_11_84960_1186111 : frontier 10 ⟨1186111, by decide⟩
    (prefixCache 11 84960) (prefixPartial 11 84960) = false := by
  decide +kernel

theorem node_context_11_84960_1186111 : EJMOriginalGlobalDAGData.nodes 10 ⟨1186111, by decide⟩ =
    .split (coordinate 11) (![⟨1173556, by decide⟩,⟨1186071, by decide⟩,⟨1186087, by decide⟩,⟨1186110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84960_1186111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84960 ⟨1186111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84960
    ⟨1186111, by decide⟩ (by decide) (![⟨1173556, by decide⟩,⟨1186071, by decide⟩,⟨1186087, by decide⟩,⟨1186110, by decide⟩]) unmarked_context_11_84960_1186111 node_context_11_84960_1186111
  intro a
  fin_cases a
  · exact context_12_339840_1173556
  · exact context_12_339841_1186071
  · exact context_12_339842_1186087
  · exact context_12_339843_1186110

theorem selected_cut_43354 : selected 9 ⟨1186135, by decide⟩
    (prefixPartial 12 339844) = some ⟨12, 2, 0, 1186135, 339844, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_339844_1186135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339844 ⟨1186135, by decide⟩ :=
  accepted_of_selected 12 339844 ⟨1186135, by decide⟩ ⟨12, 2, 0, 1186135, 339844, 1353, 65536⟩
    (by decide) selected_cut_43354

theorem selected_cut_43355 : selected 9 ⟨1186159, by decide⟩
    (prefixPartial 12 339845) = some ⟨12, 2, 0, 1186159, 339845, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_339845_1186159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339845 ⟨1186159, by decide⟩ :=
  accepted_of_selected 12 339845 ⟨1186159, by decide⟩ ⟨12, 2, 0, 1186159, 339845, 1405, 65536⟩
    (by decide) selected_cut_43355

theorem selected_cut_43356 : selected 9 ⟨1186179, by decide⟩
    (prefixPartial 12 339846) = some ⟨12, 2, 0, 1186179, 339846, 1257, 65536⟩ := by
  decide +kernel

theorem context_12_339846_1186179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339846 ⟨1186179, by decide⟩ :=
  accepted_of_selected 12 339846 ⟨1186179, by decide⟩ ⟨12, 2, 0, 1186179, 339846, 1257, 65536⟩
    (by decide) selected_cut_43356

theorem selected_cut_43357 : selected 9 ⟨1186214, by decide⟩
    (prefixPartial 12 339847) = some ⟨12, 2, 0, 1186214, 339847, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_339847_1186214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339847 ⟨1186214, by decide⟩ :=
  accepted_of_selected 12 339847 ⟨1186214, by decide⟩ ⟨12, 2, 0, 1186214, 339847, 1521, 65536⟩
    (by decide) selected_cut_43357

theorem unmarked_context_11_84961_1186215 : frontier 10 ⟨1186215, by decide⟩
    (prefixCache 11 84961) (prefixPartial 11 84961) = false := by
  decide +kernel

theorem node_context_11_84961_1186215 : EJMOriginalGlobalDAGData.nodes 10 ⟨1186215, by decide⟩ =
    .split (coordinate 11) (![⟨1186135, by decide⟩,⟨1186159, by decide⟩,⟨1186179, by decide⟩,⟨1186214, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84961_1186215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84961 ⟨1186215, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84961
    ⟨1186215, by decide⟩ (by decide) (![⟨1186135, by decide⟩,⟨1186159, by decide⟩,⟨1186179, by decide⟩,⟨1186214, by decide⟩]) unmarked_context_11_84961_1186215 node_context_11_84961_1186215
  intro a
  fin_cases a
  · exact context_12_339844_1186135
  · exact context_12_339845_1186159
  · exact context_12_339846_1186179
  · exact context_12_339847_1186214

theorem selected_cut_43358 : selected 10 ⟨1186281, by decide⟩
    (prefixPartial 11 84962) = some ⟨11, 2, 0, 1186281, 84962, 3909, 262144⟩ := by
  decide +kernel

theorem context_11_84962_1186281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84962 ⟨1186281, by decide⟩ :=
  accepted_of_selected 11 84962 ⟨1186281, by decide⟩ ⟨11, 2, 0, 1186281, 84962, 3909, 262144⟩
    (by decide) selected_cut_43358

theorem selected_cut_43359 : selected 10 ⟨1186330, by decide⟩
    (prefixPartial 11 84963) = some ⟨11, 2, 0, 1186330, 84963, 3229, 262144⟩ := by
  decide +kernel

theorem context_11_84963_1186330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84963 ⟨1186330, by decide⟩ :=
  accepted_of_selected 11 84963 ⟨1186330, by decide⟩ ⟨11, 2, 0, 1186330, 84963, 3229, 262144⟩
    (by decide) selected_cut_43359

theorem unmarked_context_10_21240_1186331 : frontier 11 ⟨1186331, by decide⟩
    (prefixCache 10 21240) (prefixPartial 10 21240) = false := by
  decide +kernel

theorem node_context_10_21240_1186331 : EJMOriginalGlobalDAGData.nodes 11 ⟨1186331, by decide⟩ =
    .split (coordinate 10) (![⟨1186111, by decide⟩,⟨1186215, by decide⟩,⟨1186281, by decide⟩,⟨1186330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21240_1186331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21240 ⟨1186331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21240
    ⟨1186331, by decide⟩ (by decide) (![⟨1186111, by decide⟩,⟨1186215, by decide⟩,⟨1186281, by decide⟩,⟨1186330, by decide⟩]) unmarked_context_10_21240_1186331 node_context_10_21240_1186331
  intro a
  fin_cases a
  · exact context_11_84960_1186111
  · exact context_11_84961_1186215
  · exact context_11_84962_1186281
  · exact context_11_84963_1186330

theorem selected_cut_43360 : selected 9 ⟨1186350, by decide⟩
    (prefixPartial 12 339856) = some ⟨12, 2, 0, 1186350, 339856, 1269, 65536⟩ := by
  decide +kernel

theorem context_12_339856_1186350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339856 ⟨1186350, by decide⟩ :=
  accepted_of_selected 12 339856 ⟨1186350, by decide⟩ ⟨12, 2, 0, 1186350, 339856, 1269, 65536⟩
    (by decide) selected_cut_43360

theorem selected_cut_43361 : selected 9 ⟨1186368, by decide⟩
    (prefixPartial 12 339857) = some ⟨12, 2, 0, 1186368, 339857, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_339857_1186368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339857 ⟨1186368, by decide⟩ :=
  accepted_of_selected 12 339857 ⟨1186368, by decide⟩ ⟨12, 2, 0, 1186368, 339857, 1305, 65536⟩
    (by decide) selected_cut_43361

theorem selected_cut_43362 : selected 9 ⟨1186391, by decide⟩
    (prefixPartial 12 339858) = some ⟨12, 2, 0, 1186391, 339858, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_339858_1186391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339858 ⟨1186391, by decide⟩ :=
  accepted_of_selected 12 339858 ⟨1186391, by decide⟩ ⟨12, 2, 0, 1186391, 339858, 1305, 65536⟩
    (by decide) selected_cut_43362

theorem selected_cut_43363 : selected 9 ⟨1186409, by decide⟩
    (prefixPartial 12 339859) = some ⟨12, 2, 0, 1186409, 339859, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_339859_1186409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339859 ⟨1186409, by decide⟩ :=
  accepted_of_selected 12 339859 ⟨1186409, by decide⟩ ⟨12, 2, 0, 1186409, 339859, 1261, 65536⟩
    (by decide) selected_cut_43363

theorem unmarked_context_11_84964_1186410 : frontier 10 ⟨1186410, by decide⟩
    (prefixCache 11 84964) (prefixPartial 11 84964) = false := by
  decide +kernel

theorem node_context_11_84964_1186410 : EJMOriginalGlobalDAGData.nodes 10 ⟨1186410, by decide⟩ =
    .split (coordinate 11) (![⟨1186350, by decide⟩,⟨1186368, by decide⟩,⟨1186391, by decide⟩,⟨1186409, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84964_1186410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84964 ⟨1186410, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84964
    ⟨1186410, by decide⟩ (by decide) (![⟨1186350, by decide⟩,⟨1186368, by decide⟩,⟨1186391, by decide⟩,⟨1186409, by decide⟩]) unmarked_context_11_84964_1186410 node_context_11_84964_1186410
  intro a
  fin_cases a
  · exact context_12_339856_1186350
  · exact context_12_339857_1186368
  · exact context_12_339858_1186391
  · exact context_12_339859_1186409

theorem selected_cut_43364 : selected 10 ⟨1186476, by decide⟩
    (prefixPartial 11 84965) = some ⟨11, 2, 0, 1186476, 84965, 3681, 262144⟩ := by
  decide +kernel

theorem context_11_84965_1186476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84965 ⟨1186476, by decide⟩ :=
  accepted_of_selected 11 84965 ⟨1186476, by decide⟩ ⟨11, 2, 0, 1186476, 84965, 3681, 262144⟩
    (by decide) selected_cut_43364

theorem selected_cut_43365 : selected 10 ⟨1186525, by decide⟩
    (prefixPartial 11 84966) = some ⟨11, 2, 0, 1186525, 84966, 3077, 262144⟩ := by
  decide +kernel

theorem context_11_84966_1186525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84966 ⟨1186525, by decide⟩ :=
  accepted_of_selected 11 84966 ⟨1186525, by decide⟩ ⟨11, 2, 0, 1186525, 84966, 3077, 262144⟩
    (by decide) selected_cut_43365

theorem selected_cut_43366 : selected 10 ⟨1186571, by decide⟩
    (prefixPartial 11 84967) = some ⟨11, 2, 0, 1186571, 84967, 2657, 262144⟩ := by
  decide +kernel

theorem context_11_84967_1186571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84967 ⟨1186571, by decide⟩ :=
  accepted_of_selected 11 84967 ⟨1186571, by decide⟩ ⟨11, 2, 0, 1186571, 84967, 2657, 262144⟩
    (by decide) selected_cut_43366

theorem unmarked_context_10_21241_1186572 : frontier 11 ⟨1186572, by decide⟩
    (prefixCache 10 21241) (prefixPartial 10 21241) = false := by
  decide +kernel

theorem node_context_10_21241_1186572 : EJMOriginalGlobalDAGData.nodes 11 ⟨1186572, by decide⟩ =
    .split (coordinate 10) (![⟨1186410, by decide⟩,⟨1186476, by decide⟩,⟨1186525, by decide⟩,⟨1186571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21241_1186572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21241 ⟨1186572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21241
    ⟨1186572, by decide⟩ (by decide) (![⟨1186410, by decide⟩,⟨1186476, by decide⟩,⟨1186525, by decide⟩,⟨1186571, by decide⟩]) unmarked_context_10_21241_1186572 node_context_10_21241_1186572
  intro a
  fin_cases a
  · exact context_11_84964_1186410
  · exact context_11_84965_1186476
  · exact context_11_84966_1186525
  · exact context_11_84967_1186571

theorem selected_cut_43367 : selected 10 ⟨1186610, by decide⟩
    (prefixPartial 11 84968) = some ⟨11, 2, 0, 1186610, 84968, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_84968_1186610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84968 ⟨1186610, by decide⟩ :=
  accepted_of_selected 11 84968 ⟨1186610, by decide⟩ ⟨11, 2, 0, 1186610, 84968, 2329, 262144⟩
    (by decide) selected_cut_43367

theorem selected_cut_43368 : selected 10 ⟨1186656, by decide⟩
    (prefixPartial 11 84969) = some ⟨11, 2, 0, 1186656, 84969, 2389, 262144⟩ := by
  decide +kernel

theorem context_11_84969_1186656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84969 ⟨1186656, by decide⟩ :=
  accepted_of_selected 11 84969 ⟨1186656, by decide⟩ ⟨11, 2, 0, 1186656, 84969, 2389, 262144⟩
    (by decide) selected_cut_43368

theorem selected_cut_43369 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84970) = some ⟨11, 1, 0, 1109453, 84970, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84970_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84970 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84970 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84970, 1, 262144⟩
    (by decide) selected_cut_43369

theorem selected_cut_43370 : selected 10 ⟨1186671, by decide⟩
    (prefixPartial 11 84971) = some ⟨11, 2, 0, 1186671, 84971, 1177, 262144⟩ := by
  decide +kernel

theorem context_11_84971_1186671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84971 ⟨1186671, by decide⟩ :=
  accepted_of_selected 11 84971 ⟨1186671, by decide⟩ ⟨11, 2, 0, 1186671, 84971, 1177, 262144⟩
    (by decide) selected_cut_43370

theorem unmarked_context_10_21242_1186672 : frontier 11 ⟨1186672, by decide⟩
    (prefixCache 10 21242) (prefixPartial 10 21242) = false := by
  decide +kernel

theorem node_context_10_21242_1186672 : EJMOriginalGlobalDAGData.nodes 11 ⟨1186672, by decide⟩ =
    .split (coordinate 10) (![⟨1186610, by decide⟩,⟨1186656, by decide⟩,⟨1109453, by decide⟩,⟨1186671, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21242_1186672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21242 ⟨1186672, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21242
    ⟨1186672, by decide⟩ (by decide) (![⟨1186610, by decide⟩,⟨1186656, by decide⟩,⟨1109453, by decide⟩,⟨1186671, by decide⟩]) unmarked_context_10_21242_1186672 node_context_10_21242_1186672
  intro a
  fin_cases a
  · exact context_11_84968_1186610
  · exact context_11_84969_1186656
  · exact context_11_84970_1109453
  · exact context_11_84971_1186671

theorem selected_cut_43371 : selected 10 ⟨1186729, by decide⟩
    (prefixPartial 11 84972) = some ⟨11, 2, 0, 1186729, 84972, 3165, 262144⟩ := by
  decide +kernel

theorem context_11_84972_1186729 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84972 ⟨1186729, by decide⟩ :=
  accepted_of_selected 11 84972 ⟨1186729, by decide⟩ ⟨11, 2, 0, 1186729, 84972, 3165, 262144⟩
    (by decide) selected_cut_43371

theorem selected_cut_43372 : selected 10 ⟨1186770, by decide⟩
    (prefixPartial 11 84973) = some ⟨11, 2, 0, 1186770, 84973, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_84973_1186770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84973 ⟨1186770, by decide⟩ :=
  accepted_of_selected 11 84973 ⟨1186770, by decide⟩ ⟨11, 2, 0, 1186770, 84973, 2429, 262144⟩
    (by decide) selected_cut_43372

theorem selected_cut_43373 : selected 10 ⟨1186790, by decide⟩
    (prefixPartial 11 84974) = some ⟨11, 2, 0, 1186790, 84974, 1497, 262144⟩ := by
  decide +kernel

theorem context_11_84974_1186790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84974 ⟨1186790, by decide⟩ :=
  accepted_of_selected 11 84974 ⟨1186790, by decide⟩ ⟨11, 2, 0, 1186790, 84974, 1497, 262144⟩
    (by decide) selected_cut_43373

theorem selected_cut_43374 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84975) = some ⟨11, 1, 0, 977886, 84975, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84975_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84975 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84975 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84975, 1, 262144⟩
    (by decide) selected_cut_43374

theorem unmarked_context_10_21243_1186791 : frontier 11 ⟨1186791, by decide⟩
    (prefixCache 10 21243) (prefixPartial 10 21243) = false := by
  decide +kernel

theorem node_context_10_21243_1186791 : EJMOriginalGlobalDAGData.nodes 11 ⟨1186791, by decide⟩ =
    .split (coordinate 10) (![⟨1186729, by decide⟩,⟨1186770, by decide⟩,⟨1186790, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21243_1186791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21243 ⟨1186791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21243
    ⟨1186791, by decide⟩ (by decide) (![⟨1186729, by decide⟩,⟨1186770, by decide⟩,⟨1186790, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21243_1186791 node_context_10_21243_1186791
  intro a
  fin_cases a
  · exact context_11_84972_1186729
  · exact context_11_84973_1186770
  · exact context_11_84974_1186790
  · exact context_11_84975_977886

theorem unmarked_context_9_5310_1186792 : frontier 12 ⟨1186792, by decide⟩
    (prefixCache 9 5310) (prefixPartial 9 5310) = false := by
  decide +kernel

theorem node_context_9_5310_1186792 : EJMOriginalGlobalDAGData.nodes 12 ⟨1186792, by decide⟩ =
    .split (coordinate 9) (![⟨1186331, by decide⟩,⟨1186572, by decide⟩,⟨1186672, by decide⟩,⟨1186791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5310_1186792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5310 ⟨1186792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5310
    ⟨1186792, by decide⟩ (by decide) (![⟨1186331, by decide⟩,⟨1186572, by decide⟩,⟨1186672, by decide⟩,⟨1186791, by decide⟩]) unmarked_context_9_5310_1186792 node_context_9_5310_1186792
  intro a
  fin_cases a
  · exact context_10_21240_1186331
  · exact context_10_21241_1186572
  · exact context_10_21242_1186672
  · exact context_10_21243_1186791

theorem selected_cut_43375 : selected 10 ⟨1186803, by decide⟩
    (prefixPartial 11 84976) = some ⟨11, 2, 0, 1186803, 84976, 909, 262144⟩ := by
  decide +kernel

theorem context_11_84976_1186803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84976 ⟨1186803, by decide⟩ :=
  accepted_of_selected 11 84976 ⟨1186803, by decide⟩ ⟨11, 2, 0, 1186803, 84976, 909, 262144⟩
    (by decide) selected_cut_43375

theorem selected_cut_43376 : selected 10 ⟨1186827, by decide⟩
    (prefixPartial 11 84977) = some ⟨11, 2, 0, 1186827, 84977, 1557, 262144⟩ := by
  decide +kernel

theorem context_11_84977_1186827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84977 ⟨1186827, by decide⟩ :=
  accepted_of_selected 11 84977 ⟨1186827, by decide⟩ ⟨11, 2, 0, 1186827, 84977, 1557, 262144⟩
    (by decide) selected_cut_43376

theorem selected_cut_43377 : selected 10 ⟨1186847, by decide⟩
    (prefixPartial 11 84978) = some ⟨11, 2, 0, 1186847, 84978, 1389, 262144⟩ := by
  decide +kernel

theorem context_11_84978_1186847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84978 ⟨1186847, by decide⟩ :=
  accepted_of_selected 11 84978 ⟨1186847, by decide⟩ ⟨11, 2, 0, 1186847, 84978, 1389, 262144⟩
    (by decide) selected_cut_43377

theorem selected_cut_43378 : selected 10 ⟨1186864, by decide⟩
    (prefixPartial 11 84979) = some ⟨11, 2, 0, 1186864, 84979, 825, 262144⟩ := by
  decide +kernel

theorem context_11_84979_1186864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84979 ⟨1186864, by decide⟩ :=
  accepted_of_selected 11 84979 ⟨1186864, by decide⟩ ⟨11, 2, 0, 1186864, 84979, 825, 262144⟩
    (by decide) selected_cut_43378

theorem unmarked_context_10_21244_1186865 : frontier 11 ⟨1186865, by decide⟩
    (prefixCache 10 21244) (prefixPartial 10 21244) = false := by
  decide +kernel

theorem node_context_10_21244_1186865 : EJMOriginalGlobalDAGData.nodes 11 ⟨1186865, by decide⟩ =
    .split (coordinate 10) (![⟨1186803, by decide⟩,⟨1186827, by decide⟩,⟨1186847, by decide⟩,⟨1186864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21244_1186865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21244 ⟨1186865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21244
    ⟨1186865, by decide⟩ (by decide) (![⟨1186803, by decide⟩,⟨1186827, by decide⟩,⟨1186847, by decide⟩,⟨1186864, by decide⟩]) unmarked_context_10_21244_1186865 node_context_10_21244_1186865
  intro a
  fin_cases a
  · exact context_11_84976_1186803
  · exact context_11_84977_1186827
  · exact context_11_84978_1186847
  · exact context_11_84979_1186864

theorem selected_cut_43379 : selected 11 ⟨1186904, by decide⟩
    (prefixPartial 10 21245) = some ⟨10, 2, 0, 1186904, 21245, 2173, 1048576⟩ := by
  decide +kernel

theorem context_10_21245_1186904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21245 ⟨1186904, by decide⟩ :=
  accepted_of_selected 10 21245 ⟨1186904, by decide⟩ ⟨10, 2, 0, 1186904, 21245, 2173, 1048576⟩
    (by decide) selected_cut_43379

theorem selected_cut_43380 : selected 11 ⟨1186953, by decide⟩
    (prefixPartial 10 21246) = some ⟨10, 2, 0, 1186953, 21246, 1805, 1048576⟩ := by
  decide +kernel

theorem context_10_21246_1186953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21246 ⟨1186953, by decide⟩ :=
  accepted_of_selected 10 21246 ⟨1186953, by decide⟩ ⟨10, 2, 0, 1186953, 21246, 1805, 1048576⟩
    (by decide) selected_cut_43380

theorem selected_cut_43381 : selected 11 ⟨1186970, by decide⟩
    (prefixPartial 10 21247) = some ⟨10, 2, 0, 1186970, 21247, 257, 1048576⟩ := by
  decide +kernel

theorem context_10_21247_1186970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21247 ⟨1186970, by decide⟩ :=
  accepted_of_selected 10 21247 ⟨1186970, by decide⟩ ⟨10, 2, 0, 1186970, 21247, 257, 1048576⟩
    (by decide) selected_cut_43381

theorem unmarked_context_9_5311_1186971 : frontier 12 ⟨1186971, by decide⟩
    (prefixCache 9 5311) (prefixPartial 9 5311) = false := by
  decide +kernel

theorem node_context_9_5311_1186971 : EJMOriginalGlobalDAGData.nodes 12 ⟨1186971, by decide⟩ =
    .split (coordinate 9) (![⟨1186865, by decide⟩,⟨1186904, by decide⟩,⟨1186953, by decide⟩,⟨1186970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5311_1186971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5311 ⟨1186971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5311
    ⟨1186971, by decide⟩ (by decide) (![⟨1186865, by decide⟩,⟨1186904, by decide⟩,⟨1186953, by decide⟩,⟨1186970, by decide⟩]) unmarked_context_9_5311_1186971 node_context_9_5311_1186971
  intro a
  fin_cases a
  · exact context_10_21244_1186865
  · exact context_10_21245_1186904
  · exact context_10_21246_1186953
  · exact context_10_21247_1186970

theorem unmarked_context_8_1327_1186972 : frontier 13 ⟨1186972, by decide⟩
    (prefixCache 8 1327) (prefixPartial 8 1327) = false := by
  decide +kernel

theorem node_context_8_1327_1186972 : EJMOriginalGlobalDAGData.nodes 13 ⟨1186972, by decide⟩ =
    .split (coordinate 8) (![⟨1185008, by decide⟩,⟨1186045, by decide⟩,⟨1186792, by decide⟩,⟨1186971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1327_1186972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1327 ⟨1186972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1327
    ⟨1186972, by decide⟩ (by decide) (![⟨1185008, by decide⟩,⟨1186045, by decide⟩,⟨1186792, by decide⟩,⟨1186971, by decide⟩]) unmarked_context_8_1327_1186972 node_context_8_1327_1186972
  intro a
  fin_cases a
  · exact context_9_5308_1185008
  · exact context_9_5309_1186045
  · exact context_9_5310_1186792
  · exact context_9_5311_1186971

theorem unmarked_context_7_331_1186973 : frontier 14 ⟨1186973, by decide⟩
    (prefixCache 7 331) (prefixPartial 7 331) = false := by
  decide +kernel

theorem node_context_7_331_1186973 : EJMOriginalGlobalDAGData.nodes 14 ⟨1186973, by decide⟩ =
    .split (coordinate 7) (![⟨1175470, by decide⟩,⟨1178848, by decide⟩,⟨1182813, by decide⟩,⟨1186972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_331_1186973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 331 ⟨1186973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 331
    ⟨1186973, by decide⟩ (by decide) (![⟨1175470, by decide⟩,⟨1178848, by decide⟩,⟨1182813, by decide⟩,⟨1186972, by decide⟩]) unmarked_context_7_331_1186973 node_context_7_331_1186973
  intro a
  fin_cases a
  · exact context_8_1324_1175470
  · exact context_8_1325_1178848
  · exact context_8_1326_1182813
  · exact context_8_1327_1186972

theorem unmarked_context_6_82_1186974 : frontier 15 ⟨1186974, by decide⟩
    (prefixCache 6 82) (prefixPartial 6 82) = false := by
  decide +kernel

theorem node_context_6_82_1186974 : EJMOriginalGlobalDAGData.nodes 15 ⟨1186974, by decide⟩ =
    .split (coordinate 6) (![⟨1144763, by decide⟩,⟨1158171, by decide⟩,⟨1171410, by decide⟩,⟨1186973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_82_1186974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 82 ⟨1186974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 82
    ⟨1186974, by decide⟩ (by decide) (![⟨1144763, by decide⟩,⟨1158171, by decide⟩,⟨1171410, by decide⟩,⟨1186973, by decide⟩]) unmarked_context_6_82_1186974 node_context_6_82_1186974
  intro a
  fin_cases a
  · exact context_7_328_1144763
  · exact context_7_329_1158171
  · exact context_7_330_1171410
  · exact context_7_331_1186973

theorem selected_cut_43382 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 83) = some ⟨6, 1, 0, 116314, 83, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_83_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 83 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 83 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 83, 1, 268435456⟩
    (by decide) selected_cut_43382

theorem unmarked_context_5_20_1186975 : frontier 16 ⟨1186975, by decide⟩
    (prefixCache 5 20) (prefixPartial 5 20) = false := by
  decide +kernel

theorem node_context_5_20_1186975 : EJMOriginalGlobalDAGData.nodes 16 ⟨1186975, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨1132280, by decide⟩,⟨1186974, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_20_1186975 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 20 ⟨1186975, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 20
    ⟨1186975, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨1132280, by decide⟩,⟨1186974, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_20_1186975 node_context_5_20_1186975
  intro a
  fin_cases a
  · exact context_6_80_434744
  · exact context_6_81_1132280
  · exact context_6_82_1186974
  · exact context_6_83_116314

theorem selected_cut_43383 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 84) = some ⟨6, 1, 0, 434744, 84, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_84_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 84 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 84 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 84, 1, 268435456⟩
    (by decide) selected_cut_43383

theorem selected_cut_43384 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 340) = some ⟨7, 1, 0, 116316, 340, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_340_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 340 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 340 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 340, 1, 67108864⟩
    (by decide) selected_cut_43384

theorem selected_cut_43385 : selected 13 ⟨643294, by decide⟩
    (prefixPartial 8 1364) = some ⟨8, 1, 0, 643294, 1364, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1364_643294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1364 ⟨643294, by decide⟩ :=
  accepted_of_selected 8 1364 ⟨643294, by decide⟩ ⟨8, 1, 0, 643294, 1364, 1, 16777216⟩
    (by decide) selected_cut_43385

theorem selected_cut_43386 : selected 13 ⟨1109534, by decide⟩
    (prefixPartial 8 1365) = some ⟨8, 1, 0, 1109534, 1365, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1365_1109534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1365 ⟨1109534, by decide⟩ :=
  accepted_of_selected 8 1365 ⟨1109534, by decide⟩ ⟨8, 1, 0, 1109534, 1365, 1, 16777216⟩
    (by decide) selected_cut_43386

theorem selected_cut_43387 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 87424) = some ⟨11, 1, 0, 434745, 87424, 1, 262144⟩ := by
  decide +kernel

theorem context_11_87424_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87424 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 87424 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 87424, 1, 262144⟩
    (by decide) selected_cut_43387

theorem selected_cut_43388 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 349700) = some ⟨12, 1, 0, 895, 349700, 1, 65536⟩ := by
  decide +kernel

theorem context_12_349700_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349700 ⟨895, by decide⟩ :=
  accepted_of_selected 12 349700 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 349700, 1, 65536⟩
    (by decide) selected_cut_43388

theorem selected_cut_43389 : selected 9 ⟨1187026, by decide⟩
    (prefixPartial 12 349701) = some ⟨12, 2, 0, 1187026, 349701, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_349701_1187026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349701 ⟨1187026, by decide⟩ :=
  accepted_of_selected 12 349701 ⟨1187026, by decide⟩ ⟨12, 2, 0, 1187026, 349701, 1421, 65536⟩
    (by decide) selected_cut_43389

theorem selected_cut_43390 : selected 9 ⟨1187077, by decide⟩
    (prefixPartial 12 349702) = some ⟨12, 2, 0, 1187077, 349702, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_349702_1187077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349702 ⟨1187077, by decide⟩ :=
  accepted_of_selected 12 349702 ⟨1187077, by decide⟩ ⟨12, 2, 0, 1187077, 349702, 2201, 65536⟩
    (by decide) selected_cut_43390

theorem selected_cut_43391 : selected 9 ⟨1187128, by decide⟩
    (prefixPartial 12 349703) = some ⟨12, 2, 0, 1187128, 349703, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_349703_1187128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 349703 ⟨1187128, by decide⟩ :=
  accepted_of_selected 12 349703 ⟨1187128, by decide⟩ ⟨12, 2, 0, 1187128, 349703, 2313, 65536⟩
    (by decide) selected_cut_43391

theorem unmarked_context_11_87425_1187129 : frontier 10 ⟨1187129, by decide⟩
    (prefixCache 11 87425) (prefixPartial 11 87425) = false := by
  decide +kernel

theorem node_context_11_87425_1187129 : EJMOriginalGlobalDAGData.nodes 10 ⟨1187129, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨1187026, by decide⟩,⟨1187077, by decide⟩,⟨1187128, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_87425_1187129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87425 ⟨1187129, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 87425
    ⟨1187129, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨1187026, by decide⟩,⟨1187077, by decide⟩,⟨1187128, by decide⟩]) unmarked_context_11_87425_1187129 node_context_11_87425_1187129
  intro a
  fin_cases a
  · exact context_12_349700_895
  · exact context_12_349701_1187026
  · exact context_12_349702_1187077
  · exact context_12_349703_1187128

theorem selected_cut_43392 : selected 10 ⟨1187186, by decide⟩
    (prefixPartial 11 87426) = some ⟨11, 2, 0, 1187186, 87426, 2989, 262144⟩ := by
  decide +kernel

theorem context_11_87426_1187186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87426 ⟨1187186, by decide⟩ :=
  accepted_of_selected 11 87426 ⟨1187186, by decide⟩ ⟨11, 2, 0, 1187186, 87426, 2989, 262144⟩
    (by decide) selected_cut_43392

theorem selected_cut_43393 : selected 10 ⟨1187230, by decide⟩
    (prefixPartial 11 87427) = some ⟨11, 2, 0, 1187230, 87427, 1537, 262144⟩ := by
  decide +kernel

theorem context_11_87427_1187230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 87427 ⟨1187230, by decide⟩ :=
  accepted_of_selected 11 87427 ⟨1187230, by decide⟩ ⟨11, 2, 0, 1187230, 87427, 1537, 262144⟩
    (by decide) selected_cut_43393

theorem unmarked_context_10_21856_1187231 : frontier 11 ⟨1187231, by decide⟩
    (prefixCache 10 21856) (prefixPartial 10 21856) = false := by
  decide +kernel

theorem node_context_10_21856_1187231 : EJMOriginalGlobalDAGData.nodes 11 ⟨1187231, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1187129, by decide⟩,⟨1187186, by decide⟩,⟨1187230, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21856_1187231 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21856 ⟨1187231, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21856
    ⟨1187231, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1187129, by decide⟩,⟨1187186, by decide⟩,⟨1187230, by decide⟩]) unmarked_context_10_21856_1187231 node_context_10_21856_1187231
  intro a
  fin_cases a
  · exact context_11_87424_434745
  · exact context_11_87425_1187129
  · exact context_11_87426_1187186
  · exact context_11_87427_1187230

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
