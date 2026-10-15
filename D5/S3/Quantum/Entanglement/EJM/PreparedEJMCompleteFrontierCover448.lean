/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover447
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_43011 : selected 9 ⟨1176055, by decide⟩
    (prefixPartial 12 339219) = some ⟨12, 2, 0, 1176055, 339219, 2929, 65536⟩ := by
  decide +kernel

theorem context_12_339219_1176055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339219 ⟨1176055, by decide⟩ :=
  accepted_of_selected 12 339219 ⟨1176055, by decide⟩ ⟨12, 2, 0, 1176055, 339219, 2929, 65536⟩
    (by decide) selected_cut_43011

theorem unmarked_context_11_84804_1176056 : frontier 10 ⟨1176056, by decide⟩
    (prefixCache 11 84804) (prefixPartial 11 84804) = false := by
  decide +kernel

theorem node_context_11_84804_1176056 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176056, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1175939, by decide⟩,⟨1175993, by decide⟩,⟨1176055, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84804_1176056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84804 ⟨1176056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84804
    ⟨1176056, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1175939, by decide⟩,⟨1175993, by decide⟩,⟨1176055, by decide⟩]) unmarked_context_11_84804_1176056 node_context_11_84804_1176056
  intro a
  fin_cases a
  · exact context_12_339216_1108174
  · exact context_12_339217_1175939
  · exact context_12_339218_1175993
  · exact context_12_339219_1176055

theorem selected_cut_43012 : selected 10 ⟨1176112, by decide⟩
    (prefixPartial 11 84805) = some ⟨11, 2, 0, 1176112, 84805, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_84805_1176112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84805 ⟨1176112, by decide⟩ :=
  accepted_of_selected 11 84805 ⟨1176112, by decide⟩ ⟨11, 2, 0, 1176112, 84805, 2725, 262144⟩
    (by decide) selected_cut_43012

theorem selected_cut_43013 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339224) = some ⟨12, 1, 0, 1108174, 339224, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339224_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339224 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339224 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339224, 1, 65536⟩
    (by decide) selected_cut_43013

theorem selected_cut_43014 : selected 9 ⟨1176167, by decide⟩
    (prefixPartial 12 339225) = some ⟨12, 2, 0, 1176167, 339225, 2653, 65536⟩ := by
  decide +kernel

theorem context_12_339225_1176167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339225 ⟨1176167, by decide⟩ :=
  accepted_of_selected 12 339225 ⟨1176167, by decide⟩ ⟨12, 2, 0, 1176167, 339225, 2653, 65536⟩
    (by decide) selected_cut_43014

theorem selected_cut_43015 : selected 9 ⟨1176216, by decide⟩
    (prefixPartial 12 339226) = some ⟨12, 2, 0, 1176216, 339226, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_339226_1176216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339226 ⟨1176216, by decide⟩ :=
  accepted_of_selected 12 339226 ⟨1176216, by decide⟩ ⟨12, 2, 0, 1176216, 339226, 2481, 65536⟩
    (by decide) selected_cut_43015

theorem selected_cut_43016 : selected 9 ⟨1176263, by decide⟩
    (prefixPartial 12 339227) = some ⟨12, 2, 0, 1176263, 339227, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_339227_1176263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339227 ⟨1176263, by decide⟩ :=
  accepted_of_selected 12 339227 ⟨1176263, by decide⟩ ⟨12, 2, 0, 1176263, 339227, 2733, 65536⟩
    (by decide) selected_cut_43016

theorem unmarked_context_11_84806_1176264 : frontier 10 ⟨1176264, by decide⟩
    (prefixCache 11 84806) (prefixPartial 11 84806) = false := by
  decide +kernel

theorem node_context_11_84806_1176264 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176264, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1176167, by decide⟩,⟨1176216, by decide⟩,⟨1176263, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84806_1176264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84806 ⟨1176264, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84806
    ⟨1176264, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1176167, by decide⟩,⟨1176216, by decide⟩,⟨1176263, by decide⟩]) unmarked_context_11_84806_1176264 node_context_11_84806_1176264
  intro a
  fin_cases a
  · exact context_12_339224_1108174
  · exact context_12_339225_1176167
  · exact context_12_339226_1176216
  · exact context_12_339227_1176263

theorem selected_cut_43017 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339228) = some ⟨12, 1, 0, 1108174, 339228, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339228_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339228 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339228 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339228, 1, 65536⟩
    (by decide) selected_cut_43017

theorem selected_cut_43018 : selected 9 ⟨1176302, by decide⟩
    (prefixPartial 12 339229) = some ⟨12, 2, 0, 1176302, 339229, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_339229_1176302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339229 ⟨1176302, by decide⟩ :=
  accepted_of_selected 12 339229 ⟨1176302, by decide⟩ ⟨12, 2, 0, 1176302, 339229, 2193, 65536⟩
    (by decide) selected_cut_43018

theorem selected_cut_43019 : selected 9 ⟨1176334, by decide⟩
    (prefixPartial 12 339230) = some ⟨12, 2, 0, 1176334, 339230, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_339230_1176334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339230 ⟨1176334, by decide⟩ :=
  accepted_of_selected 12 339230 ⟨1176334, by decide⟩ ⟨12, 2, 0, 1176334, 339230, 2141, 65536⟩
    (by decide) selected_cut_43019

theorem selected_cut_43020 : selected 9 ⟨632897, by decide⟩
    (prefixPartial 12 339231) = some ⟨12, 1, 0, 632897, 339231, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339231_632897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339231 ⟨632897, by decide⟩ :=
  accepted_of_selected 12 339231 ⟨632897, by decide⟩ ⟨12, 1, 0, 632897, 339231, 1, 65536⟩
    (by decide) selected_cut_43020

theorem unmarked_context_11_84807_1176335 : frontier 10 ⟨1176335, by decide⟩
    (prefixCache 11 84807) (prefixPartial 11 84807) = false := by
  decide +kernel

theorem node_context_11_84807_1176335 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176335, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1176302, by decide⟩,⟨1176334, by decide⟩,⟨632897, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84807_1176335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84807 ⟨1176335, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84807
    ⟨1176335, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1176302, by decide⟩,⟨1176334, by decide⟩,⟨632897, by decide⟩]) unmarked_context_11_84807_1176335 node_context_11_84807_1176335
  intro a
  fin_cases a
  · exact context_12_339228_1108174
  · exact context_12_339229_1176302
  · exact context_12_339230_1176334
  · exact context_12_339231_632897

theorem unmarked_context_10_21201_1176336 : frontier 11 ⟨1176336, by decide⟩
    (prefixCache 10 21201) (prefixPartial 10 21201) = false := by
  decide +kernel

theorem node_context_10_21201_1176336 : EJMOriginalGlobalDAGData.nodes 11 ⟨1176336, by decide⟩ =
    .split (coordinate 10) (![⟨1176056, by decide⟩,⟨1176112, by decide⟩,⟨1176264, by decide⟩,⟨1176335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21201_1176336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21201 ⟨1176336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21201
    ⟨1176336, by decide⟩ (by decide) (![⟨1176056, by decide⟩,⟨1176112, by decide⟩,⟨1176264, by decide⟩,⟨1176335, by decide⟩]) unmarked_context_10_21201_1176336 node_context_10_21201_1176336
  intro a
  fin_cases a
  · exact context_11_84804_1176056
  · exact context_11_84805_1176112
  · exact context_11_84806_1176264
  · exact context_11_84807_1176335

theorem selected_cut_43021 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339232) = some ⟨12, 1, 0, 1108174, 339232, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339232_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339232 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339232 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339232, 1, 65536⟩
    (by decide) selected_cut_43021

theorem selected_cut_43022 : selected 9 ⟨1176395, by decide⟩
    (prefixPartial 12 339233) = some ⟨12, 2, 0, 1176395, 339233, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_339233_1176395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339233 ⟨1176395, by decide⟩ :=
  accepted_of_selected 12 339233 ⟨1176395, by decide⟩ ⟨12, 2, 0, 1176395, 339233, 2809, 65536⟩
    (by decide) selected_cut_43022

theorem selected_cut_43023 : selected 9 ⟨1176433, by decide⟩
    (prefixPartial 12 339234) = some ⟨12, 2, 0, 1176433, 339234, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_339234_1176433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339234 ⟨1176433, by decide⟩ :=
  accepted_of_selected 12 339234 ⟨1176433, by decide⟩ ⟨12, 2, 0, 1176433, 339234, 2421, 65536⟩
    (by decide) selected_cut_43023

theorem selected_cut_43024 : selected 9 ⟨1176479, by decide⟩
    (prefixPartial 12 339235) = some ⟨12, 2, 0, 1176479, 339235, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_339235_1176479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339235 ⟨1176479, by decide⟩ :=
  accepted_of_selected 12 339235 ⟨1176479, by decide⟩ ⟨12, 2, 0, 1176479, 339235, 2645, 65536⟩
    (by decide) selected_cut_43024

theorem unmarked_context_11_84808_1176480 : frontier 10 ⟨1176480, by decide⟩
    (prefixCache 11 84808) (prefixPartial 11 84808) = false := by
  decide +kernel

theorem node_context_11_84808_1176480 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176480, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1176395, by decide⟩,⟨1176433, by decide⟩,⟨1176479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84808_1176480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84808 ⟨1176480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84808
    ⟨1176480, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1176395, by decide⟩,⟨1176433, by decide⟩,⟨1176479, by decide⟩]) unmarked_context_11_84808_1176480 node_context_11_84808_1176480
  intro a
  fin_cases a
  · exact context_12_339232_1108174
  · exact context_12_339233_1176395
  · exact context_12_339234_1176433
  · exact context_12_339235_1176479

theorem selected_cut_43025 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339236) = some ⟨12, 1, 0, 1108174, 339236, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339236_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339236 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339236 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339236, 1, 65536⟩
    (by decide) selected_cut_43025

theorem selected_cut_43026 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 339237) = some ⟨12, 1, 0, 891951, 339237, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339237_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339237 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 339237 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 339237, 1, 65536⟩
    (by decide) selected_cut_43026

theorem selected_cut_43027 : selected 9 ⟨1176528, by decide⟩
    (prefixPartial 12 339238) = some ⟨12, 2, 0, 1176528, 339238, 2533, 65536⟩ := by
  decide +kernel

theorem context_12_339238_1176528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339238 ⟨1176528, by decide⟩ :=
  accepted_of_selected 12 339238 ⟨1176528, by decide⟩ ⟨12, 2, 0, 1176528, 339238, 2533, 65536⟩
    (by decide) selected_cut_43027

theorem selected_cut_43028 : selected 9 ⟨1176577, by decide⟩
    (prefixPartial 12 339239) = some ⟨12, 2, 0, 1176577, 339239, 2697, 65536⟩ := by
  decide +kernel

theorem context_12_339239_1176577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339239 ⟨1176577, by decide⟩ :=
  accepted_of_selected 12 339239 ⟨1176577, by decide⟩ ⟨12, 2, 0, 1176577, 339239, 2697, 65536⟩
    (by decide) selected_cut_43028

theorem unmarked_context_11_84809_1176578 : frontier 10 ⟨1176578, by decide⟩
    (prefixCache 11 84809) (prefixPartial 11 84809) = false := by
  decide +kernel

theorem node_context_11_84809_1176578 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176578, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1176528, by decide⟩,⟨1176577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84809_1176578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84809 ⟨1176578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84809
    ⟨1176578, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1176528, by decide⟩,⟨1176577, by decide⟩]) unmarked_context_11_84809_1176578 node_context_11_84809_1176578
  intro a
  fin_cases a
  · exact context_12_339236_1108174
  · exact context_12_339237_891951
  · exact context_12_339238_1176528
  · exact context_12_339239_1176577

theorem selected_cut_43029 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339240) = some ⟨12, 1, 0, 1108174, 339240, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339240_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339240 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339240 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339240, 1, 65536⟩
    (by decide) selected_cut_43029

theorem selected_cut_43030 : selected 9 ⟨1176625, by decide⟩
    (prefixPartial 12 339241) = some ⟨12, 2, 0, 1176625, 339241, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_339241_1176625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339241 ⟨1176625, by decide⟩ :=
  accepted_of_selected 12 339241 ⟨1176625, by decide⟩ ⟨12, 2, 0, 1176625, 339241, 2497, 65536⟩
    (by decide) selected_cut_43030

theorem selected_cut_43031 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 339242) = some ⟨12, 1, 0, 1172910, 339242, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339242_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339242 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 339242 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 339242, 1, 65536⟩
    (by decide) selected_cut_43031

theorem selected_cut_43032 : selected 9 ⟨1176668, by decide⟩
    (prefixPartial 12 339243) = some ⟨12, 2, 0, 1176668, 339243, 2557, 65536⟩ := by
  decide +kernel

theorem context_12_339243_1176668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339243 ⟨1176668, by decide⟩ :=
  accepted_of_selected 12 339243 ⟨1176668, by decide⟩ ⟨12, 2, 0, 1176668, 339243, 2557, 65536⟩
    (by decide) selected_cut_43032

theorem unmarked_context_11_84810_1176669 : frontier 10 ⟨1176669, by decide⟩
    (prefixCache 11 84810) (prefixPartial 11 84810) = false := by
  decide +kernel

theorem node_context_11_84810_1176669 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176669, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1176625, by decide⟩,⟨1172910, by decide⟩,⟨1176668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84810_1176669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84810 ⟨1176669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84810
    ⟨1176669, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1176625, by decide⟩,⟨1172910, by decide⟩,⟨1176668, by decide⟩]) unmarked_context_11_84810_1176669 node_context_11_84810_1176669
  intro a
  fin_cases a
  · exact context_12_339240_1108174
  · exact context_12_339241_1176625
  · exact context_12_339242_1172910
  · exact context_12_339243_1176668

theorem selected_cut_43033 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339244) = some ⟨12, 1, 0, 1108174, 339244, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339244_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339244 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339244 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339244, 1, 65536⟩
    (by decide) selected_cut_43033

theorem selected_cut_43034 : selected 9 ⟨1176702, by decide⟩
    (prefixPartial 12 339245) = some ⟨12, 2, 0, 1176702, 339245, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_339245_1176702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339245 ⟨1176702, by decide⟩ :=
  accepted_of_selected 12 339245 ⟨1176702, by decide⟩ ⟨12, 2, 0, 1176702, 339245, 2089, 65536⟩
    (by decide) selected_cut_43034

theorem selected_cut_43035 : selected 9 ⟨1176727, by decide⟩
    (prefixPartial 12 339246) = some ⟨12, 2, 0, 1176727, 339246, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_339246_1176727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339246 ⟨1176727, by decide⟩ :=
  accepted_of_selected 12 339246 ⟨1176727, by decide⟩ ⟨12, 2, 0, 1176727, 339246, 1893, 65536⟩
    (by decide) selected_cut_43035

theorem selected_cut_43036 : selected 9 ⟨1176762, by decide⟩
    (prefixPartial 12 339247) = some ⟨12, 2, 0, 1176762, 339247, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_339247_1176762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339247 ⟨1176762, by decide⟩ :=
  accepted_of_selected 12 339247 ⟨1176762, by decide⟩ ⟨12, 2, 0, 1176762, 339247, 2277, 65536⟩
    (by decide) selected_cut_43036

theorem unmarked_context_11_84811_1176763 : frontier 10 ⟨1176763, by decide⟩
    (prefixCache 11 84811) (prefixPartial 11 84811) = false := by
  decide +kernel

theorem node_context_11_84811_1176763 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176763, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1176702, by decide⟩,⟨1176727, by decide⟩,⟨1176762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84811_1176763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84811 ⟨1176763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84811
    ⟨1176763, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1176702, by decide⟩,⟨1176727, by decide⟩,⟨1176762, by decide⟩]) unmarked_context_11_84811_1176763 node_context_11_84811_1176763
  intro a
  fin_cases a
  · exact context_12_339244_1108174
  · exact context_12_339245_1176702
  · exact context_12_339246_1176727
  · exact context_12_339247_1176762

theorem unmarked_context_10_21202_1176764 : frontier 11 ⟨1176764, by decide⟩
    (prefixCache 10 21202) (prefixPartial 10 21202) = false := by
  decide +kernel

theorem node_context_10_21202_1176764 : EJMOriginalGlobalDAGData.nodes 11 ⟨1176764, by decide⟩ =
    .split (coordinate 10) (![⟨1176480, by decide⟩,⟨1176578, by decide⟩,⟨1176669, by decide⟩,⟨1176763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21202_1176764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21202 ⟨1176764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21202
    ⟨1176764, by decide⟩ (by decide) (![⟨1176480, by decide⟩,⟨1176578, by decide⟩,⟨1176669, by decide⟩,⟨1176763, by decide⟩]) unmarked_context_10_21202_1176764 node_context_10_21202_1176764
  intro a
  fin_cases a
  · exact context_11_84808_1176480
  · exact context_11_84809_1176578
  · exact context_11_84810_1176669
  · exact context_11_84811_1176763

theorem selected_cut_43037 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339248) = some ⟨12, 1, 0, 1108174, 339248, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339248_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339248 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339248 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339248, 1, 65536⟩
    (by decide) selected_cut_43037

theorem selected_cut_43038 : selected 9 ⟨1176809, by decide⟩
    (prefixPartial 12 339249) = some ⟨12, 2, 0, 1176809, 339249, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_339249_1176809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339249 ⟨1176809, by decide⟩ :=
  accepted_of_selected 12 339249 ⟨1176809, by decide⟩ ⟨12, 2, 0, 1176809, 339249, 2373, 65536⟩
    (by decide) selected_cut_43038

theorem selected_cut_43039 : selected 9 ⟨1176839, by decide⟩
    (prefixPartial 12 339250) = some ⟨12, 2, 0, 1176839, 339250, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_339250_1176839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339250 ⟨1176839, by decide⟩ :=
  accepted_of_selected 12 339250 ⟨1176839, by decide⟩ ⟨12, 2, 0, 1176839, 339250, 1993, 65536⟩
    (by decide) selected_cut_43039

theorem selected_cut_43040 : selected 9 ⟨1176885, by decide⟩
    (prefixPartial 12 339251) = some ⟨12, 2, 0, 1176885, 339251, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_339251_1176885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339251 ⟨1176885, by decide⟩ :=
  accepted_of_selected 12 339251 ⟨1176885, by decide⟩ ⟨12, 2, 0, 1176885, 339251, 2457, 65536⟩
    (by decide) selected_cut_43040

theorem unmarked_context_11_84812_1176886 : frontier 10 ⟨1176886, by decide⟩
    (prefixCache 11 84812) (prefixPartial 11 84812) = false := by
  decide +kernel

theorem node_context_11_84812_1176886 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176886, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1176809, by decide⟩,⟨1176839, by decide⟩,⟨1176885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84812_1176886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84812 ⟨1176886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84812
    ⟨1176886, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1176809, by decide⟩,⟨1176839, by decide⟩,⟨1176885, by decide⟩]) unmarked_context_11_84812_1176886 node_context_11_84812_1176886
  intro a
  fin_cases a
  · exact context_12_339248_1108174
  · exact context_12_339249_1176809
  · exact context_12_339250_1176839
  · exact context_12_339251_1176885

theorem selected_cut_43041 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339252) = some ⟨12, 1, 0, 1108174, 339252, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339252_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339252 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339252 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339252, 1, 65536⟩
    (by decide) selected_cut_43041

theorem selected_cut_43042 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 339253) = some ⟨12, 1, 0, 891951, 339253, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339253_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339253 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 339253 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 339253, 1, 65536⟩
    (by decide) selected_cut_43042

theorem selected_cut_43043 : selected 9 ⟨1176918, by decide⟩
    (prefixPartial 12 339254) = some ⟨12, 2, 0, 1176918, 339254, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_339254_1176918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339254 ⟨1176918, by decide⟩ :=
  accepted_of_selected 12 339254 ⟨1176918, by decide⟩ ⟨12, 2, 0, 1176918, 339254, 2045, 65536⟩
    (by decide) selected_cut_43043

theorem selected_cut_43044 : selected 9 ⟨1176960, by decide⟩
    (prefixPartial 12 339255) = some ⟨12, 2, 0, 1176960, 339255, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_339255_1176960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339255 ⟨1176960, by decide⟩ :=
  accepted_of_selected 12 339255 ⟨1176960, by decide⟩ ⟨12, 2, 0, 1176960, 339255, 2345, 65536⟩
    (by decide) selected_cut_43044

theorem unmarked_context_11_84813_1176961 : frontier 10 ⟨1176961, by decide⟩
    (prefixCache 11 84813) (prefixPartial 11 84813) = false := by
  decide +kernel

theorem node_context_11_84813_1176961 : EJMOriginalGlobalDAGData.nodes 10 ⟨1176961, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1176918, by decide⟩,⟨1176960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84813_1176961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84813 ⟨1176961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84813
    ⟨1176961, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨891951, by decide⟩,⟨1176918, by decide⟩,⟨1176960, by decide⟩]) unmarked_context_11_84813_1176961 node_context_11_84813_1176961
  intro a
  fin_cases a
  · exact context_12_339252_1108174
  · exact context_12_339253_891951
  · exact context_12_339254_1176918
  · exact context_12_339255_1176960

theorem selected_cut_43045 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 339256) = some ⟨12, 1, 0, 1108174, 339256, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339256_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339256 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 339256 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 339256, 1, 65536⟩
    (by decide) selected_cut_43045

theorem selected_cut_43046 : selected 9 ⟨1176994, by decide⟩
    (prefixPartial 12 339257) = some ⟨12, 2, 0, 1176994, 339257, 2129, 65536⟩ := by
  decide +kernel

theorem context_12_339257_1176994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339257 ⟨1176994, by decide⟩ :=
  accepted_of_selected 12 339257 ⟨1176994, by decide⟩ ⟨12, 2, 0, 1176994, 339257, 2129, 65536⟩
    (by decide) selected_cut_43046

theorem selected_cut_43047 : selected 9 ⟨1177020, by decide⟩
    (prefixPartial 12 339258) = some ⟨12, 2, 0, 1177020, 339258, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_339258_1177020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339258 ⟨1177020, by decide⟩ :=
  accepted_of_selected 12 339258 ⟨1177020, by decide⟩ ⟨12, 2, 0, 1177020, 339258, 1833, 65536⟩
    (by decide) selected_cut_43047

theorem selected_cut_43048 : selected 9 ⟨1177054, by decide⟩
    (prefixPartial 12 339259) = some ⟨12, 2, 0, 1177054, 339259, 2197, 65536⟩ := by
  decide +kernel

theorem context_12_339259_1177054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339259 ⟨1177054, by decide⟩ :=
  accepted_of_selected 12 339259 ⟨1177054, by decide⟩ ⟨12, 2, 0, 1177054, 339259, 2197, 65536⟩
    (by decide) selected_cut_43048

theorem unmarked_context_11_84814_1177055 : frontier 10 ⟨1177055, by decide⟩
    (prefixCache 11 84814) (prefixPartial 11 84814) = false := by
  decide +kernel

theorem node_context_11_84814_1177055 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177055, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1176994, by decide⟩,⟨1177020, by decide⟩,⟨1177054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84814_1177055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84814 ⟨1177055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84814
    ⟨1177055, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1176994, by decide⟩,⟨1177020, by decide⟩,⟨1177054, by decide⟩]) unmarked_context_11_84814_1177055 node_context_11_84814_1177055
  intro a
  fin_cases a
  · exact context_12_339256_1108174
  · exact context_12_339257_1176994
  · exact context_12_339258_1177020
  · exact context_12_339259_1177054

theorem selected_cut_43049 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84815) = some ⟨11, 1, 0, 977886, 84815, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84815_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84815 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84815 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84815, 1, 262144⟩
    (by decide) selected_cut_43049

theorem unmarked_context_10_21203_1177056 : frontier 11 ⟨1177056, by decide⟩
    (prefixCache 10 21203) (prefixPartial 10 21203) = false := by
  decide +kernel

theorem node_context_10_21203_1177056 : EJMOriginalGlobalDAGData.nodes 11 ⟨1177056, by decide⟩ =
    .split (coordinate 10) (![⟨1176886, by decide⟩,⟨1176961, by decide⟩,⟨1177055, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21203_1177056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21203 ⟨1177056, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21203
    ⟨1177056, by decide⟩ (by decide) (![⟨1176886, by decide⟩,⟨1176961, by decide⟩,⟨1177055, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21203_1177056 node_context_10_21203_1177056
  intro a
  fin_cases a
  · exact context_11_84812_1176886
  · exact context_11_84813_1176961
  · exact context_11_84814_1177055
  · exact context_11_84815_977886

theorem unmarked_context_9_5300_1177057 : frontier 12 ⟨1177057, by decide⟩
    (prefixCache 9 5300) (prefixPartial 9 5300) = false := by
  decide +kernel

theorem node_context_9_5300_1177057 : EJMOriginalGlobalDAGData.nodes 12 ⟨1177057, by decide⟩ =
    .split (coordinate 9) (![⟨1175873, by decide⟩,⟨1176336, by decide⟩,⟨1176764, by decide⟩,⟨1177056, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5300_1177057 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5300 ⟨1177057, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5300
    ⟨1177057, by decide⟩ (by decide) (![⟨1175873, by decide⟩,⟨1176336, by decide⟩,⟨1176764, by decide⟩,⟨1177056, by decide⟩]) unmarked_context_9_5300_1177057 node_context_9_5300_1177057
  intro a
  fin_cases a
  · exact context_10_21200_1175873
  · exact context_10_21201_1176336
  · exact context_10_21202_1176764
  · exact context_10_21203_1177056

theorem selected_cut_43050 : selected 9 ⟨1173556, by decide⟩
    (prefixPartial 12 339264) = some ⟨12, 1, 0, 1173556, 339264, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339264_1173556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339264 ⟨1173556, by decide⟩ :=
  accepted_of_selected 12 339264 ⟨1173556, by decide⟩ ⟨12, 1, 0, 1173556, 339264, 1, 65536⟩
    (by decide) selected_cut_43050

theorem selected_cut_43051 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 339265) = some ⟨12, 1, 0, 170504, 339265, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339265_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339265 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 339265 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 339265, 1, 65536⟩
    (by decide) selected_cut_43051

theorem selected_cut_43052 : selected 9 ⟨1177097, by decide⟩
    (prefixPartial 12 339266) = some ⟨12, 2, 0, 1177097, 339266, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_339266_1177097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339266 ⟨1177097, by decide⟩ :=
  accepted_of_selected 12 339266 ⟨1177097, by decide⟩ ⟨12, 2, 0, 1177097, 339266, 2057, 65536⟩
    (by decide) selected_cut_43052

theorem selected_cut_43053 : selected 9 ⟨1177133, by decide⟩
    (prefixPartial 12 339267) = some ⟨12, 2, 0, 1177133, 339267, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_339267_1177133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339267 ⟨1177133, by decide⟩ :=
  accepted_of_selected 12 339267 ⟨1177133, by decide⟩ ⟨12, 2, 0, 1177133, 339267, 2141, 65536⟩
    (by decide) selected_cut_43053

theorem unmarked_context_11_84816_1177134 : frontier 10 ⟨1177134, by decide⟩
    (prefixCache 11 84816) (prefixPartial 11 84816) = false := by
  decide +kernel

theorem node_context_11_84816_1177134 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177134, by decide⟩ =
    .split (coordinate 11) (![⟨1173556, by decide⟩,⟨170504, by decide⟩,⟨1177097, by decide⟩,⟨1177133, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84816_1177134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84816 ⟨1177134, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84816
    ⟨1177134, by decide⟩ (by decide) (![⟨1173556, by decide⟩,⟨170504, by decide⟩,⟨1177097, by decide⟩,⟨1177133, by decide⟩]) unmarked_context_11_84816_1177134 node_context_11_84816_1177134
  intro a
  fin_cases a
  · exact context_12_339264_1173556
  · exact context_12_339265_170504
  · exact context_12_339266_1177097
  · exact context_12_339267_1177133

theorem selected_cut_43054 : selected 9 ⟨1177160, by decide⟩
    (prefixPartial 12 339268) = some ⟨12, 2, 0, 1177160, 339268, 1661, 65536⟩ := by
  decide +kernel

theorem context_12_339268_1177160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339268 ⟨1177160, by decide⟩ :=
  accepted_of_selected 12 339268 ⟨1177160, by decide⟩ ⟨12, 2, 0, 1177160, 339268, 1661, 65536⟩
    (by decide) selected_cut_43054

theorem selected_cut_43055 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 339269) = some ⟨12, 1, 0, 170504, 339269, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339269_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339269 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 339269 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 339269, 1, 65536⟩
    (by decide) selected_cut_43055

theorem selected_cut_43056 : selected 9 ⟨1177191, by decide⟩
    (prefixPartial 12 339270) = some ⟨12, 2, 0, 1177191, 339270, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_339270_1177191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339270 ⟨1177191, by decide⟩ :=
  accepted_of_selected 12 339270 ⟨1177191, by decide⟩ ⟨12, 2, 0, 1177191, 339270, 1813, 65536⟩
    (by decide) selected_cut_43056

theorem selected_cut_43057 : selected 9 ⟨1177224, by decide⟩
    (prefixPartial 12 339271) = some ⟨12, 2, 0, 1177224, 339271, 1897, 65536⟩ := by
  decide +kernel

theorem context_12_339271_1177224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339271 ⟨1177224, by decide⟩ :=
  accepted_of_selected 12 339271 ⟨1177224, by decide⟩ ⟨12, 2, 0, 1177224, 339271, 1897, 65536⟩
    (by decide) selected_cut_43057

theorem unmarked_context_11_84817_1177225 : frontier 10 ⟨1177225, by decide⟩
    (prefixCache 11 84817) (prefixPartial 11 84817) = false := by
  decide +kernel

theorem node_context_11_84817_1177225 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177225, by decide⟩ =
    .split (coordinate 11) (![⟨1177160, by decide⟩,⟨170504, by decide⟩,⟨1177191, by decide⟩,⟨1177224, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84817_1177225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84817 ⟨1177225, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84817
    ⟨1177225, by decide⟩ (by decide) (![⟨1177160, by decide⟩,⟨170504, by decide⟩,⟨1177191, by decide⟩,⟨1177224, by decide⟩]) unmarked_context_11_84817_1177225 node_context_11_84817_1177225
  intro a
  fin_cases a
  · exact context_12_339268_1177160
  · exact context_12_339269_170504
  · exact context_12_339270_1177191
  · exact context_12_339271_1177224

theorem selected_cut_43058 : selected 9 ⟨1177247, by decide⟩
    (prefixPartial 12 339272) = some ⟨12, 2, 0, 1177247, 339272, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_339272_1177247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339272 ⟨1177247, by decide⟩ :=
  accepted_of_selected 12 339272 ⟨1177247, by decide⟩ ⟨12, 2, 0, 1177247, 339272, 1589, 65536⟩
    (by decide) selected_cut_43058

theorem selected_cut_43059 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 339273) = some ⟨12, 1, 0, 126371, 339273, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339273_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339273 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 339273 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 339273, 1, 65536⟩
    (by decide) selected_cut_43059

theorem selected_cut_43060 : selected 9 ⟨1177284, by decide⟩
    (prefixPartial 12 339274) = some ⟨12, 2, 0, 1177284, 339274, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_339274_1177284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339274 ⟨1177284, by decide⟩ :=
  accepted_of_selected 12 339274 ⟨1177284, by decide⟩ ⟨12, 2, 0, 1177284, 339274, 1853, 65536⟩
    (by decide) selected_cut_43060

theorem selected_cut_43061 : selected 9 ⟨1177314, by decide⟩
    (prefixPartial 12 339275) = some ⟨12, 2, 0, 1177314, 339275, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_339275_1177314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339275 ⟨1177314, by decide⟩ :=
  accepted_of_selected 12 339275 ⟨1177314, by decide⟩ ⟨12, 2, 0, 1177314, 339275, 1973, 65536⟩
    (by decide) selected_cut_43061

theorem unmarked_context_11_84818_1177315 : frontier 10 ⟨1177315, by decide⟩
    (prefixCache 11 84818) (prefixPartial 11 84818) = false := by
  decide +kernel

theorem node_context_11_84818_1177315 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177315, by decide⟩ =
    .split (coordinate 11) (![⟨1177247, by decide⟩,⟨126371, by decide⟩,⟨1177284, by decide⟩,⟨1177314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84818_1177315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84818 ⟨1177315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84818
    ⟨1177315, by decide⟩ (by decide) (![⟨1177247, by decide⟩,⟨126371, by decide⟩,⟨1177284, by decide⟩,⟨1177314, by decide⟩]) unmarked_context_11_84818_1177315 node_context_11_84818_1177315
  intro a
  fin_cases a
  · exact context_12_339272_1177247
  · exact context_12_339273_126371
  · exact context_12_339274_1177284
  · exact context_12_339275_1177314

theorem selected_cut_43062 : selected 9 ⟨1177333, by decide⟩
    (prefixPartial 12 339276) = some ⟨12, 2, 0, 1177333, 339276, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_339276_1177333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339276 ⟨1177333, by decide⟩ :=
  accepted_of_selected 12 339276 ⟨1177333, by decide⟩ ⟨12, 2, 0, 1177333, 339276, 1357, 65536⟩
    (by decide) selected_cut_43062

theorem selected_cut_43063 : selected 9 ⟨320864, by decide⟩
    (prefixPartial 12 339277) = some ⟨12, 1, 0, 320864, 339277, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339277_320864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339277 ⟨320864, by decide⟩ :=
  accepted_of_selected 12 339277 ⟨320864, by decide⟩ ⟨12, 1, 0, 320864, 339277, 1, 65536⟩
    (by decide) selected_cut_43063

theorem selected_cut_43064 : selected 9 ⟨1177352, by decide⟩
    (prefixPartial 12 339278) = some ⟨12, 2, 0, 1177352, 339278, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_339278_1177352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339278 ⟨1177352, by decide⟩ :=
  accepted_of_selected 12 339278 ⟨1177352, by decide⟩ ⟨12, 2, 0, 1177352, 339278, 1561, 65536⟩
    (by decide) selected_cut_43064

theorem selected_cut_43065 : selected 9 ⟨1177375, by decide⟩
    (prefixPartial 12 339279) = some ⟨12, 2, 0, 1177375, 339279, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_339279_1177375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339279 ⟨1177375, by decide⟩ :=
  accepted_of_selected 12 339279 ⟨1177375, by decide⟩ ⟨12, 2, 0, 1177375, 339279, 1701, 65536⟩
    (by decide) selected_cut_43065

theorem unmarked_context_11_84819_1177376 : frontier 10 ⟨1177376, by decide⟩
    (prefixCache 11 84819) (prefixPartial 11 84819) = false := by
  decide +kernel

theorem node_context_11_84819_1177376 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177376, by decide⟩ =
    .split (coordinate 11) (![⟨1177333, by decide⟩,⟨320864, by decide⟩,⟨1177352, by decide⟩,⟨1177375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84819_1177376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84819 ⟨1177376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84819
    ⟨1177376, by decide⟩ (by decide) (![⟨1177333, by decide⟩,⟨320864, by decide⟩,⟨1177352, by decide⟩,⟨1177375, by decide⟩]) unmarked_context_11_84819_1177376 node_context_11_84819_1177376
  intro a
  fin_cases a
  · exact context_12_339276_1177333
  · exact context_12_339277_320864
  · exact context_12_339278_1177352
  · exact context_12_339279_1177375

theorem unmarked_context_10_21204_1177377 : frontier 11 ⟨1177377, by decide⟩
    (prefixCache 10 21204) (prefixPartial 10 21204) = false := by
  decide +kernel

theorem node_context_10_21204_1177377 : EJMOriginalGlobalDAGData.nodes 11 ⟨1177377, by decide⟩ =
    .split (coordinate 10) (![⟨1177134, by decide⟩,⟨1177225, by decide⟩,⟨1177315, by decide⟩,⟨1177376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21204_1177377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21204 ⟨1177377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21204
    ⟨1177377, by decide⟩ (by decide) (![⟨1177134, by decide⟩,⟨1177225, by decide⟩,⟨1177315, by decide⟩,⟨1177376, by decide⟩]) unmarked_context_10_21204_1177377 node_context_10_21204_1177377
  intro a
  fin_cases a
  · exact context_11_84816_1177134
  · exact context_11_84817_1177225
  · exact context_11_84818_1177315
  · exact context_11_84819_1177376

theorem selected_cut_43066 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 21205) = some ⟨10, 1, 0, 893098, 21205, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_21205_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21205 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 21205 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 21205, 1, 1048576⟩
    (by decide) selected_cut_43066

theorem selected_cut_43067 : selected 9 ⟨1177405, by decide⟩
    (prefixPartial 12 339296) = some ⟨12, 2, 0, 1177405, 339296, 853, 65536⟩ := by
  decide +kernel

theorem context_12_339296_1177405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339296 ⟨1177405, by decide⟩ :=
  accepted_of_selected 12 339296 ⟨1177405, by decide⟩ ⟨12, 2, 0, 1177405, 339296, 853, 65536⟩
    (by decide) selected_cut_43067

theorem selected_cut_43068 : selected 9 ⟨219808, by decide⟩
    (prefixPartial 12 339297) = some ⟨12, 1, 0, 219808, 339297, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339297_219808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339297 ⟨219808, by decide⟩ :=
  accepted_of_selected 12 339297 ⟨219808, by decide⟩ ⟨12, 1, 0, 219808, 339297, 1, 65536⟩
    (by decide) selected_cut_43068

theorem selected_cut_43069 : selected 9 ⟨1177434, by decide⟩
    (prefixPartial 12 339298) = some ⟨12, 2, 0, 1177434, 339298, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_339298_1177434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339298 ⟨1177434, by decide⟩ :=
  accepted_of_selected 12 339298 ⟨1177434, by decide⟩ ⟨12, 2, 0, 1177434, 339298, 1649, 65536⟩
    (by decide) selected_cut_43069

theorem selected_cut_43070 : selected 9 ⟨1177459, by decide⟩
    (prefixPartial 12 339299) = some ⟨12, 2, 0, 1177459, 339299, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_339299_1177459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339299 ⟨1177459, by decide⟩ :=
  accepted_of_selected 12 339299 ⟨1177459, by decide⟩ ⟨12, 2, 0, 1177459, 339299, 1793, 65536⟩
    (by decide) selected_cut_43070

theorem unmarked_context_11_84824_1177460 : frontier 10 ⟨1177460, by decide⟩
    (prefixCache 11 84824) (prefixPartial 11 84824) = false := by
  decide +kernel

theorem node_context_11_84824_1177460 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177460, by decide⟩ =
    .split (coordinate 11) (![⟨1177405, by decide⟩,⟨219808, by decide⟩,⟨1177434, by decide⟩,⟨1177459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84824_1177460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84824 ⟨1177460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84824
    ⟨1177460, by decide⟩ (by decide) (![⟨1177405, by decide⟩,⟨219808, by decide⟩,⟨1177434, by decide⟩,⟨1177459, by decide⟩]) unmarked_context_11_84824_1177460 node_context_11_84824_1177460
  intro a
  fin_cases a
  · exact context_12_339296_1177405
  · exact context_12_339297_219808
  · exact context_12_339298_1177434
  · exact context_12_339299_1177459

theorem selected_cut_43071 : selected 9 ⟨1177482, by decide⟩
    (prefixPartial 12 339300) = some ⟨12, 2, 0, 1177482, 339300, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_339300_1177482 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339300 ⟨1177482, by decide⟩ :=
  accepted_of_selected 12 339300 ⟨1177482, by decide⟩ ⟨12, 2, 0, 1177482, 339300, 1493, 65536⟩
    (by decide) selected_cut_43071

theorem selected_cut_43072 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 339301) = some ⟨12, 1, 0, 891951, 339301, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339301_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339301 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 339301 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 339301, 1, 65536⟩
    (by decide) selected_cut_43072

theorem selected_cut_43073 : selected 9 ⟨1177508, by decide⟩
    (prefixPartial 12 339302) = some ⟨12, 2, 0, 1177508, 339302, 1613, 65536⟩ := by
  decide +kernel

theorem context_12_339302_1177508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339302 ⟨1177508, by decide⟩ :=
  accepted_of_selected 12 339302 ⟨1177508, by decide⟩ ⟨12, 2, 0, 1177508, 339302, 1613, 65536⟩
    (by decide) selected_cut_43073

theorem selected_cut_43074 : selected 9 ⟨1177531, by decide⟩
    (prefixPartial 12 339303) = some ⟨12, 2, 0, 1177531, 339303, 1665, 65536⟩ := by
  decide +kernel

theorem context_12_339303_1177531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339303 ⟨1177531, by decide⟩ :=
  accepted_of_selected 12 339303 ⟨1177531, by decide⟩ ⟨12, 2, 0, 1177531, 339303, 1665, 65536⟩
    (by decide) selected_cut_43074

theorem unmarked_context_11_84825_1177532 : frontier 10 ⟨1177532, by decide⟩
    (prefixCache 11 84825) (prefixPartial 11 84825) = false := by
  decide +kernel

theorem node_context_11_84825_1177532 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177532, by decide⟩ =
    .split (coordinate 11) (![⟨1177482, by decide⟩,⟨891951, by decide⟩,⟨1177508, by decide⟩,⟨1177531, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84825_1177532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84825 ⟨1177532, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84825
    ⟨1177532, by decide⟩ (by decide) (![⟨1177482, by decide⟩,⟨891951, by decide⟩,⟨1177508, by decide⟩,⟨1177531, by decide⟩]) unmarked_context_11_84825_1177532 node_context_11_84825_1177532
  intro a
  fin_cases a
  · exact context_12_339300_1177482
  · exact context_12_339301_891951
  · exact context_12_339302_1177508
  · exact context_12_339303_1177531

theorem selected_cut_43075 : selected 9 ⟨1177548, by decide⟩
    (prefixPartial 12 339304) = some ⟨12, 2, 0, 1177548, 339304, 1321, 65536⟩ := by
  decide +kernel

theorem context_12_339304_1177548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339304 ⟨1177548, by decide⟩ :=
  accepted_of_selected 12 339304 ⟨1177548, by decide⟩ ⟨12, 2, 0, 1177548, 339304, 1321, 65536⟩
    (by decide) selected_cut_43075

theorem selected_cut_43076 : selected 9 ⟨1177571, by decide⟩
    (prefixPartial 12 339305) = some ⟨12, 2, 0, 1177571, 339305, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_339305_1177571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339305 ⟨1177571, by decide⟩ :=
  accepted_of_selected 12 339305 ⟨1177571, by decide⟩ ⟨12, 2, 0, 1177571, 339305, 1501, 65536⟩
    (by decide) selected_cut_43076

theorem selected_cut_43077 : selected 9 ⟨1172910, by decide⟩
    (prefixPartial 12 339306) = some ⟨12, 1, 0, 1172910, 339306, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339306_1172910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339306 ⟨1172910, by decide⟩ :=
  accepted_of_selected 12 339306 ⟨1172910, by decide⟩ ⟨12, 1, 0, 1172910, 339306, 1, 65536⟩
    (by decide) selected_cut_43077

theorem selected_cut_43078 : selected 9 ⟨1177597, by decide⟩
    (prefixPartial 12 339307) = some ⟨12, 2, 0, 1177597, 339307, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_339307_1177597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339307 ⟨1177597, by decide⟩ :=
  accepted_of_selected 12 339307 ⟨1177597, by decide⟩ ⟨12, 2, 0, 1177597, 339307, 1629, 65536⟩
    (by decide) selected_cut_43078

theorem unmarked_context_11_84826_1177598 : frontier 10 ⟨1177598, by decide⟩
    (prefixCache 11 84826) (prefixPartial 11 84826) = false := by
  decide +kernel

theorem node_context_11_84826_1177598 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177598, by decide⟩ =
    .split (coordinate 11) (![⟨1177548, by decide⟩,⟨1177571, by decide⟩,⟨1172910, by decide⟩,⟨1177597, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84826_1177598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84826 ⟨1177598, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84826
    ⟨1177598, by decide⟩ (by decide) (![⟨1177548, by decide⟩,⟨1177571, by decide⟩,⟨1172910, by decide⟩,⟨1177597, by decide⟩]) unmarked_context_11_84826_1177598 node_context_11_84826_1177598
  intro a
  fin_cases a
  · exact context_12_339304_1177548
  · exact context_12_339305_1177571
  · exact context_12_339306_1172910
  · exact context_12_339307_1177597

theorem selected_cut_43079 : selected 9 ⟨1177611, by decide⟩
    (prefixPartial 12 339308) = some ⟨12, 2, 0, 1177611, 339308, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_339308_1177611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339308 ⟨1177611, by decide⟩ :=
  accepted_of_selected 12 339308 ⟨1177611, by decide⟩ ⟨12, 2, 0, 1177611, 339308, 1221, 65536⟩
    (by decide) selected_cut_43079

theorem selected_cut_43080 : selected 9 ⟨1177631, by decide⟩
    (prefixPartial 12 339309) = some ⟨12, 2, 0, 1177631, 339309, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_339309_1177631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339309 ⟨1177631, by decide⟩ :=
  accepted_of_selected 12 339309 ⟨1177631, by decide⟩ ⟨12, 2, 0, 1177631, 339309, 1333, 65536⟩
    (by decide) selected_cut_43080

theorem selected_cut_43081 : selected 9 ⟨1177642, by decide⟩
    (prefixPartial 12 339310) = some ⟨12, 2, 0, 1177642, 339310, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_339310_1177642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339310 ⟨1177642, by decide⟩ :=
  accepted_of_selected 12 339310 ⟨1177642, by decide⟩ ⟨12, 2, 0, 1177642, 339310, 1253, 65536⟩
    (by decide) selected_cut_43081

theorem selected_cut_43082 : selected 9 ⟨1177661, by decide⟩
    (prefixPartial 12 339311) = some ⟨12, 2, 0, 1177661, 339311, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_339311_1177661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339311 ⟨1177661, by decide⟩ :=
  accepted_of_selected 12 339311 ⟨1177661, by decide⟩ ⟨12, 2, 0, 1177661, 339311, 1405, 65536⟩
    (by decide) selected_cut_43082

theorem unmarked_context_11_84827_1177662 : frontier 10 ⟨1177662, by decide⟩
    (prefixCache 11 84827) (prefixPartial 11 84827) = false := by
  decide +kernel

theorem node_context_11_84827_1177662 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177662, by decide⟩ =
    .split (coordinate 11) (![⟨1177611, by decide⟩,⟨1177631, by decide⟩,⟨1177642, by decide⟩,⟨1177661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84827_1177662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84827 ⟨1177662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84827
    ⟨1177662, by decide⟩ (by decide) (![⟨1177611, by decide⟩,⟨1177631, by decide⟩,⟨1177642, by decide⟩,⟨1177661, by decide⟩]) unmarked_context_11_84827_1177662 node_context_11_84827_1177662
  intro a
  fin_cases a
  · exact context_12_339308_1177611
  · exact context_12_339309_1177631
  · exact context_12_339310_1177642
  · exact context_12_339311_1177661

theorem unmarked_context_10_21206_1177663 : frontier 11 ⟨1177663, by decide⟩
    (prefixCache 10 21206) (prefixPartial 10 21206) = false := by
  decide +kernel

theorem node_context_10_21206_1177663 : EJMOriginalGlobalDAGData.nodes 11 ⟨1177663, by decide⟩ =
    .split (coordinate 10) (![⟨1177460, by decide⟩,⟨1177532, by decide⟩,⟨1177598, by decide⟩,⟨1177662, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21206_1177663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21206 ⟨1177663, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21206
    ⟨1177663, by decide⟩ (by decide) (![⟨1177460, by decide⟩,⟨1177532, by decide⟩,⟨1177598, by decide⟩,⟨1177662, by decide⟩]) unmarked_context_10_21206_1177663 node_context_10_21206_1177663
  intro a
  fin_cases a
  · exact context_11_84824_1177460
  · exact context_11_84825_1177532
  · exact context_11_84826_1177598
  · exact context_11_84827_1177662

theorem selected_cut_43083 : selected 10 ⟨1177716, by decide⟩
    (prefixPartial 11 84828) = some ⟨11, 2, 0, 1177716, 84828, 2993, 262144⟩ := by
  decide +kernel

theorem context_11_84828_1177716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84828 ⟨1177716, by decide⟩ :=
  accepted_of_selected 11 84828 ⟨1177716, by decide⟩ ⟨11, 2, 0, 1177716, 84828, 2993, 262144⟩
    (by decide) selected_cut_43083

theorem selected_cut_43084 : selected 10 ⟨1177789, by decide⟩
    (prefixPartial 11 84829) = some ⟨11, 2, 0, 1177789, 84829, 3869, 262144⟩ := by
  decide +kernel

theorem context_11_84829_1177789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84829 ⟨1177789, by decide⟩ :=
  accepted_of_selected 11 84829 ⟨1177789, by decide⟩ ⟨11, 2, 0, 1177789, 84829, 3869, 262144⟩
    (by decide) selected_cut_43084

theorem selected_cut_43085 : selected 9 ⟨1177807, by decide⟩
    (prefixPartial 12 339320) = some ⟨12, 2, 0, 1177807, 339320, 1117, 65536⟩ := by
  decide +kernel

theorem context_12_339320_1177807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339320 ⟨1177807, by decide⟩ :=
  accepted_of_selected 12 339320 ⟨1177807, by decide⟩ ⟨12, 2, 0, 1177807, 339320, 1117, 65536⟩
    (by decide) selected_cut_43085

theorem selected_cut_43086 : selected 9 ⟨1177829, by decide⟩
    (prefixPartial 12 339321) = some ⟨12, 2, 0, 1177829, 339321, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_339321_1177829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339321 ⟨1177829, by decide⟩ :=
  accepted_of_selected 12 339321 ⟨1177829, by decide⟩ ⟨12, 2, 0, 1177829, 339321, 1213, 65536⟩
    (by decide) selected_cut_43086

theorem selected_cut_43087 : selected 9 ⟨1177841, by decide⟩
    (prefixPartial 12 339322) = some ⟨12, 2, 0, 1177841, 339322, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_339322_1177841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339322 ⟨1177841, by decide⟩ :=
  accepted_of_selected 12 339322 ⟨1177841, by decide⟩ ⟨12, 2, 0, 1177841, 339322, 1157, 65536⟩
    (by decide) selected_cut_43087

theorem selected_cut_43088 : selected 9 ⟨1177859, by decide⟩
    (prefixPartial 12 339323) = some ⟨12, 2, 0, 1177859, 339323, 1225, 65536⟩ := by
  decide +kernel

theorem context_12_339323_1177859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339323 ⟨1177859, by decide⟩ :=
  accepted_of_selected 12 339323 ⟨1177859, by decide⟩ ⟨12, 2, 0, 1177859, 339323, 1225, 65536⟩
    (by decide) selected_cut_43088

theorem unmarked_context_11_84830_1177860 : frontier 10 ⟨1177860, by decide⟩
    (prefixCache 11 84830) (prefixPartial 11 84830) = false := by
  decide +kernel

theorem node_context_11_84830_1177860 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177860, by decide⟩ =
    .split (coordinate 11) (![⟨1177807, by decide⟩,⟨1177829, by decide⟩,⟨1177841, by decide⟩,⟨1177859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84830_1177860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84830 ⟨1177860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84830
    ⟨1177860, by decide⟩ (by decide) (![⟨1177807, by decide⟩,⟨1177829, by decide⟩,⟨1177841, by decide⟩,⟨1177859, by decide⟩]) unmarked_context_11_84830_1177860 node_context_11_84830_1177860
  intro a
  fin_cases a
  · exact context_12_339320_1177807
  · exact context_12_339321_1177829
  · exact context_12_339322_1177841
  · exact context_12_339323_1177859

theorem selected_cut_43089 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 84831) = some ⟨11, 1, 0, 977886, 84831, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84831_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84831 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 84831 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 84831, 1, 262144⟩
    (by decide) selected_cut_43089

theorem unmarked_context_10_21207_1177861 : frontier 11 ⟨1177861, by decide⟩
    (prefixCache 10 21207) (prefixPartial 10 21207) = false := by
  decide +kernel

theorem node_context_10_21207_1177861 : EJMOriginalGlobalDAGData.nodes 11 ⟨1177861, by decide⟩ =
    .split (coordinate 10) (![⟨1177716, by decide⟩,⟨1177789, by decide⟩,⟨1177860, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21207_1177861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21207 ⟨1177861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21207
    ⟨1177861, by decide⟩ (by decide) (![⟨1177716, by decide⟩,⟨1177789, by decide⟩,⟨1177860, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_21207_1177861 node_context_10_21207_1177861
  intro a
  fin_cases a
  · exact context_11_84828_1177716
  · exact context_11_84829_1177789
  · exact context_11_84830_1177860
  · exact context_11_84831_977886

theorem unmarked_context_9_5301_1177862 : frontier 12 ⟨1177862, by decide⟩
    (prefixCache 9 5301) (prefixPartial 9 5301) = false := by
  decide +kernel

theorem node_context_9_5301_1177862 : EJMOriginalGlobalDAGData.nodes 12 ⟨1177862, by decide⟩ =
    .split (coordinate 9) (![⟨1177377, by decide⟩,⟨893098, by decide⟩,⟨1177663, by decide⟩,⟨1177861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5301_1177862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5301 ⟨1177862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5301
    ⟨1177862, by decide⟩ (by decide) (![⟨1177377, by decide⟩,⟨893098, by decide⟩,⟨1177663, by decide⟩,⟨1177861, by decide⟩]) unmarked_context_9_5301_1177862 node_context_9_5301_1177862
  intro a
  fin_cases a
  · exact context_10_21204_1177377
  · exact context_10_21205_893098
  · exact context_10_21206_1177663
  · exact context_10_21207_1177861

theorem selected_cut_43090 : selected 9 ⟨1173556, by decide⟩
    (prefixPartial 12 339328) = some ⟨12, 1, 0, 1173556, 339328, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339328_1173556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339328 ⟨1173556, by decide⟩ :=
  accepted_of_selected 12 339328 ⟨1173556, by decide⟩ ⟨12, 1, 0, 1173556, 339328, 1, 65536⟩
    (by decide) selected_cut_43090

theorem selected_cut_43091 : selected 9 ⟨1177900, by decide⟩
    (prefixPartial 12 339329) = some ⟨12, 2, 0, 1177900, 339329, 1509, 65536⟩ := by
  decide +kernel

theorem context_12_339329_1177900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339329 ⟨1177900, by decide⟩ :=
  accepted_of_selected 12 339329 ⟨1177900, by decide⟩ ⟨12, 2, 0, 1177900, 339329, 1509, 65536⟩
    (by decide) selected_cut_43091

theorem selected_cut_43092 : selected 9 ⟨1177923, by decide⟩
    (prefixPartial 12 339330) = some ⟨12, 2, 0, 1177923, 339330, 1353, 65536⟩ := by
  decide +kernel

theorem context_12_339330_1177923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339330 ⟨1177923, by decide⟩ :=
  accepted_of_selected 12 339330 ⟨1177923, by decide⟩ ⟨12, 2, 0, 1177923, 339330, 1353, 65536⟩
    (by decide) selected_cut_43092

theorem selected_cut_43093 : selected 9 ⟨1177949, by decide⟩
    (prefixPartial 12 339331) = some ⟨12, 2, 0, 1177949, 339331, 1521, 65536⟩ := by
  decide +kernel

theorem context_12_339331_1177949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339331 ⟨1177949, by decide⟩ :=
  accepted_of_selected 12 339331 ⟨1177949, by decide⟩ ⟨12, 2, 0, 1177949, 339331, 1521, 65536⟩
    (by decide) selected_cut_43093

theorem unmarked_context_11_84832_1177950 : frontier 10 ⟨1177950, by decide⟩
    (prefixCache 11 84832) (prefixPartial 11 84832) = false := by
  decide +kernel

theorem node_context_11_84832_1177950 : EJMOriginalGlobalDAGData.nodes 10 ⟨1177950, by decide⟩ =
    .split (coordinate 11) (![⟨1173556, by decide⟩,⟨1177900, by decide⟩,⟨1177923, by decide⟩,⟨1177949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84832_1177950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84832 ⟨1177950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84832
    ⟨1177950, by decide⟩ (by decide) (![⟨1173556, by decide⟩,⟨1177900, by decide⟩,⟨1177923, by decide⟩,⟨1177949, by decide⟩]) unmarked_context_11_84832_1177950 node_context_11_84832_1177950
  intro a
  fin_cases a
  · exact context_12_339328_1173556
  · exact context_12_339329_1177900
  · exact context_12_339330_1177923
  · exact context_12_339331_1177949

theorem selected_cut_43094 : selected 10 ⟨1178015, by decide⟩
    (prefixPartial 11 84833) = some ⟨11, 2, 0, 1178015, 84833, 3985, 262144⟩ := by
  decide +kernel

theorem context_11_84833_1178015 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84833 ⟨1178015, by decide⟩ :=
  accepted_of_selected 11 84833 ⟨1178015, by decide⟩ ⟨11, 2, 0, 1178015, 84833, 3985, 262144⟩
    (by decide) selected_cut_43094

theorem selected_cut_43095 : selected 9 ⟨1178033, by decide⟩
    (prefixPartial 12 339336) = some ⟨12, 2, 0, 1178033, 339336, 1249, 65536⟩ := by
  decide +kernel

theorem context_12_339336_1178033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339336 ⟨1178033, by decide⟩ :=
  accepted_of_selected 12 339336 ⟨1178033, by decide⟩ ⟨12, 2, 0, 1178033, 339336, 1249, 65536⟩
    (by decide) selected_cut_43095

theorem selected_cut_43096 : selected 9 ⟨1178060, by decide⟩
    (prefixPartial 12 339337) = some ⟨12, 2, 0, 1178060, 339337, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_339337_1178060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339337 ⟨1178060, by decide⟩ :=
  accepted_of_selected 12 339337 ⟨1178060, by decide⟩ ⟨12, 2, 0, 1178060, 339337, 1421, 65536⟩
    (by decide) selected_cut_43096

theorem selected_cut_43097 : selected 9 ⟨1109520, by decide⟩
    (prefixPartial 12 339338) = some ⟨12, 1, 0, 1109520, 339338, 1, 65536⟩ := by
  decide +kernel

theorem context_12_339338_1109520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339338 ⟨1109520, by decide⟩ :=
  accepted_of_selected 12 339338 ⟨1109520, by decide⟩ ⟨12, 1, 0, 1109520, 339338, 1, 65536⟩
    (by decide) selected_cut_43097

theorem selected_cut_43098 : selected 9 ⟨1178083, by decide⟩
    (prefixPartial 12 339339) = some ⟨12, 2, 0, 1178083, 339339, 1501, 65536⟩ := by
  decide +kernel

theorem context_12_339339_1178083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339339 ⟨1178083, by decide⟩ :=
  accepted_of_selected 12 339339 ⟨1178083, by decide⟩ ⟨12, 2, 0, 1178083, 339339, 1501, 65536⟩
    (by decide) selected_cut_43098

theorem unmarked_context_11_84834_1178084 : frontier 10 ⟨1178084, by decide⟩
    (prefixCache 11 84834) (prefixPartial 11 84834) = false := by
  decide +kernel

theorem node_context_11_84834_1178084 : EJMOriginalGlobalDAGData.nodes 10 ⟨1178084, by decide⟩ =
    .split (coordinate 11) (![⟨1178033, by decide⟩,⟨1178060, by decide⟩,⟨1109520, by decide⟩,⟨1178083, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84834_1178084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84834 ⟨1178084, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84834
    ⟨1178084, by decide⟩ (by decide) (![⟨1178033, by decide⟩,⟨1178060, by decide⟩,⟨1109520, by decide⟩,⟨1178083, by decide⟩]) unmarked_context_11_84834_1178084 node_context_11_84834_1178084
  intro a
  fin_cases a
  · exact context_12_339336_1178033
  · exact context_12_339337_1178060
  · exact context_12_339338_1109520
  · exact context_12_339339_1178083

theorem selected_cut_43099 : selected 9 ⟨1178096, by decide⟩
    (prefixPartial 12 339340) = some ⟨12, 2, 0, 1178096, 339340, 1001, 65536⟩ := by
  decide +kernel

theorem context_12_339340_1178096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339340 ⟨1178096, by decide⟩ :=
  accepted_of_selected 12 339340 ⟨1178096, by decide⟩ ⟨12, 2, 0, 1178096, 339340, 1001, 65536⟩
    (by decide) selected_cut_43099

theorem selected_cut_43100 : selected 9 ⟨1178112, by decide⟩
    (prefixPartial 12 339341) = some ⟨12, 2, 0, 1178112, 339341, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_339341_1178112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339341 ⟨1178112, by decide⟩ :=
  accepted_of_selected 12 339341 ⟨1178112, by decide⟩ ⟨12, 2, 0, 1178112, 339341, 1189, 65536⟩
    (by decide) selected_cut_43100

theorem selected_cut_43101 : selected 9 ⟨1178130, by decide⟩
    (prefixPartial 12 339342) = some ⟨12, 2, 0, 1178130, 339342, 1057, 65536⟩ := by
  decide +kernel

theorem context_12_339342_1178130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339342 ⟨1178130, by decide⟩ :=
  accepted_of_selected 12 339342 ⟨1178130, by decide⟩ ⟨12, 2, 0, 1178130, 339342, 1057, 65536⟩
    (by decide) selected_cut_43101

theorem selected_cut_43102 : selected 9 ⟨1178155, by decide⟩
    (prefixPartial 12 339343) = some ⟨12, 2, 0, 1178155, 339343, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_339343_1178155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339343 ⟨1178155, by decide⟩ :=
  accepted_of_selected 12 339343 ⟨1178155, by decide⟩ ⟨12, 2, 0, 1178155, 339343, 1425, 65536⟩
    (by decide) selected_cut_43102

theorem unmarked_context_11_84835_1178156 : frontier 10 ⟨1178156, by decide⟩
    (prefixCache 11 84835) (prefixPartial 11 84835) = false := by
  decide +kernel

theorem node_context_11_84835_1178156 : EJMOriginalGlobalDAGData.nodes 10 ⟨1178156, by decide⟩ =
    .split (coordinate 11) (![⟨1178096, by decide⟩,⟨1178112, by decide⟩,⟨1178130, by decide⟩,⟨1178155, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84835_1178156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84835 ⟨1178156, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84835
    ⟨1178156, by decide⟩ (by decide) (![⟨1178096, by decide⟩,⟨1178112, by decide⟩,⟨1178130, by decide⟩,⟨1178155, by decide⟩]) unmarked_context_11_84835_1178156 node_context_11_84835_1178156
  intro a
  fin_cases a
  · exact context_12_339340_1178096
  · exact context_12_339341_1178112
  · exact context_12_339342_1178130
  · exact context_12_339343_1178155

theorem unmarked_context_10_21208_1178157 : frontier 11 ⟨1178157, by decide⟩
    (prefixCache 10 21208) (prefixPartial 10 21208) = false := by
  decide +kernel

theorem node_context_10_21208_1178157 : EJMOriginalGlobalDAGData.nodes 11 ⟨1178157, by decide⟩ =
    .split (coordinate 10) (![⟨1177950, by decide⟩,⟨1178015, by decide⟩,⟨1178084, by decide⟩,⟨1178156, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21208_1178157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21208 ⟨1178157, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21208
    ⟨1178157, by decide⟩ (by decide) (![⟨1177950, by decide⟩,⟨1178015, by decide⟩,⟨1178084, by decide⟩,⟨1178156, by decide⟩]) unmarked_context_10_21208_1178157 node_context_10_21208_1178157
  intro a
  fin_cases a
  · exact context_11_84832_1177950
  · exact context_11_84833_1178015
  · exact context_11_84834_1178084
  · exact context_11_84835_1178156

theorem selected_cut_43103 : selected 9 ⟨1178177, by decide⟩
    (prefixPartial 12 339344) = some ⟨12, 2, 0, 1178177, 339344, 977, 65536⟩ := by
  decide +kernel

theorem context_12_339344_1178177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339344 ⟨1178177, by decide⟩ :=
  accepted_of_selected 12 339344 ⟨1178177, by decide⟩ ⟨12, 2, 0, 1178177, 339344, 977, 65536⟩
    (by decide) selected_cut_43103

theorem selected_cut_43104 : selected 9 ⟨1178200, by decide⟩
    (prefixPartial 12 339345) = some ⟨12, 2, 0, 1178200, 339345, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_339345_1178200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339345 ⟨1178200, by decide⟩ :=
  accepted_of_selected 12 339345 ⟨1178200, by decide⟩ ⟨12, 2, 0, 1178200, 339345, 1089, 65536⟩
    (by decide) selected_cut_43104

theorem selected_cut_43105 : selected 9 ⟨1178219, by decide⟩
    (prefixPartial 12 339346) = some ⟨12, 2, 0, 1178219, 339346, 1017, 65536⟩ := by
  decide +kernel

theorem context_12_339346_1178219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339346 ⟨1178219, by decide⟩ :=
  accepted_of_selected 12 339346 ⟨1178219, by decide⟩ ⟨12, 2, 0, 1178219, 339346, 1017, 65536⟩
    (by decide) selected_cut_43105

theorem selected_cut_43106 : selected 9 ⟨1178237, by decide⟩
    (prefixPartial 12 339347) = some ⟨12, 2, 0, 1178237, 339347, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_339347_1178237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 339347 ⟨1178237, by decide⟩ :=
  accepted_of_selected 12 339347 ⟨1178237, by decide⟩ ⟨12, 2, 0, 1178237, 339347, 1193, 65536⟩
    (by decide) selected_cut_43106

theorem unmarked_context_11_84836_1178238 : frontier 10 ⟨1178238, by decide⟩
    (prefixCache 11 84836) (prefixPartial 11 84836) = false := by
  decide +kernel

theorem node_context_11_84836_1178238 : EJMOriginalGlobalDAGData.nodes 10 ⟨1178238, by decide⟩ =
    .split (coordinate 11) (![⟨1178177, by decide⟩,⟨1178200, by decide⟩,⟨1178219, by decide⟩,⟨1178237, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84836_1178238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84836 ⟨1178238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84836
    ⟨1178238, by decide⟩ (by decide) (![⟨1178177, by decide⟩,⟨1178200, by decide⟩,⟨1178219, by decide⟩,⟨1178237, by decide⟩]) unmarked_context_11_84836_1178238 node_context_11_84836_1178238
  intro a
  fin_cases a
  · exact context_12_339344_1178177
  · exact context_12_339345_1178200
  · exact context_12_339346_1178219
  · exact context_12_339347_1178237

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
