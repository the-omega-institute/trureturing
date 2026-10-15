/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover274
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_88845_667936 : frontier 9 ⟨667936, by decide⟩
    (prefixCache 12 88845) (prefixPartial 12 88845) = false := by
  decide +kernel

theorem node_context_12_88845_667936 : EJMOriginalGlobalDAGData.nodes 9 ⟨667936, by decide⟩ =
    .split (coordinate 12) (![⟨667855, by decide⟩,⟨667901, by decide⟩,⟨667926, by decide⟩,⟨667935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88845_667936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88845 ⟨667936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88845
    ⟨667936, by decide⟩ (by decide) (![⟨667855, by decide⟩,⟨667901, by decide⟩,⟨667926, by decide⟩,⟨667935, by decide⟩]) unmarked_context_12_88845_667936 node_context_12_88845_667936
  intro a
  fin_cases a
  · exact context_13_355380_667855
  · exact context_13_355381_667901
  · exact context_13_355382_667926
  · exact context_13_355383_667935

theorem selected_cut_26404 : selected 8 ⟨668011, by decide⟩
    (prefixPartial 13 355384) = some ⟨13, 2, 0, 668011, 355384, 4093, 16384⟩ := by
  decide +kernel

theorem context_13_355384_668011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355384 ⟨668011, by decide⟩ :=
  accepted_of_selected 13 355384 ⟨668011, by decide⟩ ⟨13, 2, 0, 668011, 355384, 4093, 16384⟩
    (by decide) selected_cut_26404

theorem selected_cut_26405 : selected 8 ⟨668096, by decide⟩
    (prefixPartial 13 355385) = some ⟨13, 2, 0, 668096, 355385, 3581, 16384⟩ := by
  decide +kernel

theorem context_13_355385_668096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355385 ⟨668096, by decide⟩ :=
  accepted_of_selected 13 355385 ⟨668096, by decide⟩ ⟨13, 2, 0, 668096, 355385, 3581, 16384⟩
    (by decide) selected_cut_26405

theorem selected_cut_26406 : selected 8 ⟨668124, by decide⟩
    (prefixPartial 13 355386) = some ⟨13, 2, 0, 668124, 355386, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_355386_668124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355386 ⟨668124, by decide⟩ :=
  accepted_of_selected 13 355386 ⟨668124, by decide⟩ ⟨13, 2, 0, 668124, 355386, 2301, 16384⟩
    (by decide) selected_cut_26406

theorem selected_cut_26407 : selected 8 ⟨668132, by decide⟩
    (prefixPartial 13 355387) = some ⟨13, 2, 0, 668132, 355387, 905, 16384⟩ := by
  decide +kernel

theorem context_13_355387_668132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355387 ⟨668132, by decide⟩ :=
  accepted_of_selected 13 355387 ⟨668132, by decide⟩ ⟨13, 2, 0, 668132, 355387, 905, 16384⟩
    (by decide) selected_cut_26407

theorem unmarked_context_12_88846_668133 : frontier 9 ⟨668133, by decide⟩
    (prefixCache 12 88846) (prefixPartial 12 88846) = false := by
  decide +kernel

theorem node_context_12_88846_668133 : EJMOriginalGlobalDAGData.nodes 9 ⟨668133, by decide⟩ =
    .split (coordinate 12) (![⟨668011, by decide⟩,⟨668096, by decide⟩,⟨668124, by decide⟩,⟨668132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88846_668133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88846 ⟨668133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88846
    ⟨668133, by decide⟩ (by decide) (![⟨668011, by decide⟩,⟨668096, by decide⟩,⟨668124, by decide⟩,⟨668132, by decide⟩]) unmarked_context_12_88846_668133 node_context_12_88846_668133
  intro a
  fin_cases a
  · exact context_13_355384_668011
  · exact context_13_355385_668096
  · exact context_13_355386_668124
  · exact context_13_355387_668132

theorem selected_cut_26408 : selected 7 ⟨668141, by decide⟩
    (prefixPartial 14 1421552) = some ⟨14, 2, 0, 668141, 1421552, 329, 4096⟩ := by
  decide +kernel

theorem context_14_1421552_668141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421552 ⟨668141, by decide⟩ :=
  accepted_of_selected 14 1421552 ⟨668141, by decide⟩ ⟨14, 2, 0, 668141, 1421552, 329, 4096⟩
    (by decide) selected_cut_26408

theorem selected_cut_26409 : selected 7 ⟨668183, by decide⟩
    (prefixPartial 14 1421553) = some ⟨14, 2, 0, 668183, 1421553, 2017, 4096⟩ := by
  decide +kernel

theorem context_14_1421553_668183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421553 ⟨668183, by decide⟩ :=
  accepted_of_selected 14 1421553 ⟨668183, by decide⟩ ⟨14, 2, 0, 668183, 1421553, 2017, 4096⟩
    (by decide) selected_cut_26409

theorem selected_cut_26410 : selected 7 ⟨668221, by decide⟩
    (prefixPartial 14 1421554) = some ⟨14, 2, 0, 668221, 1421554, 1889, 4096⟩ := by
  decide +kernel

theorem context_14_1421554_668221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421554 ⟨668221, by decide⟩ :=
  accepted_of_selected 14 1421554 ⟨668221, by decide⟩ ⟨14, 2, 0, 668221, 1421554, 1889, 4096⟩
    (by decide) selected_cut_26410

theorem selected_cut_26411 : selected 7 ⟨668241, by decide⟩
    (prefixPartial 14 1421555) = some ⟨14, 2, 0, 668241, 1421555, 1165, 4096⟩ := by
  decide +kernel

theorem context_14_1421555_668241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421555 ⟨668241, by decide⟩ :=
  accepted_of_selected 14 1421555 ⟨668241, by decide⟩ ⟨14, 2, 0, 668241, 1421555, 1165, 4096⟩
    (by decide) selected_cut_26411

theorem unmarked_context_13_355388_668242 : frontier 8 ⟨668242, by decide⟩
    (prefixCache 13 355388) (prefixPartial 13 355388) = false := by
  decide +kernel

theorem node_context_13_355388_668242 : EJMOriginalGlobalDAGData.nodes 8 ⟨668242, by decide⟩ =
    .split (coordinate 13) (![⟨668141, by decide⟩,⟨668183, by decide⟩,⟨668221, by decide⟩,⟨668241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_355388_668242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355388 ⟨668242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 355388
    ⟨668242, by decide⟩ (by decide) (![⟨668141, by decide⟩,⟨668183, by decide⟩,⟨668221, by decide⟩,⟨668241, by decide⟩]) unmarked_context_13_355388_668242 node_context_13_355388_668242
  intro a
  fin_cases a
  · exact context_14_1421552_668141
  · exact context_14_1421553_668183
  · exact context_14_1421554_668221
  · exact context_14_1421555_668241

theorem selected_cut_26412 : selected 7 ⟨668286, by decide⟩
    (prefixPartial 14 1421556) = some ⟨14, 2, 0, 668286, 1421556, 1405, 4096⟩ := by
  decide +kernel

theorem context_14_1421556_668286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421556 ⟨668286, by decide⟩ :=
  accepted_of_selected 14 1421556 ⟨668286, by decide⟩ ⟨14, 2, 0, 668286, 1421556, 1405, 4096⟩
    (by decide) selected_cut_26412

theorem selected_cut_26413 : selected 7 ⟨668335, by decide⟩
    (prefixPartial 14 1421557) = some ⟨14, 2, 0, 668335, 1421557, 1249, 4096⟩ := by
  decide +kernel

theorem context_14_1421557_668335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421557 ⟨668335, by decide⟩ :=
  accepted_of_selected 14 1421557 ⟨668335, by decide⟩ ⟨14, 2, 0, 668335, 1421557, 1249, 4096⟩
    (by decide) selected_cut_26413

theorem selected_cut_26414 : selected 7 ⟨668382, by decide⟩
    (prefixPartial 14 1421558) = some ⟨14, 2, 0, 668382, 1421558, 1413, 4096⟩ := by
  decide +kernel

theorem context_14_1421558_668382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421558 ⟨668382, by decide⟩ :=
  accepted_of_selected 14 1421558 ⟨668382, by decide⟩ ⟨14, 2, 0, 668382, 1421558, 1413, 4096⟩
    (by decide) selected_cut_26414

theorem selected_cut_26415 : selected 7 ⟨668412, by decide⟩
    (prefixPartial 14 1421559) = some ⟨14, 2, 0, 668412, 1421559, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_1421559_668412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1421559 ⟨668412, by decide⟩ :=
  accepted_of_selected 14 1421559 ⟨668412, by decide⟩ ⟨14, 2, 0, 668412, 1421559, 1217, 4096⟩
    (by decide) selected_cut_26415

theorem unmarked_context_13_355389_668413 : frontier 8 ⟨668413, by decide⟩
    (prefixCache 13 355389) (prefixPartial 13 355389) = false := by
  decide +kernel

theorem node_context_13_355389_668413 : EJMOriginalGlobalDAGData.nodes 8 ⟨668413, by decide⟩ =
    .split (coordinate 13) (![⟨668286, by decide⟩,⟨668335, by decide⟩,⟨668382, by decide⟩,⟨668412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_355389_668413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355389 ⟨668413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 355389
    ⟨668413, by decide⟩ (by decide) (![⟨668286, by decide⟩,⟨668335, by decide⟩,⟨668382, by decide⟩,⟨668412, by decide⟩]) unmarked_context_13_355389_668413 node_context_13_355389_668413
  intro a
  fin_cases a
  · exact context_14_1421556_668286
  · exact context_14_1421557_668335
  · exact context_14_1421558_668382
  · exact context_14_1421559_668412

theorem selected_cut_26416 : selected 8 ⟨668507, by decide⟩
    (prefixPartial 13 355390) = some ⟨13, 2, 0, 668507, 355390, 3385, 16384⟩ := by
  decide +kernel

theorem context_13_355390_668507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355390 ⟨668507, by decide⟩ :=
  accepted_of_selected 13 355390 ⟨668507, by decide⟩ ⟨13, 2, 0, 668507, 355390, 3385, 16384⟩
    (by decide) selected_cut_26416

theorem selected_cut_26417 : selected 8 ⟨668550, by decide⟩
    (prefixPartial 13 355391) = some ⟨13, 2, 0, 668550, 355391, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_355391_668550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355391 ⟨668550, by decide⟩ :=
  accepted_of_selected 13 355391 ⟨668550, by decide⟩ ⟨13, 2, 0, 668550, 355391, 1321, 16384⟩
    (by decide) selected_cut_26417

theorem unmarked_context_12_88847_668551 : frontier 9 ⟨668551, by decide⟩
    (prefixCache 12 88847) (prefixPartial 12 88847) = false := by
  decide +kernel

theorem node_context_12_88847_668551 : EJMOriginalGlobalDAGData.nodes 9 ⟨668551, by decide⟩ =
    .split (coordinate 12) (![⟨668242, by decide⟩,⟨668413, by decide⟩,⟨668507, by decide⟩,⟨668550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88847_668551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88847 ⟨668551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88847
    ⟨668551, by decide⟩ (by decide) (![⟨668242, by decide⟩,⟨668413, by decide⟩,⟨668507, by decide⟩,⟨668550, by decide⟩]) unmarked_context_12_88847_668551 node_context_12_88847_668551
  intro a
  fin_cases a
  · exact context_13_355388_668242
  · exact context_13_355389_668413
  · exact context_13_355390_668507
  · exact context_13_355391_668550

theorem unmarked_context_11_22211_668552 : frontier 10 ⟨668552, by decide⟩
    (prefixCache 11 22211) (prefixPartial 11 22211) = false := by
  decide +kernel

theorem node_context_11_22211_668552 : EJMOriginalGlobalDAGData.nodes 10 ⟨668552, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨667936, by decide⟩,⟨668133, by decide⟩,⟨668551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22211_668552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22211 ⟨668552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22211
    ⟨668552, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨667936, by decide⟩,⟨668133, by decide⟩,⟨668551, by decide⟩]) unmarked_context_11_22211_668552 node_context_11_22211_668552
  intro a
  fin_cases a
  · exact context_12_88844_448748
  · exact context_12_88845_667936
  · exact context_12_88846_668133
  · exact context_12_88847_668551

theorem unmarked_context_10_5552_668553 : frontier 11 ⟨668553, by decide⟩
    (prefixCache 10 5552) (prefixPartial 10 5552) = false := by
  decide +kernel

theorem node_context_10_5552_668553 : EJMOriginalGlobalDAGData.nodes 11 ⟨668553, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨667303, by decide⟩,⟨667797, by decide⟩,⟨668552, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5552_668553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5552 ⟨668553, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5552
    ⟨668553, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨667303, by decide⟩,⟨667797, by decide⟩,⟨668552, by decide⟩]) unmarked_context_10_5552_668553 node_context_10_5552_668553
  intro a
  fin_cases a
  · exact context_11_22208_434745
  · exact context_11_22209_667303
  · exact context_11_22210_667797
  · exact context_11_22211_668552

theorem selected_cut_26418 : selected 8 ⟨668588, by decide⟩
    (prefixPartial 13 355392) = some ⟨13, 2, 0, 668588, 355392, 2353, 16384⟩ := by
  decide +kernel

theorem context_13_355392_668588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355392 ⟨668588, by decide⟩ :=
  accepted_of_selected 13 355392 ⟨668588, by decide⟩ ⟨13, 2, 0, 668588, 355392, 2353, 16384⟩
    (by decide) selected_cut_26418

theorem selected_cut_26419 : selected 8 ⟨668615, by decide⟩
    (prefixPartial 13 355393) = some ⟨13, 2, 0, 668615, 355393, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_355393_668615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355393 ⟨668615, by decide⟩ :=
  accepted_of_selected 13 355393 ⟨668615, by decide⟩ ⟨13, 2, 0, 668615, 355393, 1893, 16384⟩
    (by decide) selected_cut_26419

theorem selected_cut_26420 : selected 8 ⟨668636, by decide⟩
    (prefixPartial 13 355394) = some ⟨13, 2, 0, 668636, 355394, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_355394_668636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355394 ⟨668636, by decide⟩ :=
  accepted_of_selected 13 355394 ⟨668636, by decide⟩ ⟨13, 2, 0, 668636, 355394, 1609, 16384⟩
    (by decide) selected_cut_26420

theorem selected_cut_26421 : selected 8 ⟨668640, by decide⟩
    (prefixPartial 13 355395) = some ⟨13, 2, 0, 668640, 355395, 621, 16384⟩ := by
  decide +kernel

theorem context_13_355395_668640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355395 ⟨668640, by decide⟩ :=
  accepted_of_selected 13 355395 ⟨668640, by decide⟩ ⟨13, 2, 0, 668640, 355395, 621, 16384⟩
    (by decide) selected_cut_26421

theorem unmarked_context_12_88848_668641 : frontier 9 ⟨668641, by decide⟩
    (prefixCache 12 88848) (prefixPartial 12 88848) = false := by
  decide +kernel

theorem node_context_12_88848_668641 : EJMOriginalGlobalDAGData.nodes 9 ⟨668641, by decide⟩ =
    .split (coordinate 12) (![⟨668588, by decide⟩,⟨668615, by decide⟩,⟨668636, by decide⟩,⟨668640, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88848_668641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88848 ⟨668641, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88848
    ⟨668641, by decide⟩ (by decide) (![⟨668588, by decide⟩,⟨668615, by decide⟩,⟨668636, by decide⟩,⟨668640, by decide⟩]) unmarked_context_12_88848_668641 node_context_12_88848_668641
  intro a
  fin_cases a
  · exact context_13_355392_668588
  · exact context_13_355393_668615
  · exact context_13_355394_668636
  · exact context_13_355395_668640

theorem selected_cut_26422 : selected 8 ⟨668685, by decide⟩
    (prefixPartial 13 355396) = some ⟨13, 2, 0, 668685, 355396, 2769, 16384⟩ := by
  decide +kernel

theorem context_13_355396_668685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355396 ⟨668685, by decide⟩ :=
  accepted_of_selected 13 355396 ⟨668685, by decide⟩ ⟨13, 2, 0, 668685, 355396, 2769, 16384⟩
    (by decide) selected_cut_26422

theorem selected_cut_26423 : selected 8 ⟨668715, by decide⟩
    (prefixPartial 13 355397) = some ⟨13, 2, 0, 668715, 355397, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_355397_668715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355397 ⟨668715, by decide⟩ :=
  accepted_of_selected 13 355397 ⟨668715, by decide⟩ ⟨13, 2, 0, 668715, 355397, 1949, 16384⟩
    (by decide) selected_cut_26423

theorem selected_cut_26424 : selected 8 ⟨668736, by decide⟩
    (prefixPartial 13 355398) = some ⟨13, 2, 0, 668736, 355398, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_355398_668736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355398 ⟨668736, by decide⟩ :=
  accepted_of_selected 13 355398 ⟨668736, by decide⟩ ⟨13, 2, 0, 668736, 355398, 1789, 16384⟩
    (by decide) selected_cut_26424

theorem selected_cut_26425 : selected 8 ⟨668742, by decide⟩
    (prefixPartial 13 355399) = some ⟨13, 2, 0, 668742, 355399, 625, 16384⟩ := by
  decide +kernel

theorem context_13_355399_668742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355399 ⟨668742, by decide⟩ :=
  accepted_of_selected 13 355399 ⟨668742, by decide⟩ ⟨13, 2, 0, 668742, 355399, 625, 16384⟩
    (by decide) selected_cut_26425

theorem unmarked_context_12_88849_668743 : frontier 9 ⟨668743, by decide⟩
    (prefixCache 12 88849) (prefixPartial 12 88849) = false := by
  decide +kernel

theorem node_context_12_88849_668743 : EJMOriginalGlobalDAGData.nodes 9 ⟨668743, by decide⟩ =
    .split (coordinate 12) (![⟨668685, by decide⟩,⟨668715, by decide⟩,⟨668736, by decide⟩,⟨668742, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88849_668743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88849 ⟨668743, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88849
    ⟨668743, by decide⟩ (by decide) (![⟨668685, by decide⟩,⟨668715, by decide⟩,⟨668736, by decide⟩,⟨668742, by decide⟩]) unmarked_context_12_88849_668743 node_context_12_88849_668743
  intro a
  fin_cases a
  · exact context_13_355396_668685
  · exact context_13_355397_668715
  · exact context_13_355398_668736
  · exact context_13_355399_668742

theorem selected_cut_26426 : selected 8 ⟨668793, by decide⟩
    (prefixPartial 13 355400) = some ⟨13, 2, 0, 668793, 355400, 3061, 16384⟩ := by
  decide +kernel

theorem context_13_355400_668793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355400 ⟨668793, by decide⟩ :=
  accepted_of_selected 13 355400 ⟨668793, by decide⟩ ⟨13, 2, 0, 668793, 355400, 3061, 16384⟩
    (by decide) selected_cut_26426

theorem selected_cut_26427 : selected 8 ⟨668829, by decide⟩
    (prefixPartial 13 355401) = some ⟨13, 2, 0, 668829, 355401, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_355401_668829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355401 ⟨668829, by decide⟩ :=
  accepted_of_selected 13 355401 ⟨668829, by decide⟩ ⟨13, 2, 0, 668829, 355401, 2421, 16384⟩
    (by decide) selected_cut_26427

theorem selected_cut_26428 : selected 8 ⟨668853, by decide⟩
    (prefixPartial 13 355402) = some ⟨13, 2, 0, 668853, 355402, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_355402_668853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355402 ⟨668853, by decide⟩ :=
  accepted_of_selected 13 355402 ⟨668853, by decide⟩ ⟨13, 2, 0, 668853, 355402, 1929, 16384⟩
    (by decide) selected_cut_26428

theorem selected_cut_26429 : selected 8 ⟨668858, by decide⟩
    (prefixPartial 13 355403) = some ⟨13, 2, 0, 668858, 355403, 645, 16384⟩ := by
  decide +kernel

theorem context_13_355403_668858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355403 ⟨668858, by decide⟩ :=
  accepted_of_selected 13 355403 ⟨668858, by decide⟩ ⟨13, 2, 0, 668858, 355403, 645, 16384⟩
    (by decide) selected_cut_26429

theorem unmarked_context_12_88850_668859 : frontier 9 ⟨668859, by decide⟩
    (prefixCache 12 88850) (prefixPartial 12 88850) = false := by
  decide +kernel

theorem node_context_12_88850_668859 : EJMOriginalGlobalDAGData.nodes 9 ⟨668859, by decide⟩ =
    .split (coordinate 12) (![⟨668793, by decide⟩,⟨668829, by decide⟩,⟨668853, by decide⟩,⟨668858, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88850_668859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88850 ⟨668859, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88850
    ⟨668859, by decide⟩ (by decide) (![⟨668793, by decide⟩,⟨668829, by decide⟩,⟨668853, by decide⟩,⟨668858, by decide⟩]) unmarked_context_12_88850_668859 node_context_12_88850_668859
  intro a
  fin_cases a
  · exact context_13_355400_668793
  · exact context_13_355401_668829
  · exact context_13_355402_668853
  · exact context_13_355403_668858

theorem selected_cut_26430 : selected 8 ⟨668898, by decide⟩
    (prefixPartial 13 355404) = some ⟨13, 2, 0, 668898, 355404, 2597, 16384⟩ := by
  decide +kernel

theorem context_13_355404_668898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355404 ⟨668898, by decide⟩ :=
  accepted_of_selected 13 355404 ⟨668898, by decide⟩ ⟨13, 2, 0, 668898, 355404, 2597, 16384⟩
    (by decide) selected_cut_26430

theorem selected_cut_26431 : selected 8 ⟨668931, by decide⟩
    (prefixPartial 13 355405) = some ⟨13, 2, 0, 668931, 355405, 2365, 16384⟩ := by
  decide +kernel

theorem context_13_355405_668931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355405 ⟨668931, by decide⟩ :=
  accepted_of_selected 13 355405 ⟨668931, by decide⟩ ⟨13, 2, 0, 668931, 355405, 2365, 16384⟩
    (by decide) selected_cut_26431

theorem selected_cut_26432 : selected 8 ⟨668949, by decide⟩
    (prefixPartial 13 355406) = some ⟨13, 2, 0, 668949, 355406, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_355406_668949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355406 ⟨668949, by decide⟩ :=
  accepted_of_selected 13 355406 ⟨668949, by decide⟩ ⟨13, 2, 0, 668949, 355406, 1741, 16384⟩
    (by decide) selected_cut_26432

theorem selected_cut_26433 : selected 8 ⟨668951, by decide⟩
    (prefixPartial 13 355407) = some ⟨13, 2, 0, 668951, 355407, 557, 16384⟩ := by
  decide +kernel

theorem context_13_355407_668951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355407 ⟨668951, by decide⟩ :=
  accepted_of_selected 13 355407 ⟨668951, by decide⟩ ⟨13, 2, 0, 668951, 355407, 557, 16384⟩
    (by decide) selected_cut_26433

theorem unmarked_context_12_88851_668952 : frontier 9 ⟨668952, by decide⟩
    (prefixCache 12 88851) (prefixPartial 12 88851) = false := by
  decide +kernel

theorem node_context_12_88851_668952 : EJMOriginalGlobalDAGData.nodes 9 ⟨668952, by decide⟩ =
    .split (coordinate 12) (![⟨668898, by decide⟩,⟨668931, by decide⟩,⟨668949, by decide⟩,⟨668951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88851_668952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88851 ⟨668952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88851
    ⟨668952, by decide⟩ (by decide) (![⟨668898, by decide⟩,⟨668931, by decide⟩,⟨668949, by decide⟩,⟨668951, by decide⟩]) unmarked_context_12_88851_668952 node_context_12_88851_668952
  intro a
  fin_cases a
  · exact context_13_355404_668898
  · exact context_13_355405_668931
  · exact context_13_355406_668949
  · exact context_13_355407_668951

theorem unmarked_context_11_22212_668953 : frontier 10 ⟨668953, by decide⟩
    (prefixCache 11 22212) (prefixPartial 11 22212) = false := by
  decide +kernel

theorem node_context_11_22212_668953 : EJMOriginalGlobalDAGData.nodes 10 ⟨668953, by decide⟩ =
    .split (coordinate 11) (![⟨668641, by decide⟩,⟨668743, by decide⟩,⟨668859, by decide⟩,⟨668952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22212_668953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22212 ⟨668953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22212
    ⟨668953, by decide⟩ (by decide) (![⟨668641, by decide⟩,⟨668743, by decide⟩,⟨668859, by decide⟩,⟨668952, by decide⟩]) unmarked_context_11_22212_668953 node_context_11_22212_668953
  intro a
  fin_cases a
  · exact context_12_88848_668641
  · exact context_12_88849_668743
  · exact context_12_88850_668859
  · exact context_12_88851_668952

theorem selected_cut_26434 : selected 8 ⟨668986, by decide⟩
    (prefixPartial 13 355408) = some ⟨13, 2, 0, 668986, 355408, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_355408_668986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355408 ⟨668986, by decide⟩ :=
  accepted_of_selected 13 355408 ⟨668986, by decide⟩ ⟨13, 2, 0, 668986, 355408, 1977, 16384⟩
    (by decide) selected_cut_26434

theorem selected_cut_26435 : selected 8 ⟨669036, by decide⟩
    (prefixPartial 13 355409) = some ⟨13, 2, 0, 669036, 355409, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_355409_669036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355409 ⟨669036, by decide⟩ :=
  accepted_of_selected 13 355409 ⟨669036, by decide⟩ ⟨13, 2, 0, 669036, 355409, 2501, 16384⟩
    (by decide) selected_cut_26435

theorem selected_cut_26436 : selected 8 ⟨669053, by decide⟩
    (prefixPartial 13 355410) = some ⟨13, 2, 0, 669053, 355410, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_355410_669053 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355410 ⟨669053, by decide⟩ :=
  accepted_of_selected 13 355410 ⟨669053, by decide⟩ ⟨13, 2, 0, 669053, 355410, 1509, 16384⟩
    (by decide) selected_cut_26436

theorem selected_cut_26437 : selected 8 ⟨669059, by decide⟩
    (prefixPartial 13 355411) = some ⟨13, 2, 0, 669059, 355411, 757, 16384⟩ := by
  decide +kernel

theorem context_13_355411_669059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355411 ⟨669059, by decide⟩ :=
  accepted_of_selected 13 355411 ⟨669059, by decide⟩ ⟨13, 2, 0, 669059, 355411, 757, 16384⟩
    (by decide) selected_cut_26437

theorem unmarked_context_12_88852_669060 : frontier 9 ⟨669060, by decide⟩
    (prefixCache 12 88852) (prefixPartial 12 88852) = false := by
  decide +kernel

theorem node_context_12_88852_669060 : EJMOriginalGlobalDAGData.nodes 9 ⟨669060, by decide⟩ =
    .split (coordinate 12) (![⟨668986, by decide⟩,⟨669036, by decide⟩,⟨669053, by decide⟩,⟨669059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88852_669060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88852 ⟨669060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88852
    ⟨669060, by decide⟩ (by decide) (![⟨668986, by decide⟩,⟨669036, by decide⟩,⟨669053, by decide⟩,⟨669059, by decide⟩]) unmarked_context_12_88852_669060 node_context_12_88852_669060
  intro a
  fin_cases a
  · exact context_13_355408_668986
  · exact context_13_355409_669036
  · exact context_13_355410_669053
  · exact context_13_355411_669059

theorem selected_cut_26438 : selected 8 ⟨669100, by decide⟩
    (prefixPartial 13 355412) = some ⟨13, 2, 0, 669100, 355412, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_355412_669100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355412 ⟨669100, by decide⟩ :=
  accepted_of_selected 13 355412 ⟨669100, by decide⟩ ⟨13, 2, 0, 669100, 355412, 2197, 16384⟩
    (by decide) selected_cut_26438

theorem selected_cut_26439 : selected 8 ⟨669132, by decide⟩
    (prefixPartial 13 355413) = some ⟨13, 2, 0, 669132, 355413, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_355413_669132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355413 ⟨669132, by decide⟩ :=
  accepted_of_selected 13 355413 ⟨669132, by decide⟩ ⟨13, 2, 0, 669132, 355413, 1973, 16384⟩
    (by decide) selected_cut_26439

theorem selected_cut_26440 : selected 8 ⟨669146, by decide⟩
    (prefixPartial 13 355414) = some ⟨13, 2, 0, 669146, 355414, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_355414_669146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355414 ⟨669146, by decide⟩ :=
  accepted_of_selected 13 355414 ⟨669146, by decide⟩ ⟨13, 2, 0, 669146, 355414, 1313, 16384⟩
    (by decide) selected_cut_26440

theorem selected_cut_26441 : selected 8 ⟨669151, by decide⟩
    (prefixPartial 13 355415) = some ⟨13, 2, 0, 669151, 355415, 625, 16384⟩ := by
  decide +kernel

theorem context_13_355415_669151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355415 ⟨669151, by decide⟩ :=
  accepted_of_selected 13 355415 ⟨669151, by decide⟩ ⟨13, 2, 0, 669151, 355415, 625, 16384⟩
    (by decide) selected_cut_26441

theorem unmarked_context_12_88853_669152 : frontier 9 ⟨669152, by decide⟩
    (prefixCache 12 88853) (prefixPartial 12 88853) = false := by
  decide +kernel

theorem node_context_12_88853_669152 : EJMOriginalGlobalDAGData.nodes 9 ⟨669152, by decide⟩ =
    .split (coordinate 12) (![⟨669100, by decide⟩,⟨669132, by decide⟩,⟨669146, by decide⟩,⟨669151, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88853_669152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88853 ⟨669152, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88853
    ⟨669152, by decide⟩ (by decide) (![⟨669100, by decide⟩,⟨669132, by decide⟩,⟨669146, by decide⟩,⟨669151, by decide⟩]) unmarked_context_12_88853_669152 node_context_12_88853_669152
  intro a
  fin_cases a
  · exact context_13_355412_669100
  · exact context_13_355413_669132
  · exact context_13_355414_669146
  · exact context_13_355415_669151

theorem selected_cut_26442 : selected 8 ⟨669189, by decide⟩
    (prefixPartial 13 355416) = some ⟨13, 2, 0, 669189, 355416, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_355416_669189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355416 ⟨669189, by decide⟩ :=
  accepted_of_selected 13 355416 ⟨669189, by decide⟩ ⟨13, 2, 0, 669189, 355416, 2377, 16384⟩
    (by decide) selected_cut_26442

theorem selected_cut_26443 : selected 8 ⟨669230, by decide⟩
    (prefixPartial 13 355417) = some ⟨13, 2, 0, 669230, 355417, 2489, 16384⟩ := by
  decide +kernel

theorem context_13_355417_669230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355417 ⟨669230, by decide⟩ :=
  accepted_of_selected 13 355417 ⟨669230, by decide⟩ ⟨13, 2, 0, 669230, 355417, 2489, 16384⟩
    (by decide) selected_cut_26443

theorem selected_cut_26444 : selected 8 ⟨669250, by decide⟩
    (prefixPartial 13 355418) = some ⟨13, 2, 0, 669250, 355418, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_355418_669250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355418 ⟨669250, by decide⟩ :=
  accepted_of_selected 13 355418 ⟨669250, by decide⟩ ⟨13, 2, 0, 669250, 355418, 1629, 16384⟩
    (by decide) selected_cut_26444

theorem selected_cut_26445 : selected 8 ⟨669256, by decide⟩
    (prefixPartial 13 355419) = some ⟨13, 2, 0, 669256, 355419, 713, 16384⟩ := by
  decide +kernel

theorem context_13_355419_669256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355419 ⟨669256, by decide⟩ :=
  accepted_of_selected 13 355419 ⟨669256, by decide⟩ ⟨13, 2, 0, 669256, 355419, 713, 16384⟩
    (by decide) selected_cut_26445

theorem unmarked_context_12_88854_669257 : frontier 9 ⟨669257, by decide⟩
    (prefixCache 12 88854) (prefixPartial 12 88854) = false := by
  decide +kernel

theorem node_context_12_88854_669257 : EJMOriginalGlobalDAGData.nodes 9 ⟨669257, by decide⟩ =
    .split (coordinate 12) (![⟨669189, by decide⟩,⟨669230, by decide⟩,⟨669250, by decide⟩,⟨669256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88854_669257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88854 ⟨669257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88854
    ⟨669257, by decide⟩ (by decide) (![⟨669189, by decide⟩,⟨669230, by decide⟩,⟨669250, by decide⟩,⟨669256, by decide⟩]) unmarked_context_12_88854_669257 node_context_12_88854_669257
  intro a
  fin_cases a
  · exact context_13_355416_669189
  · exact context_13_355417_669230
  · exact context_13_355418_669250
  · exact context_13_355419_669256

theorem selected_cut_26446 : selected 8 ⟨669291, by decide⟩
    (prefixPartial 13 355420) = some ⟨13, 2, 0, 669291, 355420, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_355420_669291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355420 ⟨669291, by decide⟩ :=
  accepted_of_selected 13 355420 ⟨669291, by decide⟩ ⟨13, 2, 0, 669291, 355420, 2097, 16384⟩
    (by decide) selected_cut_26446

theorem selected_cut_26447 : selected 8 ⟨669333, by decide⟩
    (prefixPartial 13 355421) = some ⟨13, 2, 0, 669333, 355421, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_355421_669333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355421 ⟨669333, by decide⟩ :=
  accepted_of_selected 13 355421 ⟨669333, by decide⟩ ⟨13, 2, 0, 669333, 355421, 2493, 16384⟩
    (by decide) selected_cut_26447

theorem selected_cut_26448 : selected 8 ⟨669351, by decide⟩
    (prefixPartial 13 355422) = some ⟨13, 2, 0, 669351, 355422, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_355422_669351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355422 ⟨669351, by decide⟩ :=
  accepted_of_selected 13 355422 ⟨669351, by decide⟩ ⟨13, 2, 0, 669351, 355422, 1461, 16384⟩
    (by decide) selected_cut_26448

theorem selected_cut_26449 : selected 8 ⟨669355, by decide⟩
    (prefixPartial 13 355423) = some ⟨13, 2, 0, 669355, 355423, 609, 16384⟩ := by
  decide +kernel

theorem context_13_355423_669355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355423 ⟨669355, by decide⟩ :=
  accepted_of_selected 13 355423 ⟨669355, by decide⟩ ⟨13, 2, 0, 669355, 355423, 609, 16384⟩
    (by decide) selected_cut_26449

theorem unmarked_context_12_88855_669356 : frontier 9 ⟨669356, by decide⟩
    (prefixCache 12 88855) (prefixPartial 12 88855) = false := by
  decide +kernel

theorem node_context_12_88855_669356 : EJMOriginalGlobalDAGData.nodes 9 ⟨669356, by decide⟩ =
    .split (coordinate 12) (![⟨669291, by decide⟩,⟨669333, by decide⟩,⟨669351, by decide⟩,⟨669355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88855_669356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88855 ⟨669356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88855
    ⟨669356, by decide⟩ (by decide) (![⟨669291, by decide⟩,⟨669333, by decide⟩,⟨669351, by decide⟩,⟨669355, by decide⟩]) unmarked_context_12_88855_669356 node_context_12_88855_669356
  intro a
  fin_cases a
  · exact context_13_355420_669291
  · exact context_13_355421_669333
  · exact context_13_355422_669351
  · exact context_13_355423_669355

theorem unmarked_context_11_22213_669357 : frontier 10 ⟨669357, by decide⟩
    (prefixCache 11 22213) (prefixPartial 11 22213) = false := by
  decide +kernel

theorem node_context_11_22213_669357 : EJMOriginalGlobalDAGData.nodes 10 ⟨669357, by decide⟩ =
    .split (coordinate 11) (![⟨669060, by decide⟩,⟨669152, by decide⟩,⟨669257, by decide⟩,⟨669356, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22213_669357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22213 ⟨669357, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22213
    ⟨669357, by decide⟩ (by decide) (![⟨669060, by decide⟩,⟨669152, by decide⟩,⟨669257, by decide⟩,⟨669356, by decide⟩]) unmarked_context_11_22213_669357 node_context_11_22213_669357
  intro a
  fin_cases a
  · exact context_12_88852_669060
  · exact context_12_88853_669152
  · exact context_12_88854_669257
  · exact context_12_88855_669356

theorem selected_cut_26450 : selected 8 ⟨669383, by decide⟩
    (prefixPartial 13 355424) = some ⟨13, 2, 0, 669383, 355424, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_355424_669383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355424 ⟨669383, by decide⟩ :=
  accepted_of_selected 13 355424 ⟨669383, by decide⟩ ⟨13, 2, 0, 669383, 355424, 1685, 16384⟩
    (by decide) selected_cut_26450

theorem selected_cut_26451 : selected 8 ⟨669414, by decide⟩
    (prefixPartial 13 355425) = some ⟨13, 2, 0, 669414, 355425, 2177, 16384⟩ := by
  decide +kernel

theorem context_13_355425_669414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355425 ⟨669414, by decide⟩ :=
  accepted_of_selected 13 355425 ⟨669414, by decide⟩ ⟨13, 2, 0, 669414, 355425, 2177, 16384⟩
    (by decide) selected_cut_26451

theorem selected_cut_26452 : selected 8 ⟨669436, by decide⟩
    (prefixPartial 13 355426) = some ⟨13, 2, 0, 669436, 355426, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_355426_669436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355426 ⟨669436, by decide⟩ :=
  accepted_of_selected 13 355426 ⟨669436, by decide⟩ ⟨13, 2, 0, 669436, 355426, 1873, 16384⟩
    (by decide) selected_cut_26452

theorem selected_cut_26453 : selected 8 ⟨669441, by decide⟩
    (prefixPartial 13 355427) = some ⟨13, 2, 0, 669441, 355427, 709, 16384⟩ := by
  decide +kernel

theorem context_13_355427_669441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355427 ⟨669441, by decide⟩ :=
  accepted_of_selected 13 355427 ⟨669441, by decide⟩ ⟨13, 2, 0, 669441, 355427, 709, 16384⟩
    (by decide) selected_cut_26453

theorem unmarked_context_12_88856_669442 : frontier 9 ⟨669442, by decide⟩
    (prefixCache 12 88856) (prefixPartial 12 88856) = false := by
  decide +kernel

theorem node_context_12_88856_669442 : EJMOriginalGlobalDAGData.nodes 9 ⟨669442, by decide⟩ =
    .split (coordinate 12) (![⟨669383, by decide⟩,⟨669414, by decide⟩,⟨669436, by decide⟩,⟨669441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88856_669442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88856 ⟨669442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88856
    ⟨669442, by decide⟩ (by decide) (![⟨669383, by decide⟩,⟨669414, by decide⟩,⟨669436, by decide⟩,⟨669441, by decide⟩]) unmarked_context_12_88856_669442 node_context_12_88856_669442
  intro a
  fin_cases a
  · exact context_13_355424_669383
  · exact context_13_355425_669414
  · exact context_13_355426_669436
  · exact context_13_355427_669441

theorem selected_cut_26454 : selected 8 ⟨669473, by decide⟩
    (prefixPartial 13 355428) = some ⟨13, 2, 0, 669473, 355428, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_355428_669473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355428 ⟨669473, by decide⟩ :=
  accepted_of_selected 13 355428 ⟨669473, by decide⟩ ⟨13, 2, 0, 669473, 355428, 2021, 16384⟩
    (by decide) selected_cut_26454

theorem selected_cut_26455 : selected 8 ⟨669503, by decide⟩
    (prefixPartial 13 355429) = some ⟨13, 2, 0, 669503, 355429, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_355429_669503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355429 ⟨669503, by decide⟩ :=
  accepted_of_selected 13 355429 ⟨669503, by decide⟩ ⟨13, 2, 0, 669503, 355429, 1801, 16384⟩
    (by decide) selected_cut_26455

theorem selected_cut_26456 : selected 8 ⟨669523, by decide⟩
    (prefixPartial 13 355430) = some ⟨13, 2, 0, 669523, 355430, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_355430_669523 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355430 ⟨669523, by decide⟩ :=
  accepted_of_selected 13 355430 ⟨669523, by decide⟩ ⟨13, 2, 0, 669523, 355430, 1853, 16384⟩
    (by decide) selected_cut_26456

theorem selected_cut_26457 : selected 8 ⟨669530, by decide⟩
    (prefixPartial 13 355431) = some ⟨13, 2, 0, 669530, 355431, 649, 16384⟩ := by
  decide +kernel

theorem context_13_355431_669530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355431 ⟨669530, by decide⟩ :=
  accepted_of_selected 13 355431 ⟨669530, by decide⟩ ⟨13, 2, 0, 669530, 355431, 649, 16384⟩
    (by decide) selected_cut_26457

theorem unmarked_context_12_88857_669531 : frontier 9 ⟨669531, by decide⟩
    (prefixCache 12 88857) (prefixPartial 12 88857) = false := by
  decide +kernel

theorem node_context_12_88857_669531 : EJMOriginalGlobalDAGData.nodes 9 ⟨669531, by decide⟩ =
    .split (coordinate 12) (![⟨669473, by decide⟩,⟨669503, by decide⟩,⟨669523, by decide⟩,⟨669530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88857_669531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88857 ⟨669531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88857
    ⟨669531, by decide⟩ (by decide) (![⟨669473, by decide⟩,⟨669503, by decide⟩,⟨669523, by decide⟩,⟨669530, by decide⟩]) unmarked_context_12_88857_669531 node_context_12_88857_669531
  intro a
  fin_cases a
  · exact context_13_355428_669473
  · exact context_13_355429_669503
  · exact context_13_355430_669523
  · exact context_13_355431_669530

theorem selected_cut_26458 : selected 8 ⟨669562, by decide⟩
    (prefixPartial 13 355432) = some ⟨13, 2, 0, 669562, 355432, 2205, 16384⟩ := by
  decide +kernel

theorem context_13_355432_669562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355432 ⟨669562, by decide⟩ :=
  accepted_of_selected 13 355432 ⟨669562, by decide⟩ ⟨13, 2, 0, 669562, 355432, 2205, 16384⟩
    (by decide) selected_cut_26458

theorem selected_cut_26459 : selected 8 ⟨669591, by decide⟩
    (prefixPartial 13 355433) = some ⟨13, 2, 0, 669591, 355433, 2549, 16384⟩ := by
  decide +kernel

theorem context_13_355433_669591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355433 ⟨669591, by decide⟩ :=
  accepted_of_selected 13 355433 ⟨669591, by decide⟩ ⟨13, 2, 0, 669591, 355433, 2549, 16384⟩
    (by decide) selected_cut_26459

theorem selected_cut_26460 : selected 8 ⟨669616, by decide⟩
    (prefixPartial 13 355434) = some ⟨13, 2, 0, 669616, 355434, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_355434_669616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355434 ⟨669616, by decide⟩ :=
  accepted_of_selected 13 355434 ⟨669616, by decide⟩ ⟨13, 2, 0, 669616, 355434, 2005, 16384⟩
    (by decide) selected_cut_26460

theorem selected_cut_26461 : selected 8 ⟨669622, by decide⟩
    (prefixPartial 13 355435) = some ⟨13, 2, 0, 669622, 355435, 749, 16384⟩ := by
  decide +kernel

theorem context_13_355435_669622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355435 ⟨669622, by decide⟩ :=
  accepted_of_selected 13 355435 ⟨669622, by decide⟩ ⟨13, 2, 0, 669622, 355435, 749, 16384⟩
    (by decide) selected_cut_26461

theorem unmarked_context_12_88858_669623 : frontier 9 ⟨669623, by decide⟩
    (prefixCache 12 88858) (prefixPartial 12 88858) = false := by
  decide +kernel

theorem node_context_12_88858_669623 : EJMOriginalGlobalDAGData.nodes 9 ⟨669623, by decide⟩ =
    .split (coordinate 12) (![⟨669562, by decide⟩,⟨669591, by decide⟩,⟨669616, by decide⟩,⟨669622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88858_669623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88858 ⟨669623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88858
    ⟨669623, by decide⟩ (by decide) (![⟨669562, by decide⟩,⟨669591, by decide⟩,⟨669616, by decide⟩,⟨669622, by decide⟩]) unmarked_context_12_88858_669623 node_context_12_88858_669623
  intro a
  fin_cases a
  · exact context_13_355432_669562
  · exact context_13_355433_669591
  · exact context_13_355434_669616
  · exact context_13_355435_669622

theorem selected_cut_26462 : selected 8 ⟨669658, by decide⟩
    (prefixPartial 13 355436) = some ⟨13, 2, 0, 669658, 355436, 1857, 16384⟩ := by
  decide +kernel

theorem context_13_355436_669658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355436 ⟨669658, by decide⟩ :=
  accepted_of_selected 13 355436 ⟨669658, by decide⟩ ⟨13, 2, 0, 669658, 355436, 1857, 16384⟩
    (by decide) selected_cut_26462

theorem selected_cut_26463 : selected 8 ⟨669693, by decide⟩
    (prefixPartial 13 355437) = some ⟨13, 2, 0, 669693, 355437, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_355437_669693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355437 ⟨669693, by decide⟩ :=
  accepted_of_selected 13 355437 ⟨669693, by decide⟩ ⟨13, 2, 0, 669693, 355437, 2541, 16384⟩
    (by decide) selected_cut_26463

theorem selected_cut_26464 : selected 8 ⟨669707, by decide⟩
    (prefixPartial 13 355438) = some ⟨13, 2, 0, 669707, 355438, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_355438_669707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355438 ⟨669707, by decide⟩ :=
  accepted_of_selected 13 355438 ⟨669707, by decide⟩ ⟨13, 2, 0, 669707, 355438, 1905, 16384⟩
    (by decide) selected_cut_26464

theorem selected_cut_26465 : selected 8 ⟨669712, by decide⟩
    (prefixPartial 13 355439) = some ⟨13, 2, 0, 669712, 355439, 633, 16384⟩ := by
  decide +kernel

theorem context_13_355439_669712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355439 ⟨669712, by decide⟩ :=
  accepted_of_selected 13 355439 ⟨669712, by decide⟩ ⟨13, 2, 0, 669712, 355439, 633, 16384⟩
    (by decide) selected_cut_26465

theorem unmarked_context_12_88859_669713 : frontier 9 ⟨669713, by decide⟩
    (prefixCache 12 88859) (prefixPartial 12 88859) = false := by
  decide +kernel

theorem node_context_12_88859_669713 : EJMOriginalGlobalDAGData.nodes 9 ⟨669713, by decide⟩ =
    .split (coordinate 12) (![⟨669658, by decide⟩,⟨669693, by decide⟩,⟨669707, by decide⟩,⟨669712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88859_669713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88859 ⟨669713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88859
    ⟨669713, by decide⟩ (by decide) (![⟨669658, by decide⟩,⟨669693, by decide⟩,⟨669707, by decide⟩,⟨669712, by decide⟩]) unmarked_context_12_88859_669713 node_context_12_88859_669713
  intro a
  fin_cases a
  · exact context_13_355436_669658
  · exact context_13_355437_669693
  · exact context_13_355438_669707
  · exact context_13_355439_669712

theorem unmarked_context_11_22214_669714 : frontier 10 ⟨669714, by decide⟩
    (prefixCache 11 22214) (prefixPartial 11 22214) = false := by
  decide +kernel

theorem node_context_11_22214_669714 : EJMOriginalGlobalDAGData.nodes 10 ⟨669714, by decide⟩ =
    .split (coordinate 11) (![⟨669442, by decide⟩,⟨669531, by decide⟩,⟨669623, by decide⟩,⟨669713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22214_669714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22214 ⟨669714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22214
    ⟨669714, by decide⟩ (by decide) (![⟨669442, by decide⟩,⟨669531, by decide⟩,⟨669623, by decide⟩,⟨669713, by decide⟩]) unmarked_context_11_22214_669714 node_context_11_22214_669714
  intro a
  fin_cases a
  · exact context_12_88856_669442
  · exact context_12_88857_669531
  · exact context_12_88858_669623
  · exact context_12_88859_669713

theorem selected_cut_26466 : selected 8 ⟨669741, by decide⟩
    (prefixPartial 13 355440) = some ⟨13, 2, 0, 669741, 355440, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_355440_669741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355440 ⟨669741, by decide⟩ :=
  accepted_of_selected 13 355440 ⟨669741, by decide⟩ ⟨13, 2, 0, 669741, 355440, 1589, 16384⟩
    (by decide) selected_cut_26466

theorem selected_cut_26467 : selected 8 ⟨669771, by decide⟩
    (prefixPartial 13 355441) = some ⟨13, 2, 0, 669771, 355441, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_355441_669771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355441 ⟨669771, by decide⟩ :=
  accepted_of_selected 13 355441 ⟨669771, by decide⟩ ⟨13, 2, 0, 669771, 355441, 1893, 16384⟩
    (by decide) selected_cut_26467

theorem selected_cut_26468 : selected 8 ⟨669791, by decide⟩
    (prefixPartial 13 355442) = some ⟨13, 2, 0, 669791, 355442, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_355442_669791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355442 ⟨669791, by decide⟩ :=
  accepted_of_selected 13 355442 ⟨669791, by decide⟩ ⟨13, 2, 0, 669791, 355442, 1709, 16384⟩
    (by decide) selected_cut_26468

theorem selected_cut_26469 : selected 8 ⟨669801, by decide⟩
    (prefixPartial 13 355443) = some ⟨13, 2, 0, 669801, 355443, 729, 16384⟩ := by
  decide +kernel

theorem context_13_355443_669801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355443 ⟨669801, by decide⟩ :=
  accepted_of_selected 13 355443 ⟨669801, by decide⟩ ⟨13, 2, 0, 669801, 355443, 729, 16384⟩
    (by decide) selected_cut_26469

theorem unmarked_context_12_88860_669802 : frontier 9 ⟨669802, by decide⟩
    (prefixCache 12 88860) (prefixPartial 12 88860) = false := by
  decide +kernel

theorem node_context_12_88860_669802 : EJMOriginalGlobalDAGData.nodes 9 ⟨669802, by decide⟩ =
    .split (coordinate 12) (![⟨669741, by decide⟩,⟨669771, by decide⟩,⟨669791, by decide⟩,⟨669801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88860_669802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88860 ⟨669802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88860
    ⟨669802, by decide⟩ (by decide) (![⟨669741, by decide⟩,⟨669771, by decide⟩,⟨669791, by decide⟩,⟨669801, by decide⟩]) unmarked_context_12_88860_669802 node_context_12_88860_669802
  intro a
  fin_cases a
  · exact context_13_355440_669741
  · exact context_13_355441_669771
  · exact context_13_355442_669791
  · exact context_13_355443_669801

theorem selected_cut_26470 : selected 8 ⟨669824, by decide⟩
    (prefixPartial 13 355444) = some ⟨13, 2, 0, 669824, 355444, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_355444_669824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355444 ⟨669824, by decide⟩ :=
  accepted_of_selected 13 355444 ⟨669824, by decide⟩ ⟨13, 2, 0, 669824, 355444, 1689, 16384⟩
    (by decide) selected_cut_26470

theorem selected_cut_26471 : selected 8 ⟨669844, by decide⟩
    (prefixPartial 13 355445) = some ⟨13, 2, 0, 669844, 355445, 1625, 16384⟩ := by
  decide +kernel

theorem context_13_355445_669844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355445 ⟨669844, by decide⟩ :=
  accepted_of_selected 13 355445 ⟨669844, by decide⟩ ⟨13, 2, 0, 669844, 355445, 1625, 16384⟩
    (by decide) selected_cut_26471

theorem selected_cut_26472 : selected 8 ⟨669867, by decide⟩
    (prefixPartial 13 355446) = some ⟨13, 2, 0, 669867, 355446, 1805, 16384⟩ := by
  decide +kernel

theorem context_13_355446_669867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355446 ⟨669867, by decide⟩ :=
  accepted_of_selected 13 355446 ⟨669867, by decide⟩ ⟨13, 2, 0, 669867, 355446, 1805, 16384⟩
    (by decide) selected_cut_26472

theorem selected_cut_26473 : selected 8 ⟨669875, by decide⟩
    (prefixPartial 13 355447) = some ⟨13, 2, 0, 669875, 355447, 669, 16384⟩ := by
  decide +kernel

theorem context_13_355447_669875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355447 ⟨669875, by decide⟩ :=
  accepted_of_selected 13 355447 ⟨669875, by decide⟩ ⟨13, 2, 0, 669875, 355447, 669, 16384⟩
    (by decide) selected_cut_26473

theorem unmarked_context_12_88861_669876 : frontier 9 ⟨669876, by decide⟩
    (prefixCache 12 88861) (prefixPartial 12 88861) = false := by
  decide +kernel

theorem node_context_12_88861_669876 : EJMOriginalGlobalDAGData.nodes 9 ⟨669876, by decide⟩ =
    .split (coordinate 12) (![⟨669824, by decide⟩,⟨669844, by decide⟩,⟨669867, by decide⟩,⟨669875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88861_669876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88861 ⟨669876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88861
    ⟨669876, by decide⟩ (by decide) (![⟨669824, by decide⟩,⟨669844, by decide⟩,⟨669867, by decide⟩,⟨669875, by decide⟩]) unmarked_context_12_88861_669876 node_context_12_88861_669876
  intro a
  fin_cases a
  · exact context_13_355444_669824
  · exact context_13_355445_669844
  · exact context_13_355446_669867
  · exact context_13_355447_669875

theorem selected_cut_26474 : selected 8 ⟨669907, by decide⟩
    (prefixPartial 13 355448) = some ⟨13, 2, 0, 669907, 355448, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_355448_669907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355448 ⟨669907, by decide⟩ :=
  accepted_of_selected 13 355448 ⟨669907, by decide⟩ ⟨13, 2, 0, 669907, 355448, 1917, 16384⟩
    (by decide) selected_cut_26474

theorem selected_cut_26475 : selected 8 ⟨669950, by decide⟩
    (prefixPartial 13 355449) = some ⟨13, 2, 0, 669950, 355449, 2497, 16384⟩ := by
  decide +kernel

theorem context_13_355449_669950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355449 ⟨669950, by decide⟩ :=
  accepted_of_selected 13 355449 ⟨669950, by decide⟩ ⟨13, 2, 0, 669950, 355449, 2497, 16384⟩
    (by decide) selected_cut_26475

theorem selected_cut_26476 : selected 8 ⟨669967, by decide⟩
    (prefixPartial 13 355450) = some ⟨13, 2, 0, 669967, 355450, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_355450_669967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355450 ⟨669967, by decide⟩ :=
  accepted_of_selected 13 355450 ⟨669967, by decide⟩ ⟨13, 2, 0, 669967, 355450, 1841, 16384⟩
    (by decide) selected_cut_26476

theorem selected_cut_26477 : selected 8 ⟨669973, by decide⟩
    (prefixPartial 13 355451) = some ⟨13, 2, 0, 669973, 355451, 713, 16384⟩ := by
  decide +kernel

theorem context_13_355451_669973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355451 ⟨669973, by decide⟩ :=
  accepted_of_selected 13 355451 ⟨669973, by decide⟩ ⟨13, 2, 0, 669973, 355451, 713, 16384⟩
    (by decide) selected_cut_26477

theorem unmarked_context_12_88862_669974 : frontier 9 ⟨669974, by decide⟩
    (prefixCache 12 88862) (prefixPartial 12 88862) = false := by
  decide +kernel

theorem node_context_12_88862_669974 : EJMOriginalGlobalDAGData.nodes 9 ⟨669974, by decide⟩ =
    .split (coordinate 12) (![⟨669907, by decide⟩,⟨669950, by decide⟩,⟨669967, by decide⟩,⟨669973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88862_669974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88862 ⟨669974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88862
    ⟨669974, by decide⟩ (by decide) (![⟨669907, by decide⟩,⟨669950, by decide⟩,⟨669967, by decide⟩,⟨669973, by decide⟩]) unmarked_context_12_88862_669974 node_context_12_88862_669974
  intro a
  fin_cases a
  · exact context_13_355448_669907
  · exact context_13_355449_669950
  · exact context_13_355450_669967
  · exact context_13_355451_669973

theorem selected_cut_26478 : selected 8 ⟨670035, by decide⟩
    (prefixPartial 13 355452) = some ⟨13, 2, 0, 670035, 355452, 2789, 16384⟩ := by
  decide +kernel

theorem context_13_355452_670035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355452 ⟨670035, by decide⟩ :=
  accepted_of_selected 13 355452 ⟨670035, by decide⟩ ⟨13, 2, 0, 670035, 355452, 2789, 16384⟩
    (by decide) selected_cut_26478

theorem selected_cut_26479 : selected 8 ⟨670128, by decide⟩
    (prefixPartial 13 355453) = some ⟨13, 2, 0, 670128, 355453, 3625, 16384⟩ := by
  decide +kernel

theorem context_13_355453_670128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355453 ⟨670128, by decide⟩ :=
  accepted_of_selected 13 355453 ⟨670128, by decide⟩ ⟨13, 2, 0, 670128, 355453, 3625, 16384⟩
    (by decide) selected_cut_26479

theorem selected_cut_26480 : selected 8 ⟨670166, by decide⟩
    (prefixPartial 13 355454) = some ⟨13, 2, 0, 670166, 355454, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_355454_670166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355454 ⟨670166, by decide⟩ :=
  accepted_of_selected 13 355454 ⟨670166, by decide⟩ ⟨13, 2, 0, 670166, 355454, 2577, 16384⟩
    (by decide) selected_cut_26480

theorem selected_cut_26481 : selected 8 ⟨670175, by decide⟩
    (prefixPartial 13 355455) = some ⟨13, 2, 0, 670175, 355455, 945, 16384⟩ := by
  decide +kernel

theorem context_13_355455_670175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355455 ⟨670175, by decide⟩ :=
  accepted_of_selected 13 355455 ⟨670175, by decide⟩ ⟨13, 2, 0, 670175, 355455, 945, 16384⟩
    (by decide) selected_cut_26481

theorem unmarked_context_12_88863_670176 : frontier 9 ⟨670176, by decide⟩
    (prefixCache 12 88863) (prefixPartial 12 88863) = false := by
  decide +kernel

theorem node_context_12_88863_670176 : EJMOriginalGlobalDAGData.nodes 9 ⟨670176, by decide⟩ =
    .split (coordinate 12) (![⟨670035, by decide⟩,⟨670128, by decide⟩,⟨670166, by decide⟩,⟨670175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88863_670176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88863 ⟨670176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88863
    ⟨670176, by decide⟩ (by decide) (![⟨670035, by decide⟩,⟨670128, by decide⟩,⟨670166, by decide⟩,⟨670175, by decide⟩]) unmarked_context_12_88863_670176 node_context_12_88863_670176
  intro a
  fin_cases a
  · exact context_13_355452_670035
  · exact context_13_355453_670128
  · exact context_13_355454_670166
  · exact context_13_355455_670175

theorem unmarked_context_11_22215_670177 : frontier 10 ⟨670177, by decide⟩
    (prefixCache 11 22215) (prefixPartial 11 22215) = false := by
  decide +kernel

theorem node_context_11_22215_670177 : EJMOriginalGlobalDAGData.nodes 10 ⟨670177, by decide⟩ =
    .split (coordinate 11) (![⟨669802, by decide⟩,⟨669876, by decide⟩,⟨669974, by decide⟩,⟨670176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22215_670177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22215 ⟨670177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22215
    ⟨670177, by decide⟩ (by decide) (![⟨669802, by decide⟩,⟨669876, by decide⟩,⟨669974, by decide⟩,⟨670176, by decide⟩]) unmarked_context_11_22215_670177 node_context_11_22215_670177
  intro a
  fin_cases a
  · exact context_12_88860_669802
  · exact context_12_88861_669876
  · exact context_12_88862_669974
  · exact context_12_88863_670176

theorem unmarked_context_10_5553_670178 : frontier 11 ⟨670178, by decide⟩
    (prefixCache 10 5553) (prefixPartial 10 5553) = false := by
  decide +kernel

theorem node_context_10_5553_670178 : EJMOriginalGlobalDAGData.nodes 11 ⟨670178, by decide⟩ =
    .split (coordinate 10) (![⟨668953, by decide⟩,⟨669357, by decide⟩,⟨669714, by decide⟩,⟨670177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5553_670178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5553 ⟨670178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5553
    ⟨670178, by decide⟩ (by decide) (![⟨668953, by decide⟩,⟨669357, by decide⟩,⟨669714, by decide⟩,⟨670177, by decide⟩]) unmarked_context_10_5553_670178 node_context_10_5553_670178
  intro a
  fin_cases a
  · exact context_11_22212_668953
  · exact context_11_22213_669357
  · exact context_11_22214_669714
  · exact context_11_22215_670177

theorem selected_cut_26482 : selected 8 ⟨670197, by decide⟩
    (prefixPartial 13 355456) = some ⟨13, 2, 0, 670197, 355456, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_355456_670197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355456 ⟨670197, by decide⟩ :=
  accepted_of_selected 13 355456 ⟨670197, by decide⟩ ⟨13, 2, 0, 670197, 355456, 1417, 16384⟩
    (by decide) selected_cut_26482

theorem selected_cut_26483 : selected 8 ⟨670218, by decide⟩
    (prefixPartial 13 355457) = some ⟨13, 2, 0, 670218, 355457, 1933, 16384⟩ := by
  decide +kernel

theorem context_13_355457_670218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355457 ⟨670218, by decide⟩ :=
  accepted_of_selected 13 355457 ⟨670218, by decide⟩ ⟨13, 2, 0, 670218, 355457, 1933, 16384⟩
    (by decide) selected_cut_26483

theorem selected_cut_26484 : selected 8 ⟨670233, by decide⟩
    (prefixPartial 13 355458) = some ⟨13, 2, 0, 670233, 355458, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_355458_670233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355458 ⟨670233, by decide⟩ :=
  accepted_of_selected 13 355458 ⟨670233, by decide⟩ ⟨13, 2, 0, 670233, 355458, 1273, 16384⟩
    (by decide) selected_cut_26484

theorem selected_cut_26485 : selected 8 ⟨670241, by decide⟩
    (prefixPartial 13 355459) = some ⟨13, 2, 0, 670241, 355459, 757, 16384⟩ := by
  decide +kernel

theorem context_13_355459_670241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355459 ⟨670241, by decide⟩ :=
  accepted_of_selected 13 355459 ⟨670241, by decide⟩ ⟨13, 2, 0, 670241, 355459, 757, 16384⟩
    (by decide) selected_cut_26485

theorem unmarked_context_12_88864_670242 : frontier 9 ⟨670242, by decide⟩
    (prefixCache 12 88864) (prefixPartial 12 88864) = false := by
  decide +kernel

theorem node_context_12_88864_670242 : EJMOriginalGlobalDAGData.nodes 9 ⟨670242, by decide⟩ =
    .split (coordinate 12) (![⟨670197, by decide⟩,⟨670218, by decide⟩,⟨670233, by decide⟩,⟨670241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88864_670242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88864 ⟨670242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88864
    ⟨670242, by decide⟩ (by decide) (![⟨670197, by decide⟩,⟨670218, by decide⟩,⟨670233, by decide⟩,⟨670241, by decide⟩]) unmarked_context_12_88864_670242 node_context_12_88864_670242
  intro a
  fin_cases a
  · exact context_13_355456_670197
  · exact context_13_355457_670218
  · exact context_13_355458_670233
  · exact context_13_355459_670241

theorem selected_cut_26486 : selected 8 ⟨670261, by decide⟩
    (prefixPartial 13 355460) = some ⟨13, 2, 0, 670261, 355460, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_355460_670261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355460 ⟨670261, by decide⟩ :=
  accepted_of_selected 13 355460 ⟨670261, by decide⟩ ⟨13, 2, 0, 670261, 355460, 1377, 16384⟩
    (by decide) selected_cut_26486

theorem selected_cut_26487 : selected 8 ⟨670284, by decide⟩
    (prefixPartial 13 355461) = some ⟨13, 2, 0, 670284, 355461, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_355461_670284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355461 ⟨670284, by decide⟩ :=
  accepted_of_selected 13 355461 ⟨670284, by decide⟩ ⟨13, 2, 0, 670284, 355461, 1833, 16384⟩
    (by decide) selected_cut_26487

theorem selected_cut_26488 : selected 8 ⟨670299, by decide⟩
    (prefixPartial 13 355462) = some ⟨13, 2, 0, 670299, 355462, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_355462_670299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355462 ⟨670299, by decide⟩ :=
  accepted_of_selected 13 355462 ⟨670299, by decide⟩ ⟨13, 2, 0, 670299, 355462, 1389, 16384⟩
    (by decide) selected_cut_26488

theorem selected_cut_26489 : selected 8 ⟨670305, by decide⟩
    (prefixPartial 13 355463) = some ⟨13, 2, 0, 670305, 355463, 657, 16384⟩ := by
  decide +kernel

theorem context_13_355463_670305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355463 ⟨670305, by decide⟩ :=
  accepted_of_selected 13 355463 ⟨670305, by decide⟩ ⟨13, 2, 0, 670305, 355463, 657, 16384⟩
    (by decide) selected_cut_26489

theorem unmarked_context_12_88865_670306 : frontier 9 ⟨670306, by decide⟩
    (prefixCache 12 88865) (prefixPartial 12 88865) = false := by
  decide +kernel

theorem node_context_12_88865_670306 : EJMOriginalGlobalDAGData.nodes 9 ⟨670306, by decide⟩ =
    .split (coordinate 12) (![⟨670261, by decide⟩,⟨670284, by decide⟩,⟨670299, by decide⟩,⟨670305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88865_670306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88865 ⟨670306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88865
    ⟨670306, by decide⟩ (by decide) (![⟨670261, by decide⟩,⟨670284, by decide⟩,⟨670299, by decide⟩,⟨670305, by decide⟩]) unmarked_context_12_88865_670306 node_context_12_88865_670306
  intro a
  fin_cases a
  · exact context_13_355460_670261
  · exact context_13_355461_670284
  · exact context_13_355462_670299
  · exact context_13_355463_670305

theorem selected_cut_26490 : selected 8 ⟨670330, by decide⟩
    (prefixPartial 13 355464) = some ⟨13, 2, 0, 670330, 355464, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_355464_670330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355464 ⟨670330, by decide⟩ :=
  accepted_of_selected 13 355464 ⟨670330, by decide⟩ ⟨13, 2, 0, 670330, 355464, 1549, 16384⟩
    (by decide) selected_cut_26490

theorem selected_cut_26491 : selected 8 ⟨670371, by decide⟩
    (prefixPartial 13 355465) = some ⟨13, 2, 0, 670371, 355465, 2413, 16384⟩ := by
  decide +kernel

theorem context_13_355465_670371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355465 ⟨670371, by decide⟩ :=
  accepted_of_selected 13 355465 ⟨670371, by decide⟩ ⟨13, 2, 0, 670371, 355465, 2413, 16384⟩
    (by decide) selected_cut_26491

theorem selected_cut_26492 : selected 8 ⟨670392, by decide⟩
    (prefixPartial 13 355466) = some ⟨13, 2, 0, 670392, 355466, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_355466_670392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355466 ⟨670392, by decide⟩ :=
  accepted_of_selected 13 355466 ⟨670392, by decide⟩ ⟨13, 2, 0, 670392, 355466, 1665, 16384⟩
    (by decide) selected_cut_26492

theorem selected_cut_26493 : selected 8 ⟨670397, by decide⟩
    (prefixPartial 13 355467) = some ⟨13, 2, 0, 670397, 355467, 709, 16384⟩ := by
  decide +kernel

theorem context_13_355467_670397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355467 ⟨670397, by decide⟩ :=
  accepted_of_selected 13 355467 ⟨670397, by decide⟩ ⟨13, 2, 0, 670397, 355467, 709, 16384⟩
    (by decide) selected_cut_26493

theorem unmarked_context_12_88866_670398 : frontier 9 ⟨670398, by decide⟩
    (prefixCache 12 88866) (prefixPartial 12 88866) = false := by
  decide +kernel

theorem node_context_12_88866_670398 : EJMOriginalGlobalDAGData.nodes 9 ⟨670398, by decide⟩ =
    .split (coordinate 12) (![⟨670330, by decide⟩,⟨670371, by decide⟩,⟨670392, by decide⟩,⟨670397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88866_670398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88866 ⟨670398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88866
    ⟨670398, by decide⟩ (by decide) (![⟨670330, by decide⟩,⟨670371, by decide⟩,⟨670392, by decide⟩,⟨670397, by decide⟩]) unmarked_context_12_88866_670398 node_context_12_88866_670398
  intro a
  fin_cases a
  · exact context_13_355464_670330
  · exact context_13_355465_670371
  · exact context_13_355466_670392
  · exact context_13_355467_670397

theorem selected_cut_26494 : selected 8 ⟨670413, by decide⟩
    (prefixPartial 13 355468) = some ⟨13, 2, 0, 670413, 355468, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_355468_670413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355468 ⟨670413, by decide⟩ :=
  accepted_of_selected 13 355468 ⟨670413, by decide⟩ ⟨13, 2, 0, 670413, 355468, 1257, 16384⟩
    (by decide) selected_cut_26494

theorem selected_cut_26495 : selected 8 ⟨670438, by decide⟩
    (prefixPartial 13 355469) = some ⟨13, 2, 0, 670438, 355469, 2077, 16384⟩ := by
  decide +kernel

theorem context_13_355469_670438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355469 ⟨670438, by decide⟩ :=
  accepted_of_selected 13 355469 ⟨670438, by decide⟩ ⟨13, 2, 0, 670438, 355469, 2077, 16384⟩
    (by decide) selected_cut_26495

theorem selected_cut_26496 : selected 8 ⟨670453, by decide⟩
    (prefixPartial 13 355470) = some ⟨13, 2, 0, 670453, 355470, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_355470_670453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355470 ⟨670453, by decide⟩ :=
  accepted_of_selected 13 355470 ⟨670453, by decide⟩ ⟨13, 2, 0, 670453, 355470, 1425, 16384⟩
    (by decide) selected_cut_26496

theorem selected_cut_26497 : selected 8 ⟨670457, by decide⟩
    (prefixPartial 13 355471) = some ⟨13, 2, 0, 670457, 355471, 661, 16384⟩ := by
  decide +kernel

theorem context_13_355471_670457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355471 ⟨670457, by decide⟩ :=
  accepted_of_selected 13 355471 ⟨670457, by decide⟩ ⟨13, 2, 0, 670457, 355471, 661, 16384⟩
    (by decide) selected_cut_26497

theorem unmarked_context_12_88867_670458 : frontier 9 ⟨670458, by decide⟩
    (prefixCache 12 88867) (prefixPartial 12 88867) = false := by
  decide +kernel

theorem node_context_12_88867_670458 : EJMOriginalGlobalDAGData.nodes 9 ⟨670458, by decide⟩ =
    .split (coordinate 12) (![⟨670413, by decide⟩,⟨670438, by decide⟩,⟨670453, by decide⟩,⟨670457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_88867_670458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 88867 ⟨670458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 88867
    ⟨670458, by decide⟩ (by decide) (![⟨670413, by decide⟩,⟨670438, by decide⟩,⟨670453, by decide⟩,⟨670457, by decide⟩]) unmarked_context_12_88867_670458 node_context_12_88867_670458
  intro a
  fin_cases a
  · exact context_13_355468_670413
  · exact context_13_355469_670438
  · exact context_13_355470_670453
  · exact context_13_355471_670457

theorem unmarked_context_11_22216_670459 : frontier 10 ⟨670459, by decide⟩
    (prefixCache 11 22216) (prefixPartial 11 22216) = false := by
  decide +kernel

theorem node_context_11_22216_670459 : EJMOriginalGlobalDAGData.nodes 10 ⟨670459, by decide⟩ =
    .split (coordinate 11) (![⟨670242, by decide⟩,⟨670306, by decide⟩,⟨670398, by decide⟩,⟨670458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_22216_670459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 22216 ⟨670459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 22216
    ⟨670459, by decide⟩ (by decide) (![⟨670242, by decide⟩,⟨670306, by decide⟩,⟨670398, by decide⟩,⟨670458, by decide⟩]) unmarked_context_11_22216_670459 node_context_11_22216_670459
  intro a
  fin_cases a
  · exact context_12_88864_670242
  · exact context_12_88865_670306
  · exact context_12_88866_670398
  · exact context_12_88867_670458

theorem selected_cut_26498 : selected 8 ⟨670472, by decide⟩
    (prefixPartial 13 355472) = some ⟨13, 2, 0, 670472, 355472, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_355472_670472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 355472 ⟨670472, by decide⟩ :=
  accepted_of_selected 13 355472 ⟨670472, by decide⟩ ⟨13, 2, 0, 670472, 355472, 1145, 16384⟩
    (by decide) selected_cut_26498

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
