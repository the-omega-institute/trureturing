/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover405
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_38979 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 302373) = some ⟨12, 1, 0, 891951, 302373, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302373_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302373 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 302373 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 302373, 1, 65536⟩
    (by decide) selected_cut_38979

theorem selected_cut_38980 : selected 9 ⟨1055856, by decide⟩
    (prefixPartial 12 302374) = some ⟨12, 2, 0, 1055856, 302374, 3073, 65536⟩ := by
  decide +kernel

theorem context_12_302374_1055856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302374 ⟨1055856, by decide⟩ :=
  accepted_of_selected 12 302374 ⟨1055856, by decide⟩ ⟨12, 2, 0, 1055856, 302374, 3073, 65536⟩
    (by decide) selected_cut_38980

theorem selected_cut_38981 : selected 9 ⟨1055909, by decide⟩
    (prefixPartial 12 302375) = some ⟨12, 2, 0, 1055909, 302375, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_302375_1055909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302375 ⟨1055909, by decide⟩ :=
  accepted_of_selected 12 302375 ⟨1055909, by decide⟩ ⟨12, 2, 0, 1055909, 302375, 3341, 65536⟩
    (by decide) selected_cut_38981

theorem unmarked_context_11_75593_1055910 : frontier 10 ⟨1055910, by decide⟩
    (prefixCache 11 75593) (prefixPartial 11 75593) = false := by
  decide +kernel

theorem node_context_11_75593_1055910 : EJMOriginalGlobalDAGData.nodes 10 ⟨1055910, by decide⟩ =
    .split (coordinate 11) (![⟨1055797, by decide⟩,⟨891951, by decide⟩,⟨1055856, by decide⟩,⟨1055909, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75593_1055910 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75593 ⟨1055910, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75593
    ⟨1055910, by decide⟩ (by decide) (![⟨1055797, by decide⟩,⟨891951, by decide⟩,⟨1055856, by decide⟩,⟨1055909, by decide⟩]) unmarked_context_11_75593_1055910 node_context_11_75593_1055910
  intro a
  fin_cases a
  · exact context_12_302372_1055797
  · exact context_12_302373_891951
  · exact context_12_302374_1055856
  · exact context_12_302375_1055909

theorem selected_cut_38982 : selected 9 ⟨1055959, by decide⟩
    (prefixPartial 12 302376) = some ⟨12, 2, 0, 1055959, 302376, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_302376_1055959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302376 ⟨1055959, by decide⟩ :=
  accepted_of_selected 12 302376 ⟨1055959, by decide⟩ ⟨12, 2, 0, 1055959, 302376, 2961, 65536⟩
    (by decide) selected_cut_38982

theorem selected_cut_38983 : selected 9 ⟨1056012, by decide⟩
    (prefixPartial 12 302377) = some ⟨12, 2, 0, 1056012, 302377, 3265, 65536⟩ := by
  decide +kernel

theorem context_12_302377_1056012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302377 ⟨1056012, by decide⟩ :=
  accepted_of_selected 12 302377 ⟨1056012, by decide⟩ ⟨12, 2, 0, 1056012, 302377, 3265, 65536⟩
    (by decide) selected_cut_38983

theorem selected_cut_38984 : selected 9 ⟨1056058, by decide⟩
    (prefixPartial 12 302378) = some ⟨12, 2, 0, 1056058, 302378, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_302378_1056058 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302378 ⟨1056058, by decide⟩ :=
  accepted_of_selected 12 302378 ⟨1056058, by decide⟩ ⟨12, 2, 0, 1056058, 302378, 2825, 65536⟩
    (by decide) selected_cut_38984

theorem selected_cut_38985 : selected 9 ⟨1056109, by decide⟩
    (prefixPartial 12 302379) = some ⟨12, 2, 0, 1056109, 302379, 3149, 65536⟩ := by
  decide +kernel

theorem context_12_302379_1056109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302379 ⟨1056109, by decide⟩ :=
  accepted_of_selected 12 302379 ⟨1056109, by decide⟩ ⟨12, 2, 0, 1056109, 302379, 3149, 65536⟩
    (by decide) selected_cut_38985

theorem unmarked_context_11_75594_1056110 : frontier 10 ⟨1056110, by decide⟩
    (prefixCache 11 75594) (prefixPartial 11 75594) = false := by
  decide +kernel

theorem node_context_11_75594_1056110 : EJMOriginalGlobalDAGData.nodes 10 ⟨1056110, by decide⟩ =
    .split (coordinate 11) (![⟨1055959, by decide⟩,⟨1056012, by decide⟩,⟨1056058, by decide⟩,⟨1056109, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75594_1056110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75594 ⟨1056110, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75594
    ⟨1056110, by decide⟩ (by decide) (![⟨1055959, by decide⟩,⟨1056012, by decide⟩,⟨1056058, by decide⟩,⟨1056109, by decide⟩]) unmarked_context_11_75594_1056110 node_context_11_75594_1056110
  intro a
  fin_cases a
  · exact context_12_302376_1055959
  · exact context_12_302377_1056012
  · exact context_12_302378_1056058
  · exact context_12_302379_1056109

theorem selected_cut_38986 : selected 9 ⟨1056146, by decide⟩
    (prefixPartial 12 302380) = some ⟨12, 2, 0, 1056146, 302380, 2589, 65536⟩ := by
  decide +kernel

theorem context_12_302380_1056146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302380 ⟨1056146, by decide⟩ :=
  accepted_of_selected 12 302380 ⟨1056146, by decide⟩ ⟨12, 2, 0, 1056146, 302380, 2589, 65536⟩
    (by decide) selected_cut_38986

theorem selected_cut_38987 : selected 9 ⟨1056197, by decide⟩
    (prefixPartial 12 302381) = some ⟨12, 2, 0, 1056197, 302381, 3041, 65536⟩ := by
  decide +kernel

theorem context_12_302381_1056197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302381 ⟨1056197, by decide⟩ :=
  accepted_of_selected 12 302381 ⟨1056197, by decide⟩ ⟨12, 2, 0, 1056197, 302381, 3041, 65536⟩
    (by decide) selected_cut_38987

theorem selected_cut_38988 : selected 9 ⟨1056229, by decide⟩
    (prefixPartial 12 302382) = some ⟨12, 2, 0, 1056229, 302382, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_302382_1056229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302382 ⟨1056229, by decide⟩ :=
  accepted_of_selected 12 302382 ⟨1056229, by decide⟩ ⟨12, 2, 0, 1056229, 302382, 2569, 65536⟩
    (by decide) selected_cut_38988

theorem selected_cut_38989 : selected 9 ⟨1056278, by decide⟩
    (prefixPartial 12 302383) = some ⟨12, 2, 0, 1056278, 302383, 3069, 65536⟩ := by
  decide +kernel

theorem context_12_302383_1056278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302383 ⟨1056278, by decide⟩ :=
  accepted_of_selected 12 302383 ⟨1056278, by decide⟩ ⟨12, 2, 0, 1056278, 302383, 3069, 65536⟩
    (by decide) selected_cut_38989

theorem unmarked_context_11_75595_1056279 : frontier 10 ⟨1056279, by decide⟩
    (prefixCache 11 75595) (prefixPartial 11 75595) = false := by
  decide +kernel

theorem node_context_11_75595_1056279 : EJMOriginalGlobalDAGData.nodes 10 ⟨1056279, by decide⟩ =
    .split (coordinate 11) (![⟨1056146, by decide⟩,⟨1056197, by decide⟩,⟨1056229, by decide⟩,⟨1056278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75595_1056279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75595 ⟨1056279, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75595
    ⟨1056279, by decide⟩ (by decide) (![⟨1056146, by decide⟩,⟨1056197, by decide⟩,⟨1056229, by decide⟩,⟨1056278, by decide⟩]) unmarked_context_11_75595_1056279 node_context_11_75595_1056279
  intro a
  fin_cases a
  · exact context_12_302380_1056146
  · exact context_12_302381_1056197
  · exact context_12_302382_1056229
  · exact context_12_302383_1056278

theorem unmarked_context_10_18898_1056280 : frontier 11 ⟨1056280, by decide⟩
    (prefixCache 10 18898) (prefixPartial 10 18898) = false := by
  decide +kernel

theorem node_context_10_18898_1056280 : EJMOriginalGlobalDAGData.nodes 11 ⟨1056280, by decide⟩ =
    .split (coordinate 10) (![⟨1055746, by decide⟩,⟨1055910, by decide⟩,⟨1056110, by decide⟩,⟨1056279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18898_1056280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18898 ⟨1056280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18898
    ⟨1056280, by decide⟩ (by decide) (![⟨1055746, by decide⟩,⟨1055910, by decide⟩,⟨1056110, by decide⟩,⟨1056279, by decide⟩]) unmarked_context_10_18898_1056280 node_context_10_18898_1056280
  intro a
  fin_cases a
  · exact context_11_75592_1055746
  · exact context_11_75593_1055910
  · exact context_11_75594_1056110
  · exact context_11_75595_1056279

theorem selected_cut_38990 : selected 9 ⟨1056325, by decide⟩
    (prefixPartial 12 302384) = some ⟨12, 2, 0, 1056325, 302384, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_302384_1056325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302384 ⟨1056325, by decide⟩ :=
  accepted_of_selected 12 302384 ⟨1056325, by decide⟩ ⟨12, 2, 0, 1056325, 302384, 2425, 65536⟩
    (by decide) selected_cut_38990

theorem selected_cut_38991 : selected 9 ⟨1056376, by decide⟩
    (prefixPartial 12 302385) = some ⟨12, 2, 0, 1056376, 302385, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_302385_1056376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302385 ⟨1056376, by decide⟩ :=
  accepted_of_selected 12 302385 ⟨1056376, by decide⟩ ⟨12, 2, 0, 1056376, 302385, 2689, 65536⟩
    (by decide) selected_cut_38991

theorem selected_cut_38992 : selected 9 ⟨1056404, by decide⟩
    (prefixPartial 12 302386) = some ⟨12, 2, 0, 1056404, 302386, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_302386_1056404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302386 ⟨1056404, by decide⟩ :=
  accepted_of_selected 12 302386 ⟨1056404, by decide⟩ ⟨12, 2, 0, 1056404, 302386, 2161, 65536⟩
    (by decide) selected_cut_38992

theorem selected_cut_38993 : selected 9 ⟨1056444, by decide⟩
    (prefixPartial 12 302387) = some ⟨12, 2, 0, 1056444, 302387, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_302387_1056444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302387 ⟨1056444, by decide⟩ :=
  accepted_of_selected 12 302387 ⟨1056444, by decide⟩ ⟨12, 2, 0, 1056444, 302387, 2457, 65536⟩
    (by decide) selected_cut_38993

theorem unmarked_context_11_75596_1056445 : frontier 10 ⟨1056445, by decide⟩
    (prefixCache 11 75596) (prefixPartial 11 75596) = false := by
  decide +kernel

theorem node_context_11_75596_1056445 : EJMOriginalGlobalDAGData.nodes 10 ⟨1056445, by decide⟩ =
    .split (coordinate 11) (![⟨1056325, by decide⟩,⟨1056376, by decide⟩,⟨1056404, by decide⟩,⟨1056444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75596_1056445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75596 ⟨1056445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75596
    ⟨1056445, by decide⟩ (by decide) (![⟨1056325, by decide⟩,⟨1056376, by decide⟩,⟨1056404, by decide⟩,⟨1056444, by decide⟩]) unmarked_context_11_75596_1056445 node_context_11_75596_1056445
  intro a
  fin_cases a
  · exact context_12_302384_1056325
  · exact context_12_302385_1056376
  · exact context_12_302386_1056404
  · exact context_12_302387_1056444

theorem selected_cut_38994 : selected 9 ⟨1056492, by decide⟩
    (prefixPartial 12 302388) = some ⟨12, 2, 0, 1056492, 302388, 2741, 65536⟩ := by
  decide +kernel

theorem context_12_302388_1056492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302388 ⟨1056492, by decide⟩ :=
  accepted_of_selected 12 302388 ⟨1056492, by decide⟩ ⟨12, 2, 0, 1056492, 302388, 2741, 65536⟩
    (by decide) selected_cut_38994

theorem selected_cut_38995 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 302389) = some ⟨12, 1, 0, 891951, 302389, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302389_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302389 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 302389 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 302389, 1, 65536⟩
    (by decide) selected_cut_38995

theorem selected_cut_38996 : selected 9 ⟨1056535, by decide⟩
    (prefixPartial 12 302390) = some ⟨12, 2, 0, 1056535, 302390, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_302390_1056535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302390 ⟨1056535, by decide⟩ :=
  accepted_of_selected 12 302390 ⟨1056535, by decide⟩ ⟨12, 2, 0, 1056535, 302390, 2605, 65536⟩
    (by decide) selected_cut_38996

theorem selected_cut_38997 : selected 9 ⟨1056581, by decide⟩
    (prefixPartial 12 302391) = some ⟨12, 2, 0, 1056581, 302391, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_302391_1056581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302391 ⟨1056581, by decide⟩ :=
  accepted_of_selected 12 302391 ⟨1056581, by decide⟩ ⟨12, 2, 0, 1056581, 302391, 2757, 65536⟩
    (by decide) selected_cut_38997

theorem unmarked_context_11_75597_1056582 : frontier 10 ⟨1056582, by decide⟩
    (prefixCache 11 75597) (prefixPartial 11 75597) = false := by
  decide +kernel

theorem node_context_11_75597_1056582 : EJMOriginalGlobalDAGData.nodes 10 ⟨1056582, by decide⟩ =
    .split (coordinate 11) (![⟨1056492, by decide⟩,⟨891951, by decide⟩,⟨1056535, by decide⟩,⟨1056581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75597_1056582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75597 ⟨1056582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75597
    ⟨1056582, by decide⟩ (by decide) (![⟨1056492, by decide⟩,⟨891951, by decide⟩,⟨1056535, by decide⟩,⟨1056581, by decide⟩]) unmarked_context_11_75597_1056582 node_context_11_75597_1056582
  intro a
  fin_cases a
  · exact context_12_302388_1056492
  · exact context_12_302389_891951
  · exact context_12_302390_1056535
  · exact context_12_302391_1056581

theorem selected_cut_38998 : selected 9 ⟨1056624, by decide⟩
    (prefixPartial 12 302392) = some ⟨12, 2, 0, 1056624, 302392, 2285, 65536⟩ := by
  decide +kernel

theorem context_12_302392_1056624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302392 ⟨1056624, by decide⟩ :=
  accepted_of_selected 12 302392 ⟨1056624, by decide⟩ ⟨12, 2, 0, 1056624, 302392, 2285, 65536⟩
    (by decide) selected_cut_38998

theorem selected_cut_38999 : selected 9 ⟨1056657, by decide⟩
    (prefixPartial 12 302393) = some ⟨12, 2, 0, 1056657, 302393, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_302393_1056657 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302393 ⟨1056657, by decide⟩ :=
  accepted_of_selected 12 302393 ⟨1056657, by decide⟩ ⟨12, 2, 0, 1056657, 302393, 2473, 65536⟩
    (by decide) selected_cut_38999

theorem selected_cut_39000 : selected 9 ⟨1056692, by decide⟩
    (prefixPartial 12 302394) = some ⟨12, 2, 0, 1056692, 302394, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_302394_1056692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302394 ⟨1056692, by decide⟩ :=
  accepted_of_selected 12 302394 ⟨1056692, by decide⟩ ⟨12, 2, 0, 1056692, 302394, 2301, 65536⟩
    (by decide) selected_cut_39000

theorem selected_cut_39001 : selected 9 ⟨1056720, by decide⟩
    (prefixPartial 12 302395) = some ⟨12, 2, 0, 1056720, 302395, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_302395_1056720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302395 ⟨1056720, by decide⟩ :=
  accepted_of_selected 12 302395 ⟨1056720, by decide⟩ ⟨12, 2, 0, 1056720, 302395, 2389, 65536⟩
    (by decide) selected_cut_39001

theorem unmarked_context_11_75598_1056721 : frontier 10 ⟨1056721, by decide⟩
    (prefixCache 11 75598) (prefixPartial 11 75598) = false := by
  decide +kernel

theorem node_context_11_75598_1056721 : EJMOriginalGlobalDAGData.nodes 10 ⟨1056721, by decide⟩ =
    .split (coordinate 11) (![⟨1056624, by decide⟩,⟨1056657, by decide⟩,⟨1056692, by decide⟩,⟨1056720, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75598_1056721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75598 ⟨1056721, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75598
    ⟨1056721, by decide⟩ (by decide) (![⟨1056624, by decide⟩,⟨1056657, by decide⟩,⟨1056692, by decide⟩,⟨1056720, by decide⟩]) unmarked_context_11_75598_1056721 node_context_11_75598_1056721
  intro a
  fin_cases a
  · exact context_12_302392_1056624
  · exact context_12_302393_1056657
  · exact context_12_302394_1056692
  · exact context_12_302395_1056720

theorem selected_cut_39002 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75599) = some ⟨11, 1, 0, 977886, 75599, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75599_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75599 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75599 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75599, 1, 262144⟩
    (by decide) selected_cut_39002

theorem unmarked_context_10_18899_1056722 : frontier 11 ⟨1056722, by decide⟩
    (prefixCache 10 18899) (prefixPartial 10 18899) = false := by
  decide +kernel

theorem node_context_10_18899_1056722 : EJMOriginalGlobalDAGData.nodes 11 ⟨1056722, by decide⟩ =
    .split (coordinate 10) (![⟨1056445, by decide⟩,⟨1056582, by decide⟩,⟨1056721, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18899_1056722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18899 ⟨1056722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18899
    ⟨1056722, by decide⟩ (by decide) (![⟨1056445, by decide⟩,⟨1056582, by decide⟩,⟨1056721, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18899_1056722 node_context_10_18899_1056722
  intro a
  fin_cases a
  · exact context_11_75596_1056445
  · exact context_11_75597_1056582
  · exact context_11_75598_1056721
  · exact context_11_75599_977886

theorem unmarked_context_9_4724_1056723 : frontier 12 ⟨1056723, by decide⟩
    (prefixCache 9 4724) (prefixPartial 9 4724) = false := by
  decide +kernel

theorem node_context_9_4724_1056723 : EJMOriginalGlobalDAGData.nodes 12 ⟨1056723, by decide⟩ =
    .split (coordinate 9) (![⟨1054972, by decide⟩,⟨1055594, by decide⟩,⟨1056280, by decide⟩,⟨1056722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4724_1056723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4724 ⟨1056723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4724
    ⟨1056723, by decide⟩ (by decide) (![⟨1054972, by decide⟩,⟨1055594, by decide⟩,⟨1056280, by decide⟩,⟨1056722, by decide⟩]) unmarked_context_9_4724_1056723 node_context_9_4724_1056723
  intro a
  fin_cases a
  · exact context_10_18896_1054972
  · exact context_10_18897_1055594
  · exact context_10_18898_1056280
  · exact context_10_18899_1056722

theorem selected_cut_39003 : selected 9 ⟨1056818, by decide⟩
    (prefixPartial 12 302400) = some ⟨12, 2, 0, 1056818, 302400, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_302400_1056818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302400 ⟨1056818, by decide⟩ :=
  accepted_of_selected 12 302400 ⟨1056818, by decide⟩ ⟨12, 2, 0, 1056818, 302400, 1305, 65536⟩
    (by decide) selected_cut_39003

theorem selected_cut_39004 : selected 9 ⟨1056851, by decide⟩
    (prefixPartial 12 302401) = some ⟨12, 2, 0, 1056851, 302401, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_302401_1056851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302401 ⟨1056851, by decide⟩ :=
  accepted_of_selected 12 302401 ⟨1056851, by decide⟩ ⟨12, 2, 0, 1056851, 302401, 2269, 65536⟩
    (by decide) selected_cut_39004

theorem selected_cut_39005 : selected 9 ⟨1056887, by decide⟩
    (prefixPartial 12 302402) = some ⟨12, 2, 0, 1056887, 302402, 2077, 65536⟩ := by
  decide +kernel

theorem context_12_302402_1056887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302402 ⟨1056887, by decide⟩ :=
  accepted_of_selected 12 302402 ⟨1056887, by decide⟩ ⟨12, 2, 0, 1056887, 302402, 2077, 65536⟩
    (by decide) selected_cut_39005

theorem selected_cut_39006 : selected 9 ⟨1056920, by decide⟩
    (prefixPartial 12 302403) = some ⟨12, 2, 0, 1056920, 302403, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_302403_1056920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302403 ⟨1056920, by decide⟩ :=
  accepted_of_selected 12 302403 ⟨1056920, by decide⟩ ⟨12, 2, 0, 1056920, 302403, 2181, 65536⟩
    (by decide) selected_cut_39006

theorem unmarked_context_11_75600_1056921 : frontier 10 ⟨1056921, by decide⟩
    (prefixCache 11 75600) (prefixPartial 11 75600) = false := by
  decide +kernel

theorem node_context_11_75600_1056921 : EJMOriginalGlobalDAGData.nodes 10 ⟨1056921, by decide⟩ =
    .split (coordinate 11) (![⟨1056818, by decide⟩,⟨1056851, by decide⟩,⟨1056887, by decide⟩,⟨1056920, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75600_1056921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75600 ⟨1056921, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75600
    ⟨1056921, by decide⟩ (by decide) (![⟨1056818, by decide⟩,⟨1056851, by decide⟩,⟨1056887, by decide⟩,⟨1056920, by decide⟩]) unmarked_context_11_75600_1056921 node_context_11_75600_1056921
  intro a
  fin_cases a
  · exact context_12_302400_1056818
  · exact context_12_302401_1056851
  · exact context_12_302402_1056887
  · exact context_12_302403_1056920

theorem selected_cut_39007 : selected 9 ⟨1056985, by decide⟩
    (prefixPartial 12 302404) = some ⟨12, 2, 0, 1056985, 302404, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_302404_1056985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302404 ⟨1056985, by decide⟩ :=
  accepted_of_selected 12 302404 ⟨1056985, by decide⟩ ⟨12, 2, 0, 1056985, 302404, 2909, 65536⟩
    (by decide) selected_cut_39007

theorem selected_cut_39008 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 302405) = some ⟨12, 1, 0, 891951, 302405, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302405_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302405 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 302405 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 302405, 1, 65536⟩
    (by decide) selected_cut_39008

theorem selected_cut_39009 : selected 9 ⟨1057025, by decide⟩
    (prefixPartial 12 302406) = some ⟨12, 2, 0, 1057025, 302406, 2441, 65536⟩ := by
  decide +kernel

theorem context_12_302406_1057025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302406 ⟨1057025, by decide⟩ :=
  accepted_of_selected 12 302406 ⟨1057025, by decide⟩ ⟨12, 2, 0, 1057025, 302406, 2441, 65536⟩
    (by decide) selected_cut_39009

theorem selected_cut_39010 : selected 9 ⟨1057061, by decide⟩
    (prefixPartial 12 302407) = some ⟨12, 2, 0, 1057061, 302407, 2341, 65536⟩ := by
  decide +kernel

theorem context_12_302407_1057061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302407 ⟨1057061, by decide⟩ :=
  accepted_of_selected 12 302407 ⟨1057061, by decide⟩ ⟨12, 2, 0, 1057061, 302407, 2341, 65536⟩
    (by decide) selected_cut_39010

theorem unmarked_context_11_75601_1057062 : frontier 10 ⟨1057062, by decide⟩
    (prefixCache 11 75601) (prefixPartial 11 75601) = false := by
  decide +kernel

theorem node_context_11_75601_1057062 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057062, by decide⟩ =
    .split (coordinate 11) (![⟨1056985, by decide⟩,⟨891951, by decide⟩,⟨1057025, by decide⟩,⟨1057061, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75601_1057062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75601 ⟨1057062, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75601
    ⟨1057062, by decide⟩ (by decide) (![⟨1056985, by decide⟩,⟨891951, by decide⟩,⟨1057025, by decide⟩,⟨1057061, by decide⟩]) unmarked_context_11_75601_1057062 node_context_11_75601_1057062
  intro a
  fin_cases a
  · exact context_12_302404_1056985
  · exact context_12_302405_891951
  · exact context_12_302406_1057025
  · exact context_12_302407_1057061

theorem selected_cut_39011 : selected 9 ⟨1057105, by decide⟩
    (prefixPartial 12 302408) = some ⟨12, 2, 0, 1057105, 302408, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_302408_1057105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302408 ⟨1057105, by decide⟩ :=
  accepted_of_selected 12 302408 ⟨1057105, by decide⟩ ⟨12, 2, 0, 1057105, 302408, 2717, 65536⟩
    (by decide) selected_cut_39011

theorem selected_cut_39012 : selected 9 ⟨1057151, by decide⟩
    (prefixPartial 12 302409) = some ⟨12, 2, 0, 1057151, 302409, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_302409_1057151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302409 ⟨1057151, by decide⟩ :=
  accepted_of_selected 12 302409 ⟨1057151, by decide⟩ ⟨12, 2, 0, 1057151, 302409, 2569, 65536⟩
    (by decide) selected_cut_39012

theorem selected_cut_39013 : selected 9 ⟨1057189, by decide⟩
    (prefixPartial 12 302410) = some ⟨12, 2, 0, 1057189, 302410, 2605, 65536⟩ := by
  decide +kernel

theorem context_12_302410_1057189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302410 ⟨1057189, by decide⟩ :=
  accepted_of_selected 12 302410 ⟨1057189, by decide⟩ ⟨12, 2, 0, 1057189, 302410, 2605, 65536⟩
    (by decide) selected_cut_39013

theorem selected_cut_39014 : selected 9 ⟨1057223, by decide⟩
    (prefixPartial 12 302411) = some ⟨12, 2, 0, 1057223, 302411, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_302411_1057223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302411 ⟨1057223, by decide⟩ :=
  accepted_of_selected 12 302411 ⟨1057223, by decide⟩ ⟨12, 2, 0, 1057223, 302411, 2425, 65536⟩
    (by decide) selected_cut_39014

theorem unmarked_context_11_75602_1057224 : frontier 10 ⟨1057224, by decide⟩
    (prefixCache 11 75602) (prefixPartial 11 75602) = false := by
  decide +kernel

theorem node_context_11_75602_1057224 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057224, by decide⟩ =
    .split (coordinate 11) (![⟨1057105, by decide⟩,⟨1057151, by decide⟩,⟨1057189, by decide⟩,⟨1057223, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75602_1057224 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75602 ⟨1057224, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75602
    ⟨1057224, by decide⟩ (by decide) (![⟨1057105, by decide⟩,⟨1057151, by decide⟩,⟨1057189, by decide⟩,⟨1057223, by decide⟩]) unmarked_context_11_75602_1057224 node_context_11_75602_1057224
  intro a
  fin_cases a
  · exact context_12_302408_1057105
  · exact context_12_302409_1057151
  · exact context_12_302410_1057189
  · exact context_12_302411_1057223

theorem selected_cut_39015 : selected 9 ⟨1057267, by decide⟩
    (prefixPartial 12 302412) = some ⟨12, 2, 0, 1057267, 302412, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_302412_1057267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302412 ⟨1057267, by decide⟩ :=
  accepted_of_selected 12 302412 ⟨1057267, by decide⟩ ⟨12, 2, 0, 1057267, 302412, 2445, 65536⟩
    (by decide) selected_cut_39015

theorem selected_cut_39016 : selected 9 ⟨1057309, by decide⟩
    (prefixPartial 12 302413) = some ⟨12, 2, 0, 1057309, 302413, 2313, 65536⟩ := by
  decide +kernel

theorem context_12_302413_1057309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302413 ⟨1057309, by decide⟩ :=
  accepted_of_selected 12 302413 ⟨1057309, by decide⟩ ⟨12, 2, 0, 1057309, 302413, 2313, 65536⟩
    (by decide) selected_cut_39016

theorem selected_cut_39017 : selected 9 ⟨1057338, by decide⟩
    (prefixPartial 12 302414) = some ⟨12, 2, 0, 1057338, 302414, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_302414_1057338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302414 ⟨1057338, by decide⟩ :=
  accepted_of_selected 12 302414 ⟨1057338, by decide⟩ ⟨12, 2, 0, 1057338, 302414, 2109, 65536⟩
    (by decide) selected_cut_39017

theorem selected_cut_39018 : selected 9 ⟨1057371, by decide⟩
    (prefixPartial 12 302415) = some ⟨12, 2, 0, 1057371, 302415, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_302415_1057371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302415 ⟨1057371, by decide⟩ :=
  accepted_of_selected 12 302415 ⟨1057371, by decide⟩ ⟨12, 2, 0, 1057371, 302415, 2309, 65536⟩
    (by decide) selected_cut_39018

theorem unmarked_context_11_75603_1057372 : frontier 10 ⟨1057372, by decide⟩
    (prefixCache 11 75603) (prefixPartial 11 75603) = false := by
  decide +kernel

theorem node_context_11_75603_1057372 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057372, by decide⟩ =
    .split (coordinate 11) (![⟨1057267, by decide⟩,⟨1057309, by decide⟩,⟨1057338, by decide⟩,⟨1057371, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75603_1057372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75603 ⟨1057372, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75603
    ⟨1057372, by decide⟩ (by decide) (![⟨1057267, by decide⟩,⟨1057309, by decide⟩,⟨1057338, by decide⟩,⟨1057371, by decide⟩]) unmarked_context_11_75603_1057372 node_context_11_75603_1057372
  intro a
  fin_cases a
  · exact context_12_302412_1057267
  · exact context_12_302413_1057309
  · exact context_12_302414_1057338
  · exact context_12_302415_1057371

theorem unmarked_context_10_18900_1057373 : frontier 11 ⟨1057373, by decide⟩
    (prefixCache 10 18900) (prefixPartial 10 18900) = false := by
  decide +kernel

theorem node_context_10_18900_1057373 : EJMOriginalGlobalDAGData.nodes 11 ⟨1057373, by decide⟩ =
    .split (coordinate 10) (![⟨1056921, by decide⟩,⟨1057062, by decide⟩,⟨1057224, by decide⟩,⟨1057372, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18900_1057373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18900 ⟨1057373, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18900
    ⟨1057373, by decide⟩ (by decide) (![⟨1056921, by decide⟩,⟨1057062, by decide⟩,⟨1057224, by decide⟩,⟨1057372, by decide⟩]) unmarked_context_10_18900_1057373 node_context_10_18900_1057373
  intro a
  fin_cases a
  · exact context_11_75600_1056921
  · exact context_11_75601_1057062
  · exact context_11_75602_1057224
  · exact context_11_75603_1057372

theorem selected_cut_39019 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 18901) = some ⟨10, 1, 0, 893098, 18901, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_18901_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18901 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 18901 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 18901, 1, 1048576⟩
    (by decide) selected_cut_39019

theorem selected_cut_39020 : selected 9 ⟨1057398, by decide⟩
    (prefixPartial 12 302432) = some ⟨12, 2, 0, 1057398, 302432, 2029, 65536⟩ := by
  decide +kernel

theorem context_12_302432_1057398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302432 ⟨1057398, by decide⟩ :=
  accepted_of_selected 12 302432 ⟨1057398, by decide⟩ ⟨12, 2, 0, 1057398, 302432, 2029, 65536⟩
    (by decide) selected_cut_39020

theorem selected_cut_39021 : selected 9 ⟨1057436, by decide⟩
    (prefixPartial 12 302433) = some ⟨12, 2, 0, 1057436, 302433, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_302433_1057436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302433 ⟨1057436, by decide⟩ :=
  accepted_of_selected 12 302433 ⟨1057436, by decide⟩ ⟨12, 2, 0, 1057436, 302433, 2245, 65536⟩
    (by decide) selected_cut_39021

theorem selected_cut_39022 : selected 9 ⟨1057470, by decide⟩
    (prefixPartial 12 302434) = some ⟨12, 2, 0, 1057470, 302434, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_302434_1057470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302434 ⟨1057470, by decide⟩ :=
  accepted_of_selected 12 302434 ⟨1057470, by decide⟩ ⟨12, 2, 0, 1057470, 302434, 1757, 65536⟩
    (by decide) selected_cut_39022

theorem selected_cut_39023 : selected 9 ⟨1057495, by decide⟩
    (prefixPartial 12 302435) = some ⟨12, 2, 0, 1057495, 302435, 1905, 65536⟩ := by
  decide +kernel

theorem context_12_302435_1057495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302435 ⟨1057495, by decide⟩ :=
  accepted_of_selected 12 302435 ⟨1057495, by decide⟩ ⟨12, 2, 0, 1057495, 302435, 1905, 65536⟩
    (by decide) selected_cut_39023

theorem unmarked_context_11_75608_1057496 : frontier 10 ⟨1057496, by decide⟩
    (prefixCache 11 75608) (prefixPartial 11 75608) = false := by
  decide +kernel

theorem node_context_11_75608_1057496 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057496, by decide⟩ =
    .split (coordinate 11) (![⟨1057398, by decide⟩,⟨1057436, by decide⟩,⟨1057470, by decide⟩,⟨1057495, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75608_1057496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75608 ⟨1057496, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75608
    ⟨1057496, by decide⟩ (by decide) (![⟨1057398, by decide⟩,⟨1057436, by decide⟩,⟨1057470, by decide⟩,⟨1057495, by decide⟩]) unmarked_context_11_75608_1057496 node_context_11_75608_1057496
  intro a
  fin_cases a
  · exact context_12_302432_1057398
  · exact context_12_302433_1057436
  · exact context_12_302434_1057470
  · exact context_12_302435_1057495

theorem selected_cut_39024 : selected 9 ⟨1057530, by decide⟩
    (prefixPartial 12 302436) = some ⟨12, 2, 0, 1057530, 302436, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_302436_1057530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302436 ⟨1057530, by decide⟩ :=
  accepted_of_selected 12 302436 ⟨1057530, by decide⟩ ⟨12, 2, 0, 1057530, 302436, 2181, 65536⟩
    (by decide) selected_cut_39024

theorem selected_cut_39025 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 302437) = some ⟨12, 1, 0, 891951, 302437, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302437_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302437 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 302437 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 302437, 1, 65536⟩
    (by decide) selected_cut_39025

theorem selected_cut_39026 : selected 9 ⟨1057556, by decide⟩
    (prefixPartial 12 302438) = some ⟨12, 2, 0, 1057556, 302438, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_302438_1057556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302438 ⟨1057556, by decide⟩ :=
  accepted_of_selected 12 302438 ⟨1057556, by decide⟩ ⟨12, 2, 0, 1057556, 302438, 1873, 65536⟩
    (by decide) selected_cut_39026

theorem selected_cut_39027 : selected 9 ⟨1057585, by decide⟩
    (prefixPartial 12 302439) = some ⟨12, 2, 0, 1057585, 302439, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_302439_1057585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302439 ⟨1057585, by decide⟩ :=
  accepted_of_selected 12 302439 ⟨1057585, by decide⟩ ⟨12, 2, 0, 1057585, 302439, 1977, 65536⟩
    (by decide) selected_cut_39027

theorem unmarked_context_11_75609_1057586 : frontier 10 ⟨1057586, by decide⟩
    (prefixCache 11 75609) (prefixPartial 11 75609) = false := by
  decide +kernel

theorem node_context_11_75609_1057586 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057586, by decide⟩ =
    .split (coordinate 11) (![⟨1057530, by decide⟩,⟨891951, by decide⟩,⟨1057556, by decide⟩,⟨1057585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75609_1057586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75609 ⟨1057586, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75609
    ⟨1057586, by decide⟩ (by decide) (![⟨1057530, by decide⟩,⟨891951, by decide⟩,⟨1057556, by decide⟩,⟨1057585, by decide⟩]) unmarked_context_11_75609_1057586 node_context_11_75609_1057586
  intro a
  fin_cases a
  · exact context_12_302436_1057530
  · exact context_12_302437_891951
  · exact context_12_302438_1057556
  · exact context_12_302439_1057585

theorem selected_cut_39028 : selected 9 ⟨1057616, by decide⟩
    (prefixPartial 12 302440) = some ⟨12, 2, 0, 1057616, 302440, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_302440_1057616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302440 ⟨1057616, by decide⟩ :=
  accepted_of_selected 12 302440 ⟨1057616, by decide⟩ ⟨12, 2, 0, 1057616, 302440, 2097, 65536⟩
    (by decide) selected_cut_39028

theorem selected_cut_39029 : selected 9 ⟨1057651, by decide⟩
    (prefixPartial 12 302441) = some ⟨12, 2, 0, 1057651, 302441, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_302441_1057651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302441 ⟨1057651, by decide⟩ :=
  accepted_of_selected 12 302441 ⟨1057651, by decide⟩ ⟨12, 2, 0, 1057651, 302441, 2189, 65536⟩
    (by decide) selected_cut_39029

theorem selected_cut_39030 : selected 9 ⟨811630, by decide⟩
    (prefixPartial 12 302442) = some ⟨12, 1, 0, 811630, 302442, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302442_811630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302442 ⟨811630, by decide⟩ :=
  accepted_of_selected 12 302442 ⟨811630, by decide⟩ ⟨12, 1, 0, 811630, 302442, 1, 65536⟩
    (by decide) selected_cut_39030

theorem selected_cut_39031 : selected 9 ⟨1057682, by decide⟩
    (prefixPartial 12 302443) = some ⟨12, 2, 0, 1057682, 302443, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_302443_1057682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302443 ⟨1057682, by decide⟩ :=
  accepted_of_selected 12 302443 ⟨1057682, by decide⟩ ⟨12, 2, 0, 1057682, 302443, 2081, 65536⟩
    (by decide) selected_cut_39031

theorem unmarked_context_11_75610_1057683 : frontier 10 ⟨1057683, by decide⟩
    (prefixCache 11 75610) (prefixPartial 11 75610) = false := by
  decide +kernel

theorem node_context_11_75610_1057683 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057683, by decide⟩ =
    .split (coordinate 11) (![⟨1057616, by decide⟩,⟨1057651, by decide⟩,⟨811630, by decide⟩,⟨1057682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75610_1057683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75610 ⟨1057683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75610
    ⟨1057683, by decide⟩ (by decide) (![⟨1057616, by decide⟩,⟨1057651, by decide⟩,⟨811630, by decide⟩,⟨1057682, by decide⟩]) unmarked_context_11_75610_1057683 node_context_11_75610_1057683
  intro a
  fin_cases a
  · exact context_12_302440_1057616
  · exact context_12_302441_1057651
  · exact context_12_302442_811630
  · exact context_12_302443_1057682

theorem selected_cut_39032 : selected 9 ⟨1057708, by decide⟩
    (prefixPartial 12 302444) = some ⟨12, 2, 0, 1057708, 302444, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_302444_1057708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302444 ⟨1057708, by decide⟩ :=
  accepted_of_selected 12 302444 ⟨1057708, by decide⟩ ⟨12, 2, 0, 1057708, 302444, 1813, 65536⟩
    (by decide) selected_cut_39032

theorem selected_cut_39033 : selected 9 ⟨1057735, by decide⟩
    (prefixPartial 12 302445) = some ⟨12, 2, 0, 1057735, 302445, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_302445_1057735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302445 ⟨1057735, by decide⟩ :=
  accepted_of_selected 12 302445 ⟨1057735, by decide⟩ ⟨12, 2, 0, 1057735, 302445, 1933, 65536⟩
    (by decide) selected_cut_39033

theorem selected_cut_39034 : selected 9 ⟨1057759, by decide⟩
    (prefixPartial 12 302446) = some ⟨12, 2, 0, 1057759, 302446, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_302446_1057759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302446 ⟨1057759, by decide⟩ :=
  accepted_of_selected 12 302446 ⟨1057759, by decide⟩ ⟨12, 2, 0, 1057759, 302446, 1621, 65536⟩
    (by decide) selected_cut_39034

theorem selected_cut_39035 : selected 9 ⟨1057789, by decide⟩
    (prefixPartial 12 302447) = some ⟨12, 2, 0, 1057789, 302447, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_302447_1057789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302447 ⟨1057789, by decide⟩ :=
  accepted_of_selected 12 302447 ⟨1057789, by decide⟩ ⟨12, 2, 0, 1057789, 302447, 1957, 65536⟩
    (by decide) selected_cut_39035

theorem unmarked_context_11_75611_1057790 : frontier 10 ⟨1057790, by decide⟩
    (prefixCache 11 75611) (prefixPartial 11 75611) = false := by
  decide +kernel

theorem node_context_11_75611_1057790 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057790, by decide⟩ =
    .split (coordinate 11) (![⟨1057708, by decide⟩,⟨1057735, by decide⟩,⟨1057759, by decide⟩,⟨1057789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75611_1057790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75611 ⟨1057790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75611
    ⟨1057790, by decide⟩ (by decide) (![⟨1057708, by decide⟩,⟨1057735, by decide⟩,⟨1057759, by decide⟩,⟨1057789, by decide⟩]) unmarked_context_11_75611_1057790 node_context_11_75611_1057790
  intro a
  fin_cases a
  · exact context_12_302444_1057708
  · exact context_12_302445_1057735
  · exact context_12_302446_1057759
  · exact context_12_302447_1057789

theorem unmarked_context_10_18902_1057791 : frontier 11 ⟨1057791, by decide⟩
    (prefixCache 10 18902) (prefixPartial 10 18902) = false := by
  decide +kernel

theorem node_context_10_18902_1057791 : EJMOriginalGlobalDAGData.nodes 11 ⟨1057791, by decide⟩ =
    .split (coordinate 10) (![⟨1057496, by decide⟩,⟨1057586, by decide⟩,⟨1057683, by decide⟩,⟨1057790, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18902_1057791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18902 ⟨1057791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18902
    ⟨1057791, by decide⟩ (by decide) (![⟨1057496, by decide⟩,⟨1057586, by decide⟩,⟨1057683, by decide⟩,⟨1057790, by decide⟩]) unmarked_context_10_18902_1057791 node_context_10_18902_1057791
  intro a
  fin_cases a
  · exact context_11_75608_1057496
  · exact context_11_75609_1057586
  · exact context_11_75610_1057683
  · exact context_11_75611_1057790

theorem selected_cut_39036 : selected 9 ⟨1057812, by decide⟩
    (prefixPartial 12 302448) = some ⟨12, 2, 0, 1057812, 302448, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_302448_1057812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302448 ⟨1057812, by decide⟩ :=
  accepted_of_selected 12 302448 ⟨1057812, by decide⟩ ⟨12, 2, 0, 1057812, 302448, 1517, 65536⟩
    (by decide) selected_cut_39036

theorem selected_cut_39037 : selected 9 ⟨1057834, by decide⟩
    (prefixPartial 12 302449) = some ⟨12, 2, 0, 1057834, 302449, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_302449_1057834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302449 ⟨1057834, by decide⟩ :=
  accepted_of_selected 12 302449 ⟨1057834, by decide⟩ ⟨12, 2, 0, 1057834, 302449, 1629, 65536⟩
    (by decide) selected_cut_39037

theorem selected_cut_39038 : selected 9 ⟨1057850, by decide⟩
    (prefixPartial 12 302450) = some ⟨12, 2, 0, 1057850, 302450, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_302450_1057850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302450 ⟨1057850, by decide⟩ :=
  accepted_of_selected 12 302450 ⟨1057850, by decide⟩ ⟨12, 2, 0, 1057850, 302450, 1365, 65536⟩
    (by decide) selected_cut_39038

theorem selected_cut_39039 : selected 9 ⟨1057866, by decide⟩
    (prefixPartial 12 302451) = some ⟨12, 2, 0, 1057866, 302451, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_302451_1057866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302451 ⟨1057866, by decide⟩ :=
  accepted_of_selected 12 302451 ⟨1057866, by decide⟩ ⟨12, 2, 0, 1057866, 302451, 1381, 65536⟩
    (by decide) selected_cut_39039

theorem unmarked_context_11_75612_1057867 : frontier 10 ⟨1057867, by decide⟩
    (prefixCache 11 75612) (prefixPartial 11 75612) = false := by
  decide +kernel

theorem node_context_11_75612_1057867 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057867, by decide⟩ =
    .split (coordinate 11) (![⟨1057812, by decide⟩,⟨1057834, by decide⟩,⟨1057850, by decide⟩,⟨1057866, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75612_1057867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75612 ⟨1057867, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75612
    ⟨1057867, by decide⟩ (by decide) (![⟨1057812, by decide⟩,⟨1057834, by decide⟩,⟨1057850, by decide⟩,⟨1057866, by decide⟩]) unmarked_context_11_75612_1057867 node_context_11_75612_1057867
  intro a
  fin_cases a
  · exact context_12_302448_1057812
  · exact context_12_302449_1057834
  · exact context_12_302450_1057850
  · exact context_12_302451_1057866

theorem selected_cut_39040 : selected 9 ⟨1057911, by decide⟩
    (prefixPartial 12 302452) = some ⟨12, 2, 0, 1057911, 302452, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_302452_1057911 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302452 ⟨1057911, by decide⟩ :=
  accepted_of_selected 12 302452 ⟨1057911, by decide⟩ ⟨12, 2, 0, 1057911, 302452, 1785, 65536⟩
    (by decide) selected_cut_39040

theorem selected_cut_39041 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 302453) = some ⟨12, 1, 0, 891951, 302453, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302453_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302453 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 302453 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 302453, 1, 65536⟩
    (by decide) selected_cut_39041

theorem selected_cut_39042 : selected 9 ⟨1057933, by decide⟩
    (prefixPartial 12 302454) = some ⟨12, 2, 0, 1057933, 302454, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_302454_1057933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302454 ⟨1057933, by decide⟩ :=
  accepted_of_selected 12 302454 ⟨1057933, by decide⟩ ⟨12, 2, 0, 1057933, 302454, 1545, 65536⟩
    (by decide) selected_cut_39042

theorem selected_cut_39043 : selected 9 ⟨1057953, by decide⟩
    (prefixPartial 12 302455) = some ⟨12, 2, 0, 1057953, 302455, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_302455_1057953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302455 ⟨1057953, by decide⟩ :=
  accepted_of_selected 12 302455 ⟨1057953, by decide⟩ ⟨12, 2, 0, 1057953, 302455, 1529, 65536⟩
    (by decide) selected_cut_39043

theorem unmarked_context_11_75613_1057954 : frontier 10 ⟨1057954, by decide⟩
    (prefixCache 11 75613) (prefixPartial 11 75613) = false := by
  decide +kernel

theorem node_context_11_75613_1057954 : EJMOriginalGlobalDAGData.nodes 10 ⟨1057954, by decide⟩ =
    .split (coordinate 11) (![⟨1057911, by decide⟩,⟨891951, by decide⟩,⟨1057933, by decide⟩,⟨1057953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75613_1057954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75613 ⟨1057954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75613
    ⟨1057954, by decide⟩ (by decide) (![⟨1057911, by decide⟩,⟨891951, by decide⟩,⟨1057933, by decide⟩,⟨1057953, by decide⟩]) unmarked_context_11_75613_1057954 node_context_11_75613_1057954
  intro a
  fin_cases a
  · exact context_12_302452_1057911
  · exact context_12_302453_891951
  · exact context_12_302454_1057933
  · exact context_12_302455_1057953

theorem selected_cut_39044 : selected 9 ⟨1057971, by decide⟩
    (prefixPartial 12 302456) = some ⟨12, 2, 0, 1057971, 302456, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_302456_1057971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302456 ⟨1057971, by decide⟩ :=
  accepted_of_selected 12 302456 ⟨1057971, by decide⟩ ⟨12, 2, 0, 1057971, 302456, 1513, 65536⟩
    (by decide) selected_cut_39044

theorem selected_cut_39045 : selected 9 ⟨1057991, by decide⟩
    (prefixPartial 12 302457) = some ⟨12, 2, 0, 1057991, 302457, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_302457_1057991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302457 ⟨1057991, by decide⟩ :=
  accepted_of_selected 12 302457 ⟨1057991, by decide⟩ ⟨12, 2, 0, 1057991, 302457, 1585, 65536⟩
    (by decide) selected_cut_39045

theorem selected_cut_39046 : selected 9 ⟨1058008, by decide⟩
    (prefixPartial 12 302458) = some ⟨12, 2, 0, 1058008, 302458, 1469, 65536⟩ := by
  decide +kernel

theorem context_12_302458_1058008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302458 ⟨1058008, by decide⟩ :=
  accepted_of_selected 12 302458 ⟨1058008, by decide⟩ ⟨12, 2, 0, 1058008, 302458, 1469, 65536⟩
    (by decide) selected_cut_39046

theorem selected_cut_39047 : selected 9 ⟨1058026, by decide⟩
    (prefixPartial 12 302459) = some ⟨12, 2, 0, 1058026, 302459, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_302459_1058026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302459 ⟨1058026, by decide⟩ :=
  accepted_of_selected 12 302459 ⟨1058026, by decide⟩ ⟨12, 2, 0, 1058026, 302459, 1405, 65536⟩
    (by decide) selected_cut_39047

theorem unmarked_context_11_75614_1058027 : frontier 10 ⟨1058027, by decide⟩
    (prefixCache 11 75614) (prefixPartial 11 75614) = false := by
  decide +kernel

theorem node_context_11_75614_1058027 : EJMOriginalGlobalDAGData.nodes 10 ⟨1058027, by decide⟩ =
    .split (coordinate 11) (![⟨1057971, by decide⟩,⟨1057991, by decide⟩,⟨1058008, by decide⟩,⟨1058026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75614_1058027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75614 ⟨1058027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75614
    ⟨1058027, by decide⟩ (by decide) (![⟨1057971, by decide⟩,⟨1057991, by decide⟩,⟨1058008, by decide⟩,⟨1058026, by decide⟩]) unmarked_context_11_75614_1058027 node_context_11_75614_1058027
  intro a
  fin_cases a
  · exact context_12_302456_1057971
  · exact context_12_302457_1057991
  · exact context_12_302458_1058008
  · exact context_12_302459_1058026

theorem selected_cut_39048 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75615) = some ⟨11, 1, 0, 977886, 75615, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75615_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75615 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75615 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75615, 1, 262144⟩
    (by decide) selected_cut_39048

theorem unmarked_context_10_18903_1058028 : frontier 11 ⟨1058028, by decide⟩
    (prefixCache 10 18903) (prefixPartial 10 18903) = false := by
  decide +kernel

theorem node_context_10_18903_1058028 : EJMOriginalGlobalDAGData.nodes 11 ⟨1058028, by decide⟩ =
    .split (coordinate 10) (![⟨1057867, by decide⟩,⟨1057954, by decide⟩,⟨1058027, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18903_1058028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18903 ⟨1058028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18903
    ⟨1058028, by decide⟩ (by decide) (![⟨1057867, by decide⟩,⟨1057954, by decide⟩,⟨1058027, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18903_1058028 node_context_10_18903_1058028
  intro a
  fin_cases a
  · exact context_11_75612_1057867
  · exact context_11_75613_1057954
  · exact context_11_75614_1058027
  · exact context_11_75615_977886

theorem unmarked_context_9_4725_1058029 : frontier 12 ⟨1058029, by decide⟩
    (prefixCache 9 4725) (prefixPartial 9 4725) = false := by
  decide +kernel

theorem node_context_9_4725_1058029 : EJMOriginalGlobalDAGData.nodes 12 ⟨1058029, by decide⟩ =
    .split (coordinate 9) (![⟨1057373, by decide⟩,⟨893098, by decide⟩,⟨1057791, by decide⟩,⟨1058028, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4725_1058029 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4725 ⟨1058029, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4725
    ⟨1058029, by decide⟩ (by decide) (![⟨1057373, by decide⟩,⟨893098, by decide⟩,⟨1057791, by decide⟩,⟨1058028, by decide⟩]) unmarked_context_9_4725_1058029 node_context_9_4725_1058029
  intro a
  fin_cases a
  · exact context_10_18900_1057373
  · exact context_10_18901_893098
  · exact context_10_18902_1057791
  · exact context_10_18903_1058028

theorem selected_cut_39049 : selected 10 ⟨1058092, by decide⟩
    (prefixPartial 11 75616) = some ⟨11, 2, 0, 1058092, 75616, 3977, 262144⟩ := by
  decide +kernel

theorem context_11_75616_1058092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75616 ⟨1058092, by decide⟩ :=
  accepted_of_selected 11 75616 ⟨1058092, by decide⟩ ⟨11, 2, 0, 1058092, 75616, 3977, 262144⟩
    (by decide) selected_cut_39049

theorem selected_cut_39050 : selected 10 ⟨1058153, by decide⟩
    (prefixPartial 11 75617) = some ⟨11, 2, 0, 1058153, 75617, 2997, 262144⟩ := by
  decide +kernel

theorem context_11_75617_1058153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75617 ⟨1058153, by decide⟩ :=
  accepted_of_selected 11 75617 ⟨1058153, by decide⟩ ⟨11, 2, 0, 1058153, 75617, 2997, 262144⟩
    (by decide) selected_cut_39050

theorem selected_cut_39051 : selected 9 ⟨1058187, by decide⟩
    (prefixPartial 12 302472) = some ⟨12, 2, 0, 1058187, 302472, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_302472_1058187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302472 ⟨1058187, by decide⟩ :=
  accepted_of_selected 12 302472 ⟨1058187, by decide⟩ ⟨12, 2, 0, 1058187, 302472, 1493, 65536⟩
    (by decide) selected_cut_39051

theorem selected_cut_39052 : selected 9 ⟨1058218, by decide⟩
    (prefixPartial 12 302473) = some ⟨12, 2, 0, 1058218, 302473, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_302473_1058218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302473 ⟨1058218, by decide⟩ :=
  accepted_of_selected 12 302473 ⟨1058218, by decide⟩ ⟨12, 2, 0, 1058218, 302473, 1529, 65536⟩
    (by decide) selected_cut_39052

theorem selected_cut_39053 : selected 9 ⟨984676, by decide⟩
    (prefixPartial 12 302474) = some ⟨12, 1, 0, 984676, 302474, 1, 65536⟩ := by
  decide +kernel

theorem context_12_302474_984676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302474 ⟨984676, by decide⟩ :=
  accepted_of_selected 12 302474 ⟨984676, by decide⟩ ⟨12, 1, 0, 984676, 302474, 1, 65536⟩
    (by decide) selected_cut_39053

theorem selected_cut_39054 : selected 9 ⟨1058240, by decide⟩
    (prefixPartial 12 302475) = some ⟨12, 2, 0, 1058240, 302475, 1373, 65536⟩ := by
  decide +kernel

theorem context_12_302475_1058240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 302475 ⟨1058240, by decide⟩ :=
  accepted_of_selected 12 302475 ⟨1058240, by decide⟩ ⟨12, 2, 0, 1058240, 302475, 1373, 65536⟩
    (by decide) selected_cut_39054

theorem unmarked_context_11_75618_1058241 : frontier 10 ⟨1058241, by decide⟩
    (prefixCache 11 75618) (prefixPartial 11 75618) = false := by
  decide +kernel

theorem node_context_11_75618_1058241 : EJMOriginalGlobalDAGData.nodes 10 ⟨1058241, by decide⟩ =
    .split (coordinate 11) (![⟨1058187, by decide⟩,⟨1058218, by decide⟩,⟨984676, by decide⟩,⟨1058240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_75618_1058241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75618 ⟨1058241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 75618
    ⟨1058241, by decide⟩ (by decide) (![⟨1058187, by decide⟩,⟨1058218, by decide⟩,⟨984676, by decide⟩,⟨1058240, by decide⟩]) unmarked_context_11_75618_1058241 node_context_11_75618_1058241
  intro a
  fin_cases a
  · exact context_12_302472_1058187
  · exact context_12_302473_1058218
  · exact context_12_302474_984676
  · exact context_12_302475_1058240

theorem selected_cut_39055 : selected 10 ⟨1058314, by decide⟩
    (prefixPartial 11 75619) = some ⟨11, 2, 0, 1058314, 75619, 3765, 262144⟩ := by
  decide +kernel

theorem context_11_75619_1058314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75619 ⟨1058314, by decide⟩ :=
  accepted_of_selected 11 75619 ⟨1058314, by decide⟩ ⟨11, 2, 0, 1058314, 75619, 3765, 262144⟩
    (by decide) selected_cut_39055

theorem unmarked_context_10_18904_1058315 : frontier 11 ⟨1058315, by decide⟩
    (prefixCache 10 18904) (prefixPartial 10 18904) = false := by
  decide +kernel

theorem node_context_10_18904_1058315 : EJMOriginalGlobalDAGData.nodes 11 ⟨1058315, by decide⟩ =
    .split (coordinate 10) (![⟨1058092, by decide⟩,⟨1058153, by decide⟩,⟨1058241, by decide⟩,⟨1058314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18904_1058315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18904 ⟨1058315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18904
    ⟨1058315, by decide⟩ (by decide) (![⟨1058092, by decide⟩,⟨1058153, by decide⟩,⟨1058241, by decide⟩,⟨1058314, by decide⟩]) unmarked_context_10_18904_1058315 node_context_10_18904_1058315
  intro a
  fin_cases a
  · exact context_11_75616_1058092
  · exact context_11_75617_1058153
  · exact context_11_75618_1058241
  · exact context_11_75619_1058314

theorem selected_cut_39056 : selected 10 ⟨1058354, by decide⟩
    (prefixPartial 11 75620) = some ⟨11, 2, 0, 1058354, 75620, 2861, 262144⟩ := by
  decide +kernel

theorem context_11_75620_1058354 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75620 ⟨1058354, by decide⟩ :=
  accepted_of_selected 11 75620 ⟨1058354, by decide⟩ ⟨11, 2, 0, 1058354, 75620, 2861, 262144⟩
    (by decide) selected_cut_39056

theorem selected_cut_39057 : selected 10 ⟨1058380, by decide⟩
    (prefixPartial 11 75621) = some ⟨11, 2, 0, 1058380, 75621, 1765, 262144⟩ := by
  decide +kernel

theorem context_11_75621_1058380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75621 ⟨1058380, by decide⟩ :=
  accepted_of_selected 11 75621 ⟨1058380, by decide⟩ ⟨11, 2, 0, 1058380, 75621, 1765, 262144⟩
    (by decide) selected_cut_39057

theorem selected_cut_39058 : selected 10 ⟨1058415, by decide⟩
    (prefixPartial 11 75622) = some ⟨11, 2, 0, 1058415, 75622, 2709, 262144⟩ := by
  decide +kernel

theorem context_11_75622_1058415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75622 ⟨1058415, by decide⟩ :=
  accepted_of_selected 11 75622 ⟨1058415, by decide⟩ ⟨11, 2, 0, 1058415, 75622, 2709, 262144⟩
    (by decide) selected_cut_39058

theorem selected_cut_39059 : selected 10 ⟨1058452, by decide⟩
    (prefixPartial 11 75623) = some ⟨11, 2, 0, 1058452, 75623, 2577, 262144⟩ := by
  decide +kernel

theorem context_11_75623_1058452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75623 ⟨1058452, by decide⟩ :=
  accepted_of_selected 11 75623 ⟨1058452, by decide⟩ ⟨11, 2, 0, 1058452, 75623, 2577, 262144⟩
    (by decide) selected_cut_39059

theorem unmarked_context_10_18905_1058453 : frontier 11 ⟨1058453, by decide⟩
    (prefixCache 10 18905) (prefixPartial 10 18905) = false := by
  decide +kernel

theorem node_context_10_18905_1058453 : EJMOriginalGlobalDAGData.nodes 11 ⟨1058453, by decide⟩ =
    .split (coordinate 10) (![⟨1058354, by decide⟩,⟨1058380, by decide⟩,⟨1058415, by decide⟩,⟨1058452, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18905_1058453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18905 ⟨1058453, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18905
    ⟨1058453, by decide⟩ (by decide) (![⟨1058354, by decide⟩,⟨1058380, by decide⟩,⟨1058415, by decide⟩,⟨1058452, by decide⟩]) unmarked_context_10_18905_1058453 node_context_10_18905_1058453
  intro a
  fin_cases a
  · exact context_11_75620_1058354
  · exact context_11_75621_1058380
  · exact context_11_75622_1058415
  · exact context_11_75623_1058452

theorem selected_cut_39060 : selected 10 ⟨1058489, by decide⟩
    (prefixPartial 11 75624) = some ⟨11, 2, 0, 1058489, 75624, 2545, 262144⟩ := by
  decide +kernel

theorem context_11_75624_1058489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75624 ⟨1058489, by decide⟩ :=
  accepted_of_selected 11 75624 ⟨1058489, by decide⟩ ⟨11, 2, 0, 1058489, 75624, 2545, 262144⟩
    (by decide) selected_cut_39060

theorem selected_cut_39061 : selected 10 ⟨1058508, by decide⟩
    (prefixPartial 11 75625) = some ⟨11, 2, 0, 1058508, 75625, 1581, 262144⟩ := by
  decide +kernel

theorem context_11_75625_1058508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75625 ⟨1058508, by decide⟩ :=
  accepted_of_selected 11 75625 ⟨1058508, by decide⟩ ⟨11, 2, 0, 1058508, 75625, 1581, 262144⟩
    (by decide) selected_cut_39061

theorem selected_cut_39062 : selected 10 ⟨1058519, by decide⟩
    (prefixPartial 11 75626) = some ⟨11, 2, 0, 1058519, 75626, 737, 262144⟩ := by
  decide +kernel

theorem context_11_75626_1058519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75626 ⟨1058519, by decide⟩ :=
  accepted_of_selected 11 75626 ⟨1058519, by decide⟩ ⟨11, 2, 0, 1058519, 75626, 737, 262144⟩
    (by decide) selected_cut_39062

theorem selected_cut_39063 : selected 10 ⟨1058550, by decide⟩
    (prefixPartial 11 75627) = some ⟨11, 2, 0, 1058550, 75627, 2285, 262144⟩ := by
  decide +kernel

theorem context_11_75627_1058550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75627 ⟨1058550, by decide⟩ :=
  accepted_of_selected 11 75627 ⟨1058550, by decide⟩ ⟨11, 2, 0, 1058550, 75627, 2285, 262144⟩
    (by decide) selected_cut_39063

theorem unmarked_context_10_18906_1058551 : frontier 11 ⟨1058551, by decide⟩
    (prefixCache 10 18906) (prefixPartial 10 18906) = false := by
  decide +kernel

theorem node_context_10_18906_1058551 : EJMOriginalGlobalDAGData.nodes 11 ⟨1058551, by decide⟩ =
    .split (coordinate 10) (![⟨1058489, by decide⟩,⟨1058508, by decide⟩,⟨1058519, by decide⟩,⟨1058550, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18906_1058551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18906 ⟨1058551, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18906
    ⟨1058551, by decide⟩ (by decide) (![⟨1058489, by decide⟩,⟨1058508, by decide⟩,⟨1058519, by decide⟩,⟨1058550, by decide⟩]) unmarked_context_10_18906_1058551 node_context_10_18906_1058551
  intro a
  fin_cases a
  · exact context_11_75624_1058489
  · exact context_11_75625_1058508
  · exact context_11_75626_1058519
  · exact context_11_75627_1058550

theorem selected_cut_39064 : selected 10 ⟨1058580, by decide⟩
    (prefixPartial 11 75628) = some ⟨11, 2, 0, 1058580, 75628, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_75628_1058580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75628 ⟨1058580, by decide⟩ :=
  accepted_of_selected 11 75628 ⟨1058580, by decide⟩ ⟨11, 2, 0, 1058580, 75628, 1709, 262144⟩
    (by decide) selected_cut_39064

theorem selected_cut_39065 : selected 10 ⟨1058596, by decide⟩
    (prefixPartial 11 75629) = some ⟨11, 2, 0, 1058596, 75629, 1149, 262144⟩ := by
  decide +kernel

theorem context_11_75629_1058596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75629 ⟨1058596, by decide⟩ :=
  accepted_of_selected 11 75629 ⟨1058596, by decide⟩ ⟨11, 2, 0, 1058596, 75629, 1149, 262144⟩
    (by decide) selected_cut_39065

theorem selected_cut_39066 : selected 10 ⟨1058615, by decide⟩
    (prefixPartial 11 75630) = some ⟨11, 2, 0, 1058615, 75630, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_75630_1058615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75630 ⟨1058615, by decide⟩ :=
  accepted_of_selected 11 75630 ⟨1058615, by decide⟩ ⟨11, 2, 0, 1058615, 75630, 1673, 262144⟩
    (by decide) selected_cut_39066

theorem selected_cut_39067 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 75631) = some ⟨11, 1, 0, 977886, 75631, 1, 262144⟩ := by
  decide +kernel

theorem context_11_75631_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75631 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 75631 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 75631, 1, 262144⟩
    (by decide) selected_cut_39067

theorem unmarked_context_10_18907_1058616 : frontier 11 ⟨1058616, by decide⟩
    (prefixCache 10 18907) (prefixPartial 10 18907) = false := by
  decide +kernel

theorem node_context_10_18907_1058616 : EJMOriginalGlobalDAGData.nodes 11 ⟨1058616, by decide⟩ =
    .split (coordinate 10) (![⟨1058580, by decide⟩,⟨1058596, by decide⟩,⟨1058615, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18907_1058616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18907 ⟨1058616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18907
    ⟨1058616, by decide⟩ (by decide) (![⟨1058580, by decide⟩,⟨1058596, by decide⟩,⟨1058615, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_18907_1058616 node_context_10_18907_1058616
  intro a
  fin_cases a
  · exact context_11_75628_1058580
  · exact context_11_75629_1058596
  · exact context_11_75630_1058615
  · exact context_11_75631_977886

theorem unmarked_context_9_4726_1058617 : frontier 12 ⟨1058617, by decide⟩
    (prefixCache 9 4726) (prefixPartial 9 4726) = false := by
  decide +kernel

theorem node_context_9_4726_1058617 : EJMOriginalGlobalDAGData.nodes 12 ⟨1058617, by decide⟩ =
    .split (coordinate 9) (![⟨1058315, by decide⟩,⟨1058453, by decide⟩,⟨1058551, by decide⟩,⟨1058616, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_4726_1058617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 4726 ⟨1058617, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 4726
    ⟨1058617, by decide⟩ (by decide) (![⟨1058315, by decide⟩,⟨1058453, by decide⟩,⟨1058551, by decide⟩,⟨1058616, by decide⟩]) unmarked_context_9_4726_1058617 node_context_9_4726_1058617
  intro a
  fin_cases a
  · exact context_10_18904_1058315
  · exact context_10_18905_1058453
  · exact context_10_18906_1058551
  · exact context_10_18907_1058616

theorem selected_cut_39068 : selected 10 ⟨1058634, by decide⟩
    (prefixPartial 11 75632) = some ⟨11, 2, 0, 1058634, 75632, 1637, 262144⟩ := by
  decide +kernel

theorem context_11_75632_1058634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75632 ⟨1058634, by decide⟩ :=
  accepted_of_selected 11 75632 ⟨1058634, by decide⟩ ⟨11, 2, 0, 1058634, 75632, 1637, 262144⟩
    (by decide) selected_cut_39068

theorem selected_cut_39069 : selected 10 ⟨1058666, by decide⟩
    (prefixPartial 11 75633) = some ⟨11, 2, 0, 1058666, 75633, 1821, 262144⟩ := by
  decide +kernel

theorem context_11_75633_1058666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75633 ⟨1058666, by decide⟩ :=
  accepted_of_selected 11 75633 ⟨1058666, by decide⟩ ⟨11, 2, 0, 1058666, 75633, 1821, 262144⟩
    (by decide) selected_cut_39069

theorem selected_cut_39070 : selected 10 ⟨1058697, by decide⟩
    (prefixPartial 11 75634) = some ⟨11, 2, 0, 1058697, 75634, 2069, 262144⟩ := by
  decide +kernel

theorem context_11_75634_1058697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75634 ⟨1058697, by decide⟩ :=
  accepted_of_selected 11 75634 ⟨1058697, by decide⟩ ⟨11, 2, 0, 1058697, 75634, 2069, 262144⟩
    (by decide) selected_cut_39070

theorem selected_cut_39071 : selected 10 ⟨1058738, by decide⟩
    (prefixPartial 11 75635) = some ⟨11, 2, 0, 1058738, 75635, 2153, 262144⟩ := by
  decide +kernel

theorem context_11_75635_1058738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75635 ⟨1058738, by decide⟩ :=
  accepted_of_selected 11 75635 ⟨1058738, by decide⟩ ⟨11, 2, 0, 1058738, 75635, 2153, 262144⟩
    (by decide) selected_cut_39071

theorem unmarked_context_10_18908_1058739 : frontier 11 ⟨1058739, by decide⟩
    (prefixCache 10 18908) (prefixPartial 10 18908) = false := by
  decide +kernel

theorem node_context_10_18908_1058739 : EJMOriginalGlobalDAGData.nodes 11 ⟨1058739, by decide⟩ =
    .split (coordinate 10) (![⟨1058634, by decide⟩,⟨1058666, by decide⟩,⟨1058697, by decide⟩,⟨1058738, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_18908_1058739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 18908 ⟨1058739, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 18908
    ⟨1058739, by decide⟩ (by decide) (![⟨1058634, by decide⟩,⟨1058666, by decide⟩,⟨1058697, by decide⟩,⟨1058738, by decide⟩]) unmarked_context_10_18908_1058739 node_context_10_18908_1058739
  intro a
  fin_cases a
  · exact context_11_75632_1058634
  · exact context_11_75633_1058666
  · exact context_11_75634_1058697
  · exact context_11_75635_1058738

theorem selected_cut_39072 : selected 10 ⟨1058762, by decide⟩
    (prefixPartial 11 75636) = some ⟨11, 2, 0, 1058762, 75636, 1545, 262144⟩ := by
  decide +kernel

theorem context_11_75636_1058762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75636 ⟨1058762, by decide⟩ :=
  accepted_of_selected 11 75636 ⟨1058762, by decide⟩ ⟨11, 2, 0, 1058762, 75636, 1545, 262144⟩
    (by decide) selected_cut_39072

theorem selected_cut_39073 : selected 10 ⟨1058781, by decide⟩
    (prefixPartial 11 75637) = some ⟨11, 2, 0, 1058781, 75637, 977, 262144⟩ := by
  decide +kernel

theorem context_11_75637_1058781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75637 ⟨1058781, by decide⟩ :=
  accepted_of_selected 11 75637 ⟨1058781, by decide⟩ ⟨11, 2, 0, 1058781, 75637, 977, 262144⟩
    (by decide) selected_cut_39073

theorem selected_cut_39074 : selected 10 ⟨1058802, by decide⟩
    (prefixPartial 11 75638) = some ⟨11, 2, 0, 1058802, 75638, 1269, 262144⟩ := by
  decide +kernel

theorem context_11_75638_1058802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75638 ⟨1058802, by decide⟩ :=
  accepted_of_selected 11 75638 ⟨1058802, by decide⟩ ⟨11, 2, 0, 1058802, 75638, 1269, 262144⟩
    (by decide) selected_cut_39074

theorem selected_cut_39075 : selected 10 ⟨1058819, by decide⟩
    (prefixPartial 11 75639) = some ⟨11, 2, 0, 1058819, 75639, 937, 262144⟩ := by
  decide +kernel

theorem context_11_75639_1058819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 75639 ⟨1058819, by decide⟩ :=
  accepted_of_selected 11 75639 ⟨1058819, by decide⟩ ⟨11, 2, 0, 1058819, 75639, 937, 262144⟩
    (by decide) selected_cut_39075

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
