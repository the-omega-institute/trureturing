/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover234
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_75794_573971 : frontier 9 ⟨573971, by decide⟩
    (prefixCache 12 75794) (prefixPartial 12 75794) = false := by
  decide +kernel

theorem node_context_12_75794_573971 : EJMOriginalGlobalDAGData.nodes 9 ⟨573971, by decide⟩ =
    .split (coordinate 12) (![⟨573925, by decide⟩,⟨573946, by decide⟩,⟨573964, by decide⟩,⟨573970, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75794_573971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75794 ⟨573971, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75794
    ⟨573971, by decide⟩ (by decide) (![⟨573925, by decide⟩,⟨573946, by decide⟩,⟨573964, by decide⟩,⟨573970, by decide⟩]) unmarked_context_12_75794_573971 node_context_12_75794_573971
  intro a
  fin_cases a
  · exact context_13_303176_573925
  · exact context_13_303177_573946
  · exact context_13_303178_573964
  · exact context_13_303179_573970

theorem selected_cut_22563 : selected 8 ⟨573997, by decide⟩
    (prefixPartial 13 303180) = some ⟨13, 2, 0, 573997, 303180, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_303180_573997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303180 ⟨573997, by decide⟩ :=
  accepted_of_selected 13 303180 ⟨573997, by decide⟩ ⟨13, 2, 0, 573997, 303180, 1325, 16384⟩
    (by decide) selected_cut_22563

theorem selected_cut_22564 : selected 8 ⟨574021, by decide⟩
    (prefixPartial 13 303181) = some ⟨13, 2, 0, 574021, 303181, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_303181_574021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303181 ⟨574021, by decide⟩ :=
  accepted_of_selected 13 303181 ⟨574021, by decide⟩ ⟨13, 2, 0, 574021, 303181, 1761, 16384⟩
    (by decide) selected_cut_22564

theorem selected_cut_22565 : selected 8 ⟨574040, by decide⟩
    (prefixPartial 13 303182) = some ⟨13, 2, 0, 574040, 303182, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_303182_574040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303182 ⟨574040, by decide⟩ :=
  accepted_of_selected 13 303182 ⟨574040, by decide⟩ ⟨13, 2, 0, 574040, 303182, 1137, 16384⟩
    (by decide) selected_cut_22565

theorem selected_cut_22566 : selected 8 ⟨574044, by decide⟩
    (prefixPartial 13 303183) = some ⟨13, 2, 0, 574044, 303183, 621, 16384⟩ := by
  decide +kernel

theorem context_13_303183_574044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303183 ⟨574044, by decide⟩ :=
  accepted_of_selected 13 303183 ⟨574044, by decide⟩ ⟨13, 2, 0, 574044, 303183, 621, 16384⟩
    (by decide) selected_cut_22566

theorem unmarked_context_12_75795_574045 : frontier 9 ⟨574045, by decide⟩
    (prefixCache 12 75795) (prefixPartial 12 75795) = false := by
  decide +kernel

theorem node_context_12_75795_574045 : EJMOriginalGlobalDAGData.nodes 9 ⟨574045, by decide⟩ =
    .split (coordinate 12) (![⟨573997, by decide⟩,⟨574021, by decide⟩,⟨574040, by decide⟩,⟨574044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75795_574045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75795 ⟨574045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75795
    ⟨574045, by decide⟩ (by decide) (![⟨573997, by decide⟩,⟨574021, by decide⟩,⟨574040, by decide⟩,⟨574044, by decide⟩]) unmarked_context_12_75795_574045 node_context_12_75795_574045
  intro a
  fin_cases a
  · exact context_13_303180_573997
  · exact context_13_303181_574021
  · exact context_13_303182_574040
  · exact context_13_303183_574044

theorem unmarked_context_11_18948_574046 : frontier 10 ⟨574046, by decide⟩
    (prefixCache 11 18948) (prefixPartial 11 18948) = false := by
  decide +kernel

theorem node_context_11_18948_574046 : EJMOriginalGlobalDAGData.nodes 10 ⟨574046, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨573896, by decide⟩,⟨573971, by decide⟩,⟨574045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18948_574046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18948 ⟨574046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18948
    ⟨574046, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨573896, by decide⟩,⟨573971, by decide⟩,⟨574045, by decide⟩]) unmarked_context_11_18948_574046 node_context_11_18948_574046
  intro a
  fin_cases a
  · exact context_12_75792_435160
  · exact context_12_75793_573896
  · exact context_12_75794_573971
  · exact context_12_75795_574045

theorem selected_cut_22567 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 75796) = some ⟨12, 1, 0, 435160, 75796, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75796_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75796 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 75796 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 75796, 1, 65536⟩
    (by decide) selected_cut_22567

theorem selected_cut_22568 : selected 8 ⟨574076, by decide⟩
    (prefixPartial 13 303188) = some ⟨13, 2, 0, 574076, 303188, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_303188_574076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303188 ⟨574076, by decide⟩ :=
  accepted_of_selected 13 303188 ⟨574076, by decide⟩ ⟨13, 2, 0, 574076, 303188, 1521, 16384⟩
    (by decide) selected_cut_22568

theorem selected_cut_22569 : selected 8 ⟨574096, by decide⟩
    (prefixPartial 13 303189) = some ⟨13, 2, 0, 574096, 303189, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_303189_574096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303189 ⟨574096, by decide⟩ :=
  accepted_of_selected 13 303189 ⟨574096, by decide⟩ ⟨13, 2, 0, 574096, 303189, 1941, 16384⟩
    (by decide) selected_cut_22569

theorem selected_cut_22570 : selected 8 ⟨574116, by decide⟩
    (prefixPartial 13 303190) = some ⟨13, 2, 0, 574116, 303190, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_303190_574116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303190 ⟨574116, by decide⟩ :=
  accepted_of_selected 13 303190 ⟨574116, by decide⟩ ⟨13, 2, 0, 574116, 303190, 1469, 16384⟩
    (by decide) selected_cut_22570

theorem selected_cut_22571 : selected 8 ⟨574121, by decide⟩
    (prefixPartial 13 303191) = some ⟨13, 2, 0, 574121, 303191, 925, 16384⟩ := by
  decide +kernel

theorem context_13_303191_574121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303191 ⟨574121, by decide⟩ :=
  accepted_of_selected 13 303191 ⟨574121, by decide⟩ ⟨13, 2, 0, 574121, 303191, 925, 16384⟩
    (by decide) selected_cut_22571

theorem unmarked_context_12_75797_574122 : frontier 9 ⟨574122, by decide⟩
    (prefixCache 12 75797) (prefixPartial 12 75797) = false := by
  decide +kernel

theorem node_context_12_75797_574122 : EJMOriginalGlobalDAGData.nodes 9 ⟨574122, by decide⟩ =
    .split (coordinate 12) (![⟨574076, by decide⟩,⟨574096, by decide⟩,⟨574116, by decide⟩,⟨574121, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75797_574122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75797 ⟨574122, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75797
    ⟨574122, by decide⟩ (by decide) (![⟨574076, by decide⟩,⟨574096, by decide⟩,⟨574116, by decide⟩,⟨574121, by decide⟩]) unmarked_context_12_75797_574122 node_context_12_75797_574122
  intro a
  fin_cases a
  · exact context_13_303188_574076
  · exact context_13_303189_574096
  · exact context_13_303190_574116
  · exact context_13_303191_574121

theorem selected_cut_22572 : selected 8 ⟨574154, by decide⟩
    (prefixPartial 13 303192) = some ⟨13, 2, 0, 574154, 303192, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_303192_574154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303192 ⟨574154, by decide⟩ :=
  accepted_of_selected 13 303192 ⟨574154, by decide⟩ ⟨13, 2, 0, 574154, 303192, 1597, 16384⟩
    (by decide) selected_cut_22572

theorem selected_cut_22573 : selected 8 ⟨574178, by decide⟩
    (prefixPartial 13 303193) = some ⟨13, 2, 0, 574178, 303193, 2213, 16384⟩ := by
  decide +kernel

theorem context_13_303193_574178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303193 ⟨574178, by decide⟩ :=
  accepted_of_selected 13 303193 ⟨574178, by decide⟩ ⟨13, 2, 0, 574178, 303193, 2213, 16384⟩
    (by decide) selected_cut_22573

theorem selected_cut_22574 : selected 8 ⟨574197, by decide⟩
    (prefixPartial 13 303194) = some ⟨13, 2, 0, 574197, 303194, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_303194_574197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303194 ⟨574197, by decide⟩ :=
  accepted_of_selected 13 303194 ⟨574197, by decide⟩ ⟨13, 2, 0, 574197, 303194, 1473, 16384⟩
    (by decide) selected_cut_22574

theorem selected_cut_22575 : selected 8 ⟨574206, by decide⟩
    (prefixPartial 13 303195) = some ⟨13, 2, 0, 574206, 303195, 913, 16384⟩ := by
  decide +kernel

theorem context_13_303195_574206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303195 ⟨574206, by decide⟩ :=
  accepted_of_selected 13 303195 ⟨574206, by decide⟩ ⟨13, 2, 0, 574206, 303195, 913, 16384⟩
    (by decide) selected_cut_22575

theorem unmarked_context_12_75798_574207 : frontier 9 ⟨574207, by decide⟩
    (prefixCache 12 75798) (prefixPartial 12 75798) = false := by
  decide +kernel

theorem node_context_12_75798_574207 : EJMOriginalGlobalDAGData.nodes 9 ⟨574207, by decide⟩ =
    .split (coordinate 12) (![⟨574154, by decide⟩,⟨574178, by decide⟩,⟨574197, by decide⟩,⟨574206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75798_574207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75798 ⟨574207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75798
    ⟨574207, by decide⟩ (by decide) (![⟨574154, by decide⟩,⟨574178, by decide⟩,⟨574197, by decide⟩,⟨574206, by decide⟩]) unmarked_context_12_75798_574207 node_context_12_75798_574207
  intro a
  fin_cases a
  · exact context_13_303192_574154
  · exact context_13_303193_574178
  · exact context_13_303194_574197
  · exact context_13_303195_574206

theorem selected_cut_22576 : selected 8 ⟨574237, by decide⟩
    (prefixPartial 13 303196) = some ⟨13, 2, 0, 574237, 303196, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_303196_574237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303196 ⟨574237, by decide⟩ :=
  accepted_of_selected 13 303196 ⟨574237, by decide⟩ ⟨13, 2, 0, 574237, 303196, 1589, 16384⟩
    (by decide) selected_cut_22576

theorem selected_cut_22577 : selected 8 ⟨574265, by decide⟩
    (prefixPartial 13 303197) = some ⟨13, 2, 0, 574265, 303197, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_303197_574265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303197 ⟨574265, by decide⟩ :=
  accepted_of_selected 13 303197 ⟨574265, by decide⟩ ⟨13, 2, 0, 574265, 303197, 2337, 16384⟩
    (by decide) selected_cut_22577

theorem selected_cut_22578 : selected 8 ⟨574288, by decide⟩
    (prefixPartial 13 303198) = some ⟨13, 2, 0, 574288, 303198, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_303198_574288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303198 ⟨574288, by decide⟩ :=
  accepted_of_selected 13 303198 ⟨574288, by decide⟩ ⟨13, 2, 0, 574288, 303198, 1549, 16384⟩
    (by decide) selected_cut_22578

theorem selected_cut_22579 : selected 8 ⟨574292, by decide⟩
    (prefixPartial 13 303199) = some ⟨13, 2, 0, 574292, 303199, 765, 16384⟩ := by
  decide +kernel

theorem context_13_303199_574292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303199 ⟨574292, by decide⟩ :=
  accepted_of_selected 13 303199 ⟨574292, by decide⟩ ⟨13, 2, 0, 574292, 303199, 765, 16384⟩
    (by decide) selected_cut_22579

theorem unmarked_context_12_75799_574293 : frontier 9 ⟨574293, by decide⟩
    (prefixCache 12 75799) (prefixPartial 12 75799) = false := by
  decide +kernel

theorem node_context_12_75799_574293 : EJMOriginalGlobalDAGData.nodes 9 ⟨574293, by decide⟩ =
    .split (coordinate 12) (![⟨574237, by decide⟩,⟨574265, by decide⟩,⟨574288, by decide⟩,⟨574292, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75799_574293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75799 ⟨574293, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75799
    ⟨574293, by decide⟩ (by decide) (![⟨574237, by decide⟩,⟨574265, by decide⟩,⟨574288, by decide⟩,⟨574292, by decide⟩]) unmarked_context_12_75799_574293 node_context_12_75799_574293
  intro a
  fin_cases a
  · exact context_13_303196_574237
  · exact context_13_303197_574265
  · exact context_13_303198_574288
  · exact context_13_303199_574292

theorem unmarked_context_11_18949_574294 : frontier 10 ⟨574294, by decide⟩
    (prefixCache 11 18949) (prefixPartial 11 18949) = false := by
  decide +kernel

theorem node_context_11_18949_574294 : EJMOriginalGlobalDAGData.nodes 10 ⟨574294, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨574122, by decide⟩,⟨574207, by decide⟩,⟨574293, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18949_574294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18949 ⟨574294, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18949
    ⟨574294, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨574122, by decide⟩,⟨574207, by decide⟩,⟨574293, by decide⟩]) unmarked_context_11_18949_574294 node_context_11_18949_574294
  intro a
  fin_cases a
  · exact context_12_75796_435160
  · exact context_12_75797_574122
  · exact context_12_75798_574207
  · exact context_12_75799_574293

theorem selected_cut_22580 : selected 9 ⟨449505, by decide⟩
    (prefixPartial 12 75800) = some ⟨12, 1, 0, 449505, 75800, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75800_449505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75800 ⟨449505, by decide⟩ :=
  accepted_of_selected 12 75800 ⟨449505, by decide⟩ ⟨12, 1, 0, 449505, 75800, 1, 65536⟩
    (by decide) selected_cut_22580

theorem selected_cut_22581 : selected 8 ⟨574324, by decide⟩
    (prefixPartial 13 303204) = some ⟨13, 2, 0, 574324, 303204, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_303204_574324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303204 ⟨574324, by decide⟩ :=
  accepted_of_selected 13 303204 ⟨574324, by decide⟩ ⟨13, 2, 0, 574324, 303204, 1441, 16384⟩
    (by decide) selected_cut_22581

theorem selected_cut_22582 : selected 8 ⟨574348, by decide⟩
    (prefixPartial 13 303205) = some ⟨13, 2, 0, 574348, 303205, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_303205_574348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303205 ⟨574348, by decide⟩ :=
  accepted_of_selected 13 303205 ⟨574348, by decide⟩ ⟨13, 2, 0, 574348, 303205, 1989, 16384⟩
    (by decide) selected_cut_22582

theorem selected_cut_22583 : selected 8 ⟨574367, by decide⟩
    (prefixPartial 13 303206) = some ⟨13, 2, 0, 574367, 303206, 1505, 16384⟩ := by
  decide +kernel

theorem context_13_303206_574367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303206 ⟨574367, by decide⟩ :=
  accepted_of_selected 13 303206 ⟨574367, by decide⟩ ⟨13, 2, 0, 574367, 303206, 1505, 16384⟩
    (by decide) selected_cut_22583

theorem selected_cut_22584 : selected 8 ⟨574375, by decide⟩
    (prefixPartial 13 303207) = some ⟨13, 2, 0, 574375, 303207, 925, 16384⟩ := by
  decide +kernel

theorem context_13_303207_574375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303207 ⟨574375, by decide⟩ :=
  accepted_of_selected 13 303207 ⟨574375, by decide⟩ ⟨13, 2, 0, 574375, 303207, 925, 16384⟩
    (by decide) selected_cut_22584

theorem unmarked_context_12_75801_574376 : frontier 9 ⟨574376, by decide⟩
    (prefixCache 12 75801) (prefixPartial 12 75801) = false := by
  decide +kernel

theorem node_context_12_75801_574376 : EJMOriginalGlobalDAGData.nodes 9 ⟨574376, by decide⟩ =
    .split (coordinate 12) (![⟨574324, by decide⟩,⟨574348, by decide⟩,⟨574367, by decide⟩,⟨574375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75801_574376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75801 ⟨574376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75801
    ⟨574376, by decide⟩ (by decide) (![⟨574324, by decide⟩,⟨574348, by decide⟩,⟨574367, by decide⟩,⟨574375, by decide⟩]) unmarked_context_12_75801_574376 node_context_12_75801_574376
  intro a
  fin_cases a
  · exact context_13_303204_574324
  · exact context_13_303205_574348
  · exact context_13_303206_574367
  · exact context_13_303207_574375

theorem selected_cut_22585 : selected 8 ⟨574401, by decide⟩
    (prefixPartial 13 303208) = some ⟨13, 2, 0, 574401, 303208, 937, 16384⟩ := by
  decide +kernel

theorem context_13_303208_574401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303208 ⟨574401, by decide⟩ :=
  accepted_of_selected 13 303208 ⟨574401, by decide⟩ ⟨13, 2, 0, 574401, 303208, 937, 16384⟩
    (by decide) selected_cut_22585

theorem selected_cut_22586 : selected 8 ⟨574424, by decide⟩
    (prefixPartial 13 303209) = some ⟨13, 2, 0, 574424, 303209, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_303209_574424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303209 ⟨574424, by decide⟩ :=
  accepted_of_selected 13 303209 ⟨574424, by decide⟩ ⟨13, 2, 0, 574424, 303209, 1749, 16384⟩
    (by decide) selected_cut_22586

theorem selected_cut_22587 : selected 8 ⟨574437, by decide⟩
    (prefixPartial 13 303210) = some ⟨13, 2, 0, 574437, 303210, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_303210_574437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303210 ⟨574437, by decide⟩ :=
  accepted_of_selected 13 303210 ⟨574437, by decide⟩ ⟨13, 2, 0, 574437, 303210, 1233, 16384⟩
    (by decide) selected_cut_22587

theorem selected_cut_22588 : selected 8 ⟨574447, by decide⟩
    (prefixPartial 13 303211) = some ⟨13, 2, 0, 574447, 303211, 833, 16384⟩ := by
  decide +kernel

theorem context_13_303211_574447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303211 ⟨574447, by decide⟩ :=
  accepted_of_selected 13 303211 ⟨574447, by decide⟩ ⟨13, 2, 0, 574447, 303211, 833, 16384⟩
    (by decide) selected_cut_22588

theorem unmarked_context_12_75802_574448 : frontier 9 ⟨574448, by decide⟩
    (prefixCache 12 75802) (prefixPartial 12 75802) = false := by
  decide +kernel

theorem node_context_12_75802_574448 : EJMOriginalGlobalDAGData.nodes 9 ⟨574448, by decide⟩ =
    .split (coordinate 12) (![⟨574401, by decide⟩,⟨574424, by decide⟩,⟨574437, by decide⟩,⟨574447, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75802_574448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75802 ⟨574448, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75802
    ⟨574448, by decide⟩ (by decide) (![⟨574401, by decide⟩,⟨574424, by decide⟩,⟨574437, by decide⟩,⟨574447, by decide⟩]) unmarked_context_12_75802_574448 node_context_12_75802_574448
  intro a
  fin_cases a
  · exact context_13_303208_574401
  · exact context_13_303209_574424
  · exact context_13_303210_574437
  · exact context_13_303211_574447

theorem selected_cut_22589 : selected 8 ⟨574470, by decide⟩
    (prefixPartial 13 303212) = some ⟨13, 2, 0, 574470, 303212, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_303212_574470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303212 ⟨574470, by decide⟩ :=
  accepted_of_selected 13 303212 ⟨574470, by decide⟩ ⟨13, 2, 0, 574470, 303212, 1121, 16384⟩
    (by decide) selected_cut_22589

theorem selected_cut_22590 : selected 8 ⟨574495, by decide⟩
    (prefixPartial 13 303213) = some ⟨13, 2, 0, 574495, 303213, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_303213_574495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303213 ⟨574495, by decide⟩ :=
  accepted_of_selected 13 303213 ⟨574495, by decide⟩ ⟨13, 2, 0, 574495, 303213, 2237, 16384⟩
    (by decide) selected_cut_22590

theorem selected_cut_22591 : selected 8 ⟨574513, by decide⟩
    (prefixPartial 13 303214) = some ⟨13, 2, 0, 574513, 303214, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_303214_574513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303214 ⟨574513, by decide⟩ :=
  accepted_of_selected 13 303214 ⟨574513, by decide⟩ ⟨13, 2, 0, 574513, 303214, 1313, 16384⟩
    (by decide) selected_cut_22591

theorem selected_cut_22592 : selected 8 ⟨574518, by decide⟩
    (prefixPartial 13 303215) = some ⟨13, 2, 0, 574518, 303215, 673, 16384⟩ := by
  decide +kernel

theorem context_13_303215_574518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303215 ⟨574518, by decide⟩ :=
  accepted_of_selected 13 303215 ⟨574518, by decide⟩ ⟨13, 2, 0, 574518, 303215, 673, 16384⟩
    (by decide) selected_cut_22592

theorem unmarked_context_12_75803_574519 : frontier 9 ⟨574519, by decide⟩
    (prefixCache 12 75803) (prefixPartial 12 75803) = false := by
  decide +kernel

theorem node_context_12_75803_574519 : EJMOriginalGlobalDAGData.nodes 9 ⟨574519, by decide⟩ =
    .split (coordinate 12) (![⟨574470, by decide⟩,⟨574495, by decide⟩,⟨574513, by decide⟩,⟨574518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75803_574519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75803 ⟨574519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75803
    ⟨574519, by decide⟩ (by decide) (![⟨574470, by decide⟩,⟨574495, by decide⟩,⟨574513, by decide⟩,⟨574518, by decide⟩]) unmarked_context_12_75803_574519 node_context_12_75803_574519
  intro a
  fin_cases a
  · exact context_13_303212_574470
  · exact context_13_303213_574495
  · exact context_13_303214_574513
  · exact context_13_303215_574518

theorem unmarked_context_11_18950_574520 : frontier 10 ⟨574520, by decide⟩
    (prefixCache 11 18950) (prefixPartial 11 18950) = false := by
  decide +kernel

theorem node_context_11_18950_574520 : EJMOriginalGlobalDAGData.nodes 10 ⟨574520, by decide⟩ =
    .split (coordinate 11) (![⟨449505, by decide⟩,⟨574376, by decide⟩,⟨574448, by decide⟩,⟨574519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18950_574520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18950 ⟨574520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18950
    ⟨574520, by decide⟩ (by decide) (![⟨449505, by decide⟩,⟨574376, by decide⟩,⟨574448, by decide⟩,⟨574519, by decide⟩]) unmarked_context_11_18950_574520 node_context_11_18950_574520
  intro a
  fin_cases a
  · exact context_12_75800_449505
  · exact context_12_75801_574376
  · exact context_12_75802_574448
  · exact context_12_75803_574519

theorem selected_cut_22593 : selected 9 ⟨539296, by decide⟩
    (prefixPartial 12 75804) = some ⟨12, 1, 0, 539296, 75804, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75804_539296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75804 ⟨539296, by decide⟩ :=
  accepted_of_selected 12 75804 ⟨539296, by decide⟩ ⟨12, 1, 0, 539296, 75804, 1, 65536⟩
    (by decide) selected_cut_22593

theorem selected_cut_22594 : selected 8 ⟨574544, by decide⟩
    (prefixPartial 13 303220) = some ⟨13, 2, 0, 574544, 303220, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_303220_574544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303220 ⟨574544, by decide⟩ :=
  accepted_of_selected 13 303220 ⟨574544, by decide⟩ ⟨13, 2, 0, 574544, 303220, 1277, 16384⟩
    (by decide) selected_cut_22594

theorem selected_cut_22595 : selected 8 ⟨574577, by decide⟩
    (prefixPartial 13 303221) = some ⟨13, 2, 0, 574577, 303221, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_303221_574577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303221 ⟨574577, by decide⟩ :=
  accepted_of_selected 13 303221 ⟨574577, by decide⟩ ⟨13, 2, 0, 574577, 303221, 2397, 16384⟩
    (by decide) selected_cut_22595

theorem selected_cut_22596 : selected 8 ⟨574594, by decide⟩
    (prefixPartial 13 303222) = some ⟨13, 2, 0, 574594, 303222, 1629, 16384⟩ := by
  decide +kernel

theorem context_13_303222_574594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303222 ⟨574594, by decide⟩ :=
  accepted_of_selected 13 303222 ⟨574594, by decide⟩ ⟨13, 2, 0, 574594, 303222, 1629, 16384⟩
    (by decide) selected_cut_22596

theorem selected_cut_22597 : selected 8 ⟨574603, by decide⟩
    (prefixPartial 13 303223) = some ⟨13, 2, 0, 574603, 303223, 925, 16384⟩ := by
  decide +kernel

theorem context_13_303223_574603 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303223 ⟨574603, by decide⟩ :=
  accepted_of_selected 13 303223 ⟨574603, by decide⟩ ⟨13, 2, 0, 574603, 303223, 925, 16384⟩
    (by decide) selected_cut_22597

theorem unmarked_context_12_75805_574604 : frontier 9 ⟨574604, by decide⟩
    (prefixCache 12 75805) (prefixPartial 12 75805) = false := by
  decide +kernel

theorem node_context_12_75805_574604 : EJMOriginalGlobalDAGData.nodes 9 ⟨574604, by decide⟩ =
    .split (coordinate 12) (![⟨574544, by decide⟩,⟨574577, by decide⟩,⟨574594, by decide⟩,⟨574603, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75805_574604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75805 ⟨574604, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75805
    ⟨574604, by decide⟩ (by decide) (![⟨574544, by decide⟩,⟨574577, by decide⟩,⟨574594, by decide⟩,⟨574603, by decide⟩]) unmarked_context_12_75805_574604 node_context_12_75805_574604
  intro a
  fin_cases a
  · exact context_13_303220_574544
  · exact context_13_303221_574577
  · exact context_13_303222_574594
  · exact context_13_303223_574603

theorem selected_cut_22598 : selected 8 ⟨574628, by decide⟩
    (prefixPartial 13 303224) = some ⟨13, 2, 0, 574628, 303224, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_303224_574628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303224 ⟨574628, by decide⟩ :=
  accepted_of_selected 13 303224 ⟨574628, by decide⟩ ⟨13, 2, 0, 574628, 303224, 1137, 16384⟩
    (by decide) selected_cut_22598

theorem selected_cut_22599 : selected 8 ⟨574654, by decide⟩
    (prefixPartial 13 303225) = some ⟨13, 2, 0, 574654, 303225, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_303225_574654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303225 ⟨574654, by decide⟩ :=
  accepted_of_selected 13 303225 ⟨574654, by decide⟩ ⟨13, 2, 0, 574654, 303225, 2377, 16384⟩
    (by decide) selected_cut_22599

theorem selected_cut_22600 : selected 8 ⟨574672, by decide⟩
    (prefixPartial 13 303226) = some ⟨13, 2, 0, 574672, 303226, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_303226_574672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303226 ⟨574672, by decide⟩ :=
  accepted_of_selected 13 303226 ⟨574672, by decide⟩ ⟨13, 2, 0, 574672, 303226, 1529, 16384⟩
    (by decide) selected_cut_22600

theorem selected_cut_22601 : selected 8 ⟨574685, by decide⟩
    (prefixPartial 13 303227) = some ⟨13, 2, 0, 574685, 303227, 957, 16384⟩ := by
  decide +kernel

theorem context_13_303227_574685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303227 ⟨574685, by decide⟩ :=
  accepted_of_selected 13 303227 ⟨574685, by decide⟩ ⟨13, 2, 0, 574685, 303227, 957, 16384⟩
    (by decide) selected_cut_22601

theorem unmarked_context_12_75806_574686 : frontier 9 ⟨574686, by decide⟩
    (prefixCache 12 75806) (prefixPartial 12 75806) = false := by
  decide +kernel

theorem node_context_12_75806_574686 : EJMOriginalGlobalDAGData.nodes 9 ⟨574686, by decide⟩ =
    .split (coordinate 12) (![⟨574628, by decide⟩,⟨574654, by decide⟩,⟨574672, by decide⟩,⟨574685, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75806_574686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75806 ⟨574686, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75806
    ⟨574686, by decide⟩ (by decide) (![⟨574628, by decide⟩,⟨574654, by decide⟩,⟨574672, by decide⟩,⟨574685, by decide⟩]) unmarked_context_12_75806_574686 node_context_12_75806_574686
  intro a
  fin_cases a
  · exact context_13_303224_574628
  · exact context_13_303225_574654
  · exact context_13_303226_574672
  · exact context_13_303227_574685

theorem selected_cut_22602 : selected 8 ⟨574712, by decide⟩
    (prefixPartial 13 303228) = some ⟨13, 2, 0, 574712, 303228, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_303228_574712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303228 ⟨574712, by decide⟩ :=
  accepted_of_selected 13 303228 ⟨574712, by decide⟩ ⟨13, 2, 0, 574712, 303228, 1041, 16384⟩
    (by decide) selected_cut_22602

theorem selected_cut_22603 : selected 8 ⟨574739, by decide⟩
    (prefixPartial 13 303229) = some ⟨13, 2, 0, 574739, 303229, 2321, 16384⟩ := by
  decide +kernel

theorem context_13_303229_574739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303229 ⟨574739, by decide⟩ :=
  accepted_of_selected 13 303229 ⟨574739, by decide⟩ ⟨13, 2, 0, 574739, 303229, 2321, 16384⟩
    (by decide) selected_cut_22603

theorem selected_cut_22604 : selected 8 ⟨574758, by decide⟩
    (prefixPartial 13 303230) = some ⟨13, 2, 0, 574758, 303230, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_303230_574758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303230 ⟨574758, by decide⟩ :=
  accepted_of_selected 13 303230 ⟨574758, by decide⟩ ⟨13, 2, 0, 574758, 303230, 1441, 16384⟩
    (by decide) selected_cut_22604

theorem selected_cut_22605 : selected 8 ⟨574762, by decide⟩
    (prefixPartial 13 303231) = some ⟨13, 2, 0, 574762, 303231, 673, 16384⟩ := by
  decide +kernel

theorem context_13_303231_574762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303231 ⟨574762, by decide⟩ :=
  accepted_of_selected 13 303231 ⟨574762, by decide⟩ ⟨13, 2, 0, 574762, 303231, 673, 16384⟩
    (by decide) selected_cut_22605

theorem unmarked_context_12_75807_574763 : frontier 9 ⟨574763, by decide⟩
    (prefixCache 12 75807) (prefixPartial 12 75807) = false := by
  decide +kernel

theorem node_context_12_75807_574763 : EJMOriginalGlobalDAGData.nodes 9 ⟨574763, by decide⟩ =
    .split (coordinate 12) (![⟨574712, by decide⟩,⟨574739, by decide⟩,⟨574758, by decide⟩,⟨574762, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75807_574763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75807 ⟨574763, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75807
    ⟨574763, by decide⟩ (by decide) (![⟨574712, by decide⟩,⟨574739, by decide⟩,⟨574758, by decide⟩,⟨574762, by decide⟩]) unmarked_context_12_75807_574763 node_context_12_75807_574763
  intro a
  fin_cases a
  · exact context_13_303228_574712
  · exact context_13_303229_574739
  · exact context_13_303230_574758
  · exact context_13_303231_574762

theorem unmarked_context_11_18951_574764 : frontier 10 ⟨574764, by decide⟩
    (prefixCache 11 18951) (prefixPartial 11 18951) = false := by
  decide +kernel

theorem node_context_11_18951_574764 : EJMOriginalGlobalDAGData.nodes 10 ⟨574764, by decide⟩ =
    .split (coordinate 11) (![⟨539296, by decide⟩,⟨574604, by decide⟩,⟨574686, by decide⟩,⟨574763, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18951_574764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18951 ⟨574764, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18951
    ⟨574764, by decide⟩ (by decide) (![⟨539296, by decide⟩,⟨574604, by decide⟩,⟨574686, by decide⟩,⟨574763, by decide⟩]) unmarked_context_11_18951_574764 node_context_11_18951_574764
  intro a
  fin_cases a
  · exact context_12_75804_539296
  · exact context_12_75805_574604
  · exact context_12_75806_574686
  · exact context_12_75807_574763

theorem unmarked_context_10_4737_574765 : frontier 11 ⟨574765, by decide⟩
    (prefixCache 10 4737) (prefixPartial 10 4737) = false := by
  decide +kernel

theorem node_context_10_4737_574765 : EJMOriginalGlobalDAGData.nodes 11 ⟨574765, by decide⟩ =
    .split (coordinate 10) (![⟨574046, by decide⟩,⟨574294, by decide⟩,⟨574520, by decide⟩,⟨574764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4737_574765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4737 ⟨574765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4737
    ⟨574765, by decide⟩ (by decide) (![⟨574046, by decide⟩,⟨574294, by decide⟩,⟨574520, by decide⟩,⟨574764, by decide⟩]) unmarked_context_10_4737_574765 node_context_10_4737_574765
  intro a
  fin_cases a
  · exact context_11_18948_574046
  · exact context_11_18949_574294
  · exact context_11_18950_574520
  · exact context_11_18951_574764

theorem selected_cut_22606 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 75808) = some ⟨12, 1, 0, 435790, 75808, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75808_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75808 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 75808 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 75808, 1, 65536⟩
    (by decide) selected_cut_22606

theorem selected_cut_22607 : selected 9 ⟨574819, by decide⟩
    (prefixPartial 12 75809) = some ⟨12, 2, 0, 574819, 75809, 4049, 65536⟩ := by
  decide +kernel

theorem context_12_75809_574819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75809 ⟨574819, by decide⟩ :=
  accepted_of_selected 12 75809 ⟨574819, by decide⟩ ⟨12, 2, 0, 574819, 75809, 4049, 65536⟩
    (by decide) selected_cut_22607

theorem selected_cut_22608 : selected 9 ⟨574874, by decide⟩
    (prefixPartial 12 75810) = some ⟨12, 2, 0, 574874, 75810, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_75810_574874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75810 ⟨574874, by decide⟩ :=
  accepted_of_selected 12 75810 ⟨574874, by decide⟩ ⟨12, 2, 0, 574874, 75810, 3861, 65536⟩
    (by decide) selected_cut_22608

theorem selected_cut_22609 : selected 9 ⟨574928, by decide⟩
    (prefixPartial 12 75811) = some ⟨12, 2, 0, 574928, 75811, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_75811_574928 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75811 ⟨574928, by decide⟩ :=
  accepted_of_selected 12 75811 ⟨574928, by decide⟩ ⟨12, 2, 0, 574928, 75811, 3897, 65536⟩
    (by decide) selected_cut_22609

theorem unmarked_context_11_18952_574929 : frontier 10 ⟨574929, by decide⟩
    (prefixCache 11 18952) (prefixPartial 11 18952) = false := by
  decide +kernel

theorem node_context_11_18952_574929 : EJMOriginalGlobalDAGData.nodes 10 ⟨574929, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨574819, by decide⟩,⟨574874, by decide⟩,⟨574928, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18952_574929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18952 ⟨574929, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18952
    ⟨574929, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨574819, by decide⟩,⟨574874, by decide⟩,⟨574928, by decide⟩]) unmarked_context_11_18952_574929 node_context_11_18952_574929
  intro a
  fin_cases a
  · exact context_12_75808_435790
  · exact context_12_75809_574819
  · exact context_12_75810_574874
  · exact context_12_75811_574928

theorem selected_cut_22610 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 75812) = some ⟨12, 1, 0, 450498, 75812, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75812_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75812 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 75812 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 75812, 1, 65536⟩
    (by decide) selected_cut_22610

theorem selected_cut_22611 : selected 8 ⟨574944, by decide⟩
    (prefixPartial 13 303252) = some ⟨13, 2, 0, 574944, 303252, 945, 16384⟩ := by
  decide +kernel

theorem context_13_303252_574944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303252 ⟨574944, by decide⟩ :=
  accepted_of_selected 13 303252 ⟨574944, by decide⟩ ⟨13, 2, 0, 574944, 303252, 945, 16384⟩
    (by decide) selected_cut_22611

theorem selected_cut_22612 : selected 8 ⟨574963, by decide⟩
    (prefixPartial 13 303253) = some ⟨13, 2, 0, 574963, 303253, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_303253_574963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303253 ⟨574963, by decide⟩ :=
  accepted_of_selected 13 303253 ⟨574963, by decide⟩ ⟨13, 2, 0, 574963, 303253, 1641, 16384⟩
    (by decide) selected_cut_22612

theorem selected_cut_22613 : selected 8 ⟨574979, by decide⟩
    (prefixPartial 13 303254) = some ⟨13, 2, 0, 574979, 303254, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_303254_574979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303254 ⟨574979, by decide⟩ :=
  accepted_of_selected 13 303254 ⟨574979, by decide⟩ ⟨13, 2, 0, 574979, 303254, 1197, 16384⟩
    (by decide) selected_cut_22613

theorem selected_cut_22614 : selected 8 ⟨574984, by decide⟩
    (prefixPartial 13 303255) = some ⟨13, 2, 0, 574984, 303255, 885, 16384⟩ := by
  decide +kernel

theorem context_13_303255_574984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303255 ⟨574984, by decide⟩ :=
  accepted_of_selected 13 303255 ⟨574984, by decide⟩ ⟨13, 2, 0, 574984, 303255, 885, 16384⟩
    (by decide) selected_cut_22614

theorem unmarked_context_12_75813_574985 : frontier 9 ⟨574985, by decide⟩
    (prefixCache 12 75813) (prefixPartial 12 75813) = false := by
  decide +kernel

theorem node_context_12_75813_574985 : EJMOriginalGlobalDAGData.nodes 9 ⟨574985, by decide⟩ =
    .split (coordinate 12) (![⟨574944, by decide⟩,⟨574963, by decide⟩,⟨574979, by decide⟩,⟨574984, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75813_574985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75813 ⟨574985, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75813
    ⟨574985, by decide⟩ (by decide) (![⟨574944, by decide⟩,⟨574963, by decide⟩,⟨574979, by decide⟩,⟨574984, by decide⟩]) unmarked_context_12_75813_574985 node_context_12_75813_574985
  intro a
  fin_cases a
  · exact context_13_303252_574944
  · exact context_13_303253_574963
  · exact context_13_303254_574979
  · exact context_13_303255_574984

theorem selected_cut_22615 : selected 8 ⟨575002, by decide⟩
    (prefixPartial 13 303256) = some ⟨13, 2, 0, 575002, 303256, 925, 16384⟩ := by
  decide +kernel

theorem context_13_303256_575002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303256 ⟨575002, by decide⟩ :=
  accepted_of_selected 13 303256 ⟨575002, by decide⟩ ⟨13, 2, 0, 575002, 303256, 925, 16384⟩
    (by decide) selected_cut_22615

theorem selected_cut_22616 : selected 8 ⟨575030, by decide⟩
    (prefixPartial 13 303257) = some ⟨13, 2, 0, 575030, 303257, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_303257_575030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303257 ⟨575030, by decide⟩ :=
  accepted_of_selected 13 303257 ⟨575030, by decide⟩ ⟨13, 2, 0, 575030, 303257, 2005, 16384⟩
    (by decide) selected_cut_22616

theorem selected_cut_22617 : selected 8 ⟨575050, by decide⟩
    (prefixPartial 13 303258) = some ⟨13, 2, 0, 575050, 303258, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_303258_575050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303258 ⟨575050, by decide⟩ :=
  accepted_of_selected 13 303258 ⟨575050, by decide⟩ ⟨13, 2, 0, 575050, 303258, 1237, 16384⟩
    (by decide) selected_cut_22617

theorem selected_cut_22618 : selected 8 ⟨575054, by decide⟩
    (prefixPartial 13 303259) = some ⟨13, 2, 0, 575054, 303259, 861, 16384⟩ := by
  decide +kernel

theorem context_13_303259_575054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303259 ⟨575054, by decide⟩ :=
  accepted_of_selected 13 303259 ⟨575054, by decide⟩ ⟨13, 2, 0, 575054, 303259, 861, 16384⟩
    (by decide) selected_cut_22618

theorem unmarked_context_12_75814_575055 : frontier 9 ⟨575055, by decide⟩
    (prefixCache 12 75814) (prefixPartial 12 75814) = false := by
  decide +kernel

theorem node_context_12_75814_575055 : EJMOriginalGlobalDAGData.nodes 9 ⟨575055, by decide⟩ =
    .split (coordinate 12) (![⟨575002, by decide⟩,⟨575030, by decide⟩,⟨575050, by decide⟩,⟨575054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75814_575055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75814 ⟨575055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75814
    ⟨575055, by decide⟩ (by decide) (![⟨575002, by decide⟩,⟨575030, by decide⟩,⟨575050, by decide⟩,⟨575054, by decide⟩]) unmarked_context_12_75814_575055 node_context_12_75814_575055
  intro a
  fin_cases a
  · exact context_13_303256_575002
  · exact context_13_303257_575030
  · exact context_13_303258_575050
  · exact context_13_303259_575054

theorem selected_cut_22619 : selected 8 ⟨575071, by decide⟩
    (prefixPartial 13 303260) = some ⟨13, 2, 0, 575071, 303260, 961, 16384⟩ := by
  decide +kernel

theorem context_13_303260_575071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303260 ⟨575071, by decide⟩ :=
  accepted_of_selected 13 303260 ⟨575071, by decide⟩ ⟨13, 2, 0, 575071, 303260, 961, 16384⟩
    (by decide) selected_cut_22619

theorem selected_cut_22620 : selected 8 ⟨575096, by decide⟩
    (prefixPartial 13 303261) = some ⟨13, 2, 0, 575096, 303261, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_303261_575096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303261 ⟨575096, by decide⟩ :=
  accepted_of_selected 13 303261 ⟨575096, by decide⟩ ⟨13, 2, 0, 575096, 303261, 2061, 16384⟩
    (by decide) selected_cut_22620

theorem selected_cut_22621 : selected 8 ⟨575113, by decide⟩
    (prefixPartial 13 303262) = some ⟨13, 2, 0, 575113, 303262, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_303262_575113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303262 ⟨575113, by decide⟩ :=
  accepted_of_selected 13 303262 ⟨575113, by decide⟩ ⟨13, 2, 0, 575113, 303262, 1177, 16384⟩
    (by decide) selected_cut_22621

theorem selected_cut_22622 : selected 8 ⟨575118, by decide⟩
    (prefixPartial 13 303263) = some ⟨13, 2, 0, 575118, 303263, 777, 16384⟩ := by
  decide +kernel

theorem context_13_303263_575118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303263 ⟨575118, by decide⟩ :=
  accepted_of_selected 13 303263 ⟨575118, by decide⟩ ⟨13, 2, 0, 575118, 303263, 777, 16384⟩
    (by decide) selected_cut_22622

theorem unmarked_context_12_75815_575119 : frontier 9 ⟨575119, by decide⟩
    (prefixCache 12 75815) (prefixPartial 12 75815) = false := by
  decide +kernel

theorem node_context_12_75815_575119 : EJMOriginalGlobalDAGData.nodes 9 ⟨575119, by decide⟩ =
    .split (coordinate 12) (![⟨575071, by decide⟩,⟨575096, by decide⟩,⟨575113, by decide⟩,⟨575118, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75815_575119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75815 ⟨575119, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75815
    ⟨575119, by decide⟩ (by decide) (![⟨575071, by decide⟩,⟨575096, by decide⟩,⟨575113, by decide⟩,⟨575118, by decide⟩]) unmarked_context_12_75815_575119 node_context_12_75815_575119
  intro a
  fin_cases a
  · exact context_13_303260_575071
  · exact context_13_303261_575096
  · exact context_13_303262_575113
  · exact context_13_303263_575118

theorem unmarked_context_11_18953_575120 : frontier 10 ⟨575120, by decide⟩
    (prefixCache 11 18953) (prefixPartial 11 18953) = false := by
  decide +kernel

theorem node_context_11_18953_575120 : EJMOriginalGlobalDAGData.nodes 10 ⟨575120, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨574985, by decide⟩,⟨575055, by decide⟩,⟨575119, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18953_575120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18953 ⟨575120, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18953
    ⟨575120, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨574985, by decide⟩,⟨575055, by decide⟩,⟨575119, by decide⟩]) unmarked_context_11_18953_575120 node_context_11_18953_575120
  intro a
  fin_cases a
  · exact context_12_75812_450498
  · exact context_12_75813_574985
  · exact context_12_75814_575055
  · exact context_12_75815_575119

theorem selected_cut_22623 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 75816) = some ⟨12, 1, 0, 435790, 75816, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75816_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75816 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 75816 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 75816, 1, 65536⟩
    (by decide) selected_cut_22623

theorem selected_cut_22624 : selected 8 ⟨575142, by decide⟩
    (prefixPartial 13 303268) = some ⟨13, 2, 0, 575142, 303268, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_303268_575142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303268 ⟨575142, by decide⟩ :=
  accepted_of_selected 13 303268 ⟨575142, by decide⟩ ⟨13, 2, 0, 575142, 303268, 1189, 16384⟩
    (by decide) selected_cut_22624

theorem selected_cut_22625 : selected 8 ⟨575171, by decide⟩
    (prefixPartial 13 303269) = some ⟨13, 2, 0, 575171, 303269, 2369, 16384⟩ := by
  decide +kernel

theorem context_13_303269_575171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303269 ⟨575171, by decide⟩ :=
  accepted_of_selected 13 303269 ⟨575171, by decide⟩ ⟨13, 2, 0, 575171, 303269, 2369, 16384⟩
    (by decide) selected_cut_22625

theorem selected_cut_22626 : selected 8 ⟨575189, by decide⟩
    (prefixPartial 13 303270) = some ⟨13, 2, 0, 575189, 303270, 1765, 16384⟩ := by
  decide +kernel

theorem context_13_303270_575189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303270 ⟨575189, by decide⟩ :=
  accepted_of_selected 13 303270 ⟨575189, by decide⟩ ⟨13, 2, 0, 575189, 303270, 1765, 16384⟩
    (by decide) selected_cut_22626

theorem selected_cut_22627 : selected 8 ⟨575198, by decide⟩
    (prefixPartial 13 303271) = some ⟨13, 2, 0, 575198, 303271, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_303271_575198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303271 ⟨575198, by decide⟩ :=
  accepted_of_selected 13 303271 ⟨575198, by decide⟩ ⟨13, 2, 0, 575198, 303271, 1145, 16384⟩
    (by decide) selected_cut_22627

theorem unmarked_context_12_75817_575199 : frontier 9 ⟨575199, by decide⟩
    (prefixCache 12 75817) (prefixPartial 12 75817) = false := by
  decide +kernel

theorem node_context_12_75817_575199 : EJMOriginalGlobalDAGData.nodes 9 ⟨575199, by decide⟩ =
    .split (coordinate 12) (![⟨575142, by decide⟩,⟨575171, by decide⟩,⟨575189, by decide⟩,⟨575198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75817_575199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75817 ⟨575199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75817
    ⟨575199, by decide⟩ (by decide) (![⟨575142, by decide⟩,⟨575171, by decide⟩,⟨575189, by decide⟩,⟨575198, by decide⟩]) unmarked_context_12_75817_575199 node_context_12_75817_575199
  intro a
  fin_cases a
  · exact context_13_303268_575142
  · exact context_13_303269_575171
  · exact context_13_303270_575189
  · exact context_13_303271_575198

theorem selected_cut_22628 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 75818) = some ⟨12, 1, 0, 474208, 75818, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75818_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75818 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 75818 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 75818, 1, 65536⟩
    (by decide) selected_cut_22628

theorem selected_cut_22629 : selected 8 ⟨575214, by decide⟩
    (prefixPartial 13 303276) = some ⟨13, 2, 0, 575214, 303276, 989, 16384⟩ := by
  decide +kernel

theorem context_13_303276_575214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303276 ⟨575214, by decide⟩ :=
  accepted_of_selected 13 303276 ⟨575214, by decide⟩ ⟨13, 2, 0, 575214, 303276, 989, 16384⟩
    (by decide) selected_cut_22629

theorem selected_cut_22630 : selected 8 ⟨575245, by decide⟩
    (prefixPartial 13 303277) = some ⟨13, 2, 0, 575245, 303277, 2909, 16384⟩ := by
  decide +kernel

theorem context_13_303277_575245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303277 ⟨575245, by decide⟩ :=
  accepted_of_selected 13 303277 ⟨575245, by decide⟩ ⟨13, 2, 0, 575245, 303277, 2909, 16384⟩
    (by decide) selected_cut_22630

theorem selected_cut_22631 : selected 8 ⟨575264, by decide⟩
    (prefixPartial 13 303278) = some ⟨13, 2, 0, 575264, 303278, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_303278_575264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303278 ⟨575264, by decide⟩ :=
  accepted_of_selected 13 303278 ⟨575264, by decide⟩ ⟨13, 2, 0, 575264, 303278, 1509, 16384⟩
    (by decide) selected_cut_22631

theorem selected_cut_22632 : selected 8 ⟨575272, by decide⟩
    (prefixPartial 13 303279) = some ⟨13, 2, 0, 575272, 303279, 945, 16384⟩ := by
  decide +kernel

theorem context_13_303279_575272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303279 ⟨575272, by decide⟩ :=
  accepted_of_selected 13 303279 ⟨575272, by decide⟩ ⟨13, 2, 0, 575272, 303279, 945, 16384⟩
    (by decide) selected_cut_22632

theorem unmarked_context_12_75819_575273 : frontier 9 ⟨575273, by decide⟩
    (prefixCache 12 75819) (prefixPartial 12 75819) = false := by
  decide +kernel

theorem node_context_12_75819_575273 : EJMOriginalGlobalDAGData.nodes 9 ⟨575273, by decide⟩ =
    .split (coordinate 12) (![⟨575214, by decide⟩,⟨575245, by decide⟩,⟨575264, by decide⟩,⟨575272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75819_575273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75819 ⟨575273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75819
    ⟨575273, by decide⟩ (by decide) (![⟨575214, by decide⟩,⟨575245, by decide⟩,⟨575264, by decide⟩,⟨575272, by decide⟩]) unmarked_context_12_75819_575273 node_context_12_75819_575273
  intro a
  fin_cases a
  · exact context_13_303276_575214
  · exact context_13_303277_575245
  · exact context_13_303278_575264
  · exact context_13_303279_575272

theorem unmarked_context_11_18954_575274 : frontier 10 ⟨575274, by decide⟩
    (prefixCache 11 18954) (prefixPartial 11 18954) = false := by
  decide +kernel

theorem node_context_11_18954_575274 : EJMOriginalGlobalDAGData.nodes 10 ⟨575274, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨575199, by decide⟩,⟨474208, by decide⟩,⟨575273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18954_575274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18954 ⟨575274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18954
    ⟨575274, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨575199, by decide⟩,⟨474208, by decide⟩,⟨575273, by decide⟩]) unmarked_context_11_18954_575274 node_context_11_18954_575274
  intro a
  fin_cases a
  · exact context_12_75816_435790
  · exact context_12_75817_575199
  · exact context_12_75818_474208
  · exact context_12_75819_575273

theorem selected_cut_22633 : selected 9 ⟨540189, by decide⟩
    (prefixPartial 12 75820) = some ⟨12, 1, 0, 540189, 75820, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75820_540189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75820 ⟨540189, by decide⟩ :=
  accepted_of_selected 12 75820 ⟨540189, by decide⟩ ⟨12, 1, 0, 540189, 75820, 1, 65536⟩
    (by decide) selected_cut_22633

theorem selected_cut_22634 : selected 8 ⟨575289, by decide⟩
    (prefixPartial 13 303284) = some ⟨13, 2, 0, 575289, 303284, 741, 16384⟩ := by
  decide +kernel

theorem context_13_303284_575289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303284 ⟨575289, by decide⟩ :=
  accepted_of_selected 13 303284 ⟨575289, by decide⟩ ⟨13, 2, 0, 575289, 303284, 741, 16384⟩
    (by decide) selected_cut_22634

theorem selected_cut_22635 : selected 8 ⟨575310, by decide⟩
    (prefixPartial 13 303285) = some ⟨13, 2, 0, 575310, 303285, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_303285_575310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303285 ⟨575310, by decide⟩ :=
  accepted_of_selected 13 303285 ⟨575310, by decide⟩ ⟨13, 2, 0, 575310, 303285, 2153, 16384⟩
    (by decide) selected_cut_22635

theorem selected_cut_22636 : selected 8 ⟨575329, by decide⟩
    (prefixPartial 13 303286) = some ⟨13, 2, 0, 575329, 303286, 1445, 16384⟩ := by
  decide +kernel

theorem context_13_303286_575329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303286 ⟨575329, by decide⟩ :=
  accepted_of_selected 13 303286 ⟨575329, by decide⟩ ⟨13, 2, 0, 575329, 303286, 1445, 16384⟩
    (by decide) selected_cut_22636

theorem selected_cut_22637 : selected 8 ⟨575335, by decide⟩
    (prefixPartial 13 303287) = some ⟨13, 2, 0, 575335, 303287, 841, 16384⟩ := by
  decide +kernel

theorem context_13_303287_575335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303287 ⟨575335, by decide⟩ :=
  accepted_of_selected 13 303287 ⟨575335, by decide⟩ ⟨13, 2, 0, 575335, 303287, 841, 16384⟩
    (by decide) selected_cut_22637

theorem unmarked_context_12_75821_575336 : frontier 9 ⟨575336, by decide⟩
    (prefixCache 12 75821) (prefixPartial 12 75821) = false := by
  decide +kernel

theorem node_context_12_75821_575336 : EJMOriginalGlobalDAGData.nodes 9 ⟨575336, by decide⟩ =
    .split (coordinate 12) (![⟨575289, by decide⟩,⟨575310, by decide⟩,⟨575329, by decide⟩,⟨575335, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75821_575336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75821 ⟨575336, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75821
    ⟨575336, by decide⟩ (by decide) (![⟨575289, by decide⟩,⟨575310, by decide⟩,⟨575329, by decide⟩,⟨575335, by decide⟩]) unmarked_context_12_75821_575336 node_context_12_75821_575336
  intro a
  fin_cases a
  · exact context_13_303284_575289
  · exact context_13_303285_575310
  · exact context_13_303286_575329
  · exact context_13_303287_575335

theorem selected_cut_22638 : selected 8 ⟨575348, by decide⟩
    (prefixPartial 13 303288) = some ⟨13, 2, 0, 575348, 303288, 581, 16384⟩ := by
  decide +kernel

theorem context_13_303288_575348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303288 ⟨575348, by decide⟩ :=
  accepted_of_selected 13 303288 ⟨575348, by decide⟩ ⟨13, 2, 0, 575348, 303288, 581, 16384⟩
    (by decide) selected_cut_22638

theorem selected_cut_22639 : selected 8 ⟨575375, by decide⟩
    (prefixPartial 13 303289) = some ⟨13, 2, 0, 575375, 303289, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_303289_575375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303289 ⟨575375, by decide⟩ :=
  accepted_of_selected 13 303289 ⟨575375, by decide⟩ ⟨13, 2, 0, 575375, 303289, 2325, 16384⟩
    (by decide) selected_cut_22639

theorem selected_cut_22640 : selected 8 ⟨575397, by decide⟩
    (prefixPartial 13 303290) = some ⟨13, 2, 0, 575397, 303290, 1341, 16384⟩ := by
  decide +kernel

theorem context_13_303290_575397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303290 ⟨575397, by decide⟩ :=
  accepted_of_selected 13 303290 ⟨575397, by decide⟩ ⟨13, 2, 0, 575397, 303290, 1341, 16384⟩
    (by decide) selected_cut_22640

theorem selected_cut_22641 : selected 8 ⟨575404, by decide⟩
    (prefixPartial 13 303291) = some ⟨13, 2, 0, 575404, 303291, 837, 16384⟩ := by
  decide +kernel

theorem context_13_303291_575404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303291 ⟨575404, by decide⟩ :=
  accepted_of_selected 13 303291 ⟨575404, by decide⟩ ⟨13, 2, 0, 575404, 303291, 837, 16384⟩
    (by decide) selected_cut_22641

theorem unmarked_context_12_75822_575405 : frontier 9 ⟨575405, by decide⟩
    (prefixCache 12 75822) (prefixPartial 12 75822) = false := by
  decide +kernel

theorem node_context_12_75822_575405 : EJMOriginalGlobalDAGData.nodes 9 ⟨575405, by decide⟩ =
    .split (coordinate 12) (![⟨575348, by decide⟩,⟨575375, by decide⟩,⟨575397, by decide⟩,⟨575404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75822_575405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75822 ⟨575405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75822
    ⟨575405, by decide⟩ (by decide) (![⟨575348, by decide⟩,⟨575375, by decide⟩,⟨575397, by decide⟩,⟨575404, by decide⟩]) unmarked_context_12_75822_575405 node_context_12_75822_575405
  intro a
  fin_cases a
  · exact context_13_303288_575348
  · exact context_13_303289_575375
  · exact context_13_303290_575397
  · exact context_13_303291_575404

theorem selected_cut_22642 : selected 8 ⟨575416, by decide⟩
    (prefixPartial 13 303292) = some ⟨13, 2, 0, 575416, 303292, 517, 16384⟩ := by
  decide +kernel

theorem context_13_303292_575416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303292 ⟨575416, by decide⟩ :=
  accepted_of_selected 13 303292 ⟨575416, by decide⟩ ⟨13, 2, 0, 575416, 303292, 517, 16384⟩
    (by decide) selected_cut_22642

theorem selected_cut_22643 : selected 8 ⟨575444, by decide⟩
    (prefixPartial 13 303293) = some ⟨13, 2, 0, 575444, 303293, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_303293_575444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303293 ⟨575444, by decide⟩ :=
  accepted_of_selected 13 303293 ⟨575444, by decide⟩ ⟨13, 2, 0, 575444, 303293, 2345, 16384⟩
    (by decide) selected_cut_22643

theorem selected_cut_22644 : selected 8 ⟨575463, by decide⟩
    (prefixPartial 13 303294) = some ⟨13, 2, 0, 575463, 303294, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_303294_575463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303294 ⟨575463, by decide⟩ :=
  accepted_of_selected 13 303294 ⟨575463, by decide⟩ ⟨13, 2, 0, 575463, 303294, 1209, 16384⟩
    (by decide) selected_cut_22644

theorem selected_cut_22645 : selected 8 ⟨575466, by decide⟩
    (prefixPartial 13 303295) = some ⟨13, 2, 0, 575466, 303295, 725, 16384⟩ := by
  decide +kernel

theorem context_13_303295_575466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303295 ⟨575466, by decide⟩ :=
  accepted_of_selected 13 303295 ⟨575466, by decide⟩ ⟨13, 2, 0, 575466, 303295, 725, 16384⟩
    (by decide) selected_cut_22645

theorem unmarked_context_12_75823_575467 : frontier 9 ⟨575467, by decide⟩
    (prefixCache 12 75823) (prefixPartial 12 75823) = false := by
  decide +kernel

theorem node_context_12_75823_575467 : EJMOriginalGlobalDAGData.nodes 9 ⟨575467, by decide⟩ =
    .split (coordinate 12) (![⟨575416, by decide⟩,⟨575444, by decide⟩,⟨575463, by decide⟩,⟨575466, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75823_575467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75823 ⟨575467, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75823
    ⟨575467, by decide⟩ (by decide) (![⟨575416, by decide⟩,⟨575444, by decide⟩,⟨575463, by decide⟩,⟨575466, by decide⟩]) unmarked_context_12_75823_575467 node_context_12_75823_575467
  intro a
  fin_cases a
  · exact context_13_303292_575416
  · exact context_13_303293_575444
  · exact context_13_303294_575463
  · exact context_13_303295_575466

theorem unmarked_context_11_18955_575468 : frontier 10 ⟨575468, by decide⟩
    (prefixCache 11 18955) (prefixPartial 11 18955) = false := by
  decide +kernel

theorem node_context_11_18955_575468 : EJMOriginalGlobalDAGData.nodes 10 ⟨575468, by decide⟩ =
    .split (coordinate 11) (![⟨540189, by decide⟩,⟨575336, by decide⟩,⟨575405, by decide⟩,⟨575467, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18955_575468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18955 ⟨575468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18955
    ⟨575468, by decide⟩ (by decide) (![⟨540189, by decide⟩,⟨575336, by decide⟩,⟨575405, by decide⟩,⟨575467, by decide⟩]) unmarked_context_11_18955_575468 node_context_11_18955_575468
  intro a
  fin_cases a
  · exact context_12_75820_540189
  · exact context_12_75821_575336
  · exact context_12_75822_575405
  · exact context_12_75823_575467

theorem unmarked_context_10_4738_575469 : frontier 11 ⟨575469, by decide⟩
    (prefixCache 10 4738) (prefixPartial 10 4738) = false := by
  decide +kernel

theorem node_context_10_4738_575469 : EJMOriginalGlobalDAGData.nodes 11 ⟨575469, by decide⟩ =
    .split (coordinate 10) (![⟨574929, by decide⟩,⟨575120, by decide⟩,⟨575274, by decide⟩,⟨575468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4738_575469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4738 ⟨575469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4738
    ⟨575469, by decide⟩ (by decide) (![⟨574929, by decide⟩,⟨575120, by decide⟩,⟨575274, by decide⟩,⟨575468, by decide⟩]) unmarked_context_10_4738_575469 node_context_10_4738_575469
  intro a
  fin_cases a
  · exact context_11_18952_574929
  · exact context_11_18953_575120
  · exact context_11_18954_575274
  · exact context_11_18955_575468

theorem selected_cut_22646 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 75824) = some ⟨12, 1, 0, 445562, 75824, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75824_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75824 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 75824 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 75824, 1, 65536⟩
    (by decide) selected_cut_22646

theorem selected_cut_22647 : selected 8 ⟨575476, by decide⟩
    (prefixPartial 13 303300) = some ⟨13, 2, 0, 575476, 303300, 461, 16384⟩ := by
  decide +kernel

theorem context_13_303300_575476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303300 ⟨575476, by decide⟩ :=
  accepted_of_selected 13 303300 ⟨575476, by decide⟩ ⟨13, 2, 0, 575476, 303300, 461, 16384⟩
    (by decide) selected_cut_22647

theorem selected_cut_22648 : selected 8 ⟨575500, by decide⟩
    (prefixPartial 13 303301) = some ⟨13, 2, 0, 575500, 303301, 1909, 16384⟩ := by
  decide +kernel

theorem context_13_303301_575500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303301 ⟨575500, by decide⟩ :=
  accepted_of_selected 13 303301 ⟨575500, by decide⟩ ⟨13, 2, 0, 575500, 303301, 1909, 16384⟩
    (by decide) selected_cut_22648

theorem selected_cut_22649 : selected 8 ⟨575518, by decide⟩
    (prefixPartial 13 303302) = some ⟨13, 2, 0, 575518, 303302, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_303302_575518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303302 ⟨575518, by decide⟩ :=
  accepted_of_selected 13 303302 ⟨575518, by decide⟩ ⟨13, 2, 0, 575518, 303302, 1249, 16384⟩
    (by decide) selected_cut_22649

theorem selected_cut_22650 : selected 8 ⟨575524, by decide⟩
    (prefixPartial 13 303303) = some ⟨13, 2, 0, 575524, 303303, 849, 16384⟩ := by
  decide +kernel

theorem context_13_303303_575524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303303 ⟨575524, by decide⟩ :=
  accepted_of_selected 13 303303 ⟨575524, by decide⟩ ⟨13, 2, 0, 575524, 303303, 849, 16384⟩
    (by decide) selected_cut_22650

theorem unmarked_context_12_75825_575525 : frontier 9 ⟨575525, by decide⟩
    (prefixCache 12 75825) (prefixPartial 12 75825) = false := by
  decide +kernel

theorem node_context_12_75825_575525 : EJMOriginalGlobalDAGData.nodes 9 ⟨575525, by decide⟩ =
    .split (coordinate 12) (![⟨575476, by decide⟩,⟨575500, by decide⟩,⟨575518, by decide⟩,⟨575524, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75825_575525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75825 ⟨575525, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75825
    ⟨575525, by decide⟩ (by decide) (![⟨575476, by decide⟩,⟨575500, by decide⟩,⟨575518, by decide⟩,⟨575524, by decide⟩]) unmarked_context_12_75825_575525 node_context_12_75825_575525
  intro a
  fin_cases a
  · exact context_13_303300_575476
  · exact context_13_303301_575500
  · exact context_13_303302_575518
  · exact context_13_303303_575524

theorem selected_cut_22651 : selected 8 ⟨575534, by decide⟩
    (prefixPartial 13 303304) = some ⟨13, 2, 0, 575534, 303304, 485, 16384⟩ := by
  decide +kernel

theorem context_13_303304_575534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303304 ⟨575534, by decide⟩ :=
  accepted_of_selected 13 303304 ⟨575534, by decide⟩ ⟨13, 2, 0, 575534, 303304, 485, 16384⟩
    (by decide) selected_cut_22651

theorem selected_cut_22652 : selected 8 ⟨575555, by decide⟩
    (prefixPartial 13 303305) = some ⟨13, 2, 0, 575555, 303305, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_303305_575555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303305 ⟨575555, by decide⟩ :=
  accepted_of_selected 13 303305 ⟨575555, by decide⟩ ⟨13, 2, 0, 575555, 303305, 1865, 16384⟩
    (by decide) selected_cut_22652

theorem selected_cut_22653 : selected 8 ⟨575575, by decide⟩
    (prefixPartial 13 303306) = some ⟨13, 2, 0, 575575, 303306, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_303306_575575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303306 ⟨575575, by decide⟩ :=
  accepted_of_selected 13 303306 ⟨575575, by decide⟩ ⟨13, 2, 0, 575575, 303306, 1261, 16384⟩
    (by decide) selected_cut_22653

theorem selected_cut_22654 : selected 8 ⟨575579, by decide⟩
    (prefixPartial 13 303307) = some ⟨13, 2, 0, 575579, 303307, 737, 16384⟩ := by
  decide +kernel

theorem context_13_303307_575579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303307 ⟨575579, by decide⟩ :=
  accepted_of_selected 13 303307 ⟨575579, by decide⟩ ⟨13, 2, 0, 575579, 303307, 737, 16384⟩
    (by decide) selected_cut_22654

theorem unmarked_context_12_75826_575580 : frontier 9 ⟨575580, by decide⟩
    (prefixCache 12 75826) (prefixPartial 12 75826) = false := by
  decide +kernel

theorem node_context_12_75826_575580 : EJMOriginalGlobalDAGData.nodes 9 ⟨575580, by decide⟩ =
    .split (coordinate 12) (![⟨575534, by decide⟩,⟨575555, by decide⟩,⟨575575, by decide⟩,⟨575579, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75826_575580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75826 ⟨575580, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75826
    ⟨575580, by decide⟩ (by decide) (![⟨575534, by decide⟩,⟨575555, by decide⟩,⟨575575, by decide⟩,⟨575579, by decide⟩]) unmarked_context_12_75826_575580 node_context_12_75826_575580
  intro a
  fin_cases a
  · exact context_13_303304_575534
  · exact context_13_303305_575555
  · exact context_13_303306_575575
  · exact context_13_303307_575579

theorem selected_cut_22655 : selected 8 ⟨575589, by decide⟩
    (prefixPartial 13 303308) = some ⟨13, 2, 0, 575589, 303308, 397, 16384⟩ := by
  decide +kernel

theorem context_13_303308_575589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303308 ⟨575589, by decide⟩ :=
  accepted_of_selected 13 303308 ⟨575589, by decide⟩ ⟨13, 2, 0, 575589, 303308, 397, 16384⟩
    (by decide) selected_cut_22655

theorem selected_cut_22656 : selected 8 ⟨575619, by decide⟩
    (prefixPartial 13 303309) = some ⟨13, 2, 0, 575619, 303309, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_303309_575619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303309 ⟨575619, by decide⟩ :=
  accepted_of_selected 13 303309 ⟨575619, by decide⟩ ⟨13, 2, 0, 575619, 303309, 2013, 16384⟩
    (by decide) selected_cut_22656

theorem selected_cut_22657 : selected 8 ⟨575637, by decide⟩
    (prefixPartial 13 303310) = some ⟨13, 2, 0, 575637, 303310, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_303310_575637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303310 ⟨575637, by decide⟩ :=
  accepted_of_selected 13 303310 ⟨575637, by decide⟩ ⟨13, 2, 0, 575637, 303310, 1217, 16384⟩
    (by decide) selected_cut_22657

theorem selected_cut_22658 : selected 8 ⟨575643, by decide⟩
    (prefixPartial 13 303311) = some ⟨13, 2, 0, 575643, 303311, 637, 16384⟩ := by
  decide +kernel

theorem context_13_303311_575643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 303311 ⟨575643, by decide⟩ :=
  accepted_of_selected 13 303311 ⟨575643, by decide⟩ ⟨13, 2, 0, 575643, 303311, 637, 16384⟩
    (by decide) selected_cut_22658

theorem unmarked_context_12_75827_575644 : frontier 9 ⟨575644, by decide⟩
    (prefixCache 12 75827) (prefixPartial 12 75827) = false := by
  decide +kernel

theorem node_context_12_75827_575644 : EJMOriginalGlobalDAGData.nodes 9 ⟨575644, by decide⟩ =
    .split (coordinate 12) (![⟨575589, by decide⟩,⟨575619, by decide⟩,⟨575637, by decide⟩,⟨575643, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75827_575644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75827 ⟨575644, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75827
    ⟨575644, by decide⟩ (by decide) (![⟨575589, by decide⟩,⟨575619, by decide⟩,⟨575637, by decide⟩,⟨575643, by decide⟩]) unmarked_context_12_75827_575644 node_context_12_75827_575644
  intro a
  fin_cases a
  · exact context_13_303308_575589
  · exact context_13_303309_575619
  · exact context_13_303310_575637
  · exact context_13_303311_575643

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
