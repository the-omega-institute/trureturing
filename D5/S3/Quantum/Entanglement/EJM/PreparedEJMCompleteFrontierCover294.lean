/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover293
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_92190_712342 : frontier 9 ⟨712342, by decide⟩
    (prefixCache 12 92190) (prefixPartial 12 92190) = false := by
  decide +kernel

theorem node_context_12_92190_712342 : EJMOriginalGlobalDAGData.nodes 9 ⟨712342, by decide⟩ =
    .split (coordinate 12) (![⟨712295, by decide⟩,⟨712319, by decide⟩,⟨712336, by decide⟩,⟨712341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92190_712342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92190 ⟨712342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92190
    ⟨712342, by decide⟩ (by decide) (![⟨712295, by decide⟩,⟨712319, by decide⟩,⟨712336, by decide⟩,⟨712341, by decide⟩]) unmarked_context_12_92190_712342 node_context_12_92190_712342
  intro a
  fin_cases a
  · exact context_13_368760_712295
  · exact context_13_368761_712319
  · exact context_13_368762_712336
  · exact context_13_368763_712341

theorem selected_cut_28228 : selected 8 ⟨712362, by decide⟩
    (prefixPartial 13 368764) = some ⟨13, 2, 0, 712362, 368764, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_368764_712362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368764 ⟨712362, by decide⟩ :=
  accepted_of_selected 13 368764 ⟨712362, by decide⟩ ⟨13, 2, 0, 712362, 368764, 1125, 16384⟩
    (by decide) selected_cut_28228

theorem selected_cut_28229 : selected 8 ⟨712390, by decide⟩
    (prefixPartial 13 368765) = some ⟨13, 2, 0, 712390, 368765, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_368765_712390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368765 ⟨712390, by decide⟩ :=
  accepted_of_selected 13 368765 ⟨712390, by decide⟩ ⟨13, 2, 0, 712390, 368765, 1749, 16384⟩
    (by decide) selected_cut_28229

theorem selected_cut_28230 : selected 8 ⟨712406, by decide⟩
    (prefixPartial 13 368766) = some ⟨13, 2, 0, 712406, 368766, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_368766_712406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368766 ⟨712406, by decide⟩ :=
  accepted_of_selected 13 368766 ⟨712406, by decide⟩ ⟨13, 2, 0, 712406, 368766, 1045, 16384⟩
    (by decide) selected_cut_28230

theorem selected_cut_28231 : selected 8 ⟨712411, by decide⟩
    (prefixPartial 13 368767) = some ⟨13, 2, 0, 712411, 368767, 745, 16384⟩ := by
  decide +kernel

theorem context_13_368767_712411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368767 ⟨712411, by decide⟩ :=
  accepted_of_selected 13 368767 ⟨712411, by decide⟩ ⟨13, 2, 0, 712411, 368767, 745, 16384⟩
    (by decide) selected_cut_28231

theorem unmarked_context_12_92191_712412 : frontier 9 ⟨712412, by decide⟩
    (prefixCache 12 92191) (prefixPartial 12 92191) = false := by
  decide +kernel

theorem node_context_12_92191_712412 : EJMOriginalGlobalDAGData.nodes 9 ⟨712412, by decide⟩ =
    .split (coordinate 12) (![⟨712362, by decide⟩,⟨712390, by decide⟩,⟨712406, by decide⟩,⟨712411, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92191_712412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92191 ⟨712412, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92191
    ⟨712412, by decide⟩ (by decide) (![⟨712362, by decide⟩,⟨712390, by decide⟩,⟨712406, by decide⟩,⟨712411, by decide⟩]) unmarked_context_12_92191_712412 node_context_12_92191_712412
  intro a
  fin_cases a
  · exact context_13_368764_712362
  · exact context_13_368765_712390
  · exact context_13_368766_712406
  · exact context_13_368767_712411

theorem unmarked_context_11_23047_712413 : frontier 10 ⟨712413, by decide⟩
    (prefixCache 11 23047) (prefixPartial 11 23047) = false := by
  decide +kernel

theorem node_context_11_23047_712413 : EJMOriginalGlobalDAGData.nodes 10 ⟨712413, by decide⟩ =
    .split (coordinate 11) (![⟨712198, by decide⟩,⟨712277, by decide⟩,⟨712342, by decide⟩,⟨712412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23047_712413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23047 ⟨712413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23047
    ⟨712413, by decide⟩ (by decide) (![⟨712198, by decide⟩,⟨712277, by decide⟩,⟨712342, by decide⟩,⟨712412, by decide⟩]) unmarked_context_11_23047_712413 node_context_11_23047_712413
  intro a
  fin_cases a
  · exact context_12_92188_712198
  · exact context_12_92189_712277
  · exact context_12_92190_712342
  · exact context_12_92191_712412

theorem unmarked_context_10_5761_712414 : frontier 11 ⟨712414, by decide⟩
    (prefixCache 10 5761) (prefixPartial 10 5761) = false := by
  decide +kernel

theorem node_context_10_5761_712414 : EJMOriginalGlobalDAGData.nodes 11 ⟨712414, by decide⟩ =
    .split (coordinate 10) (![⟨711537, by decide⟩,⟨711853, by decide⟩,⟨712138, by decide⟩,⟨712413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5761_712414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5761 ⟨712414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5761
    ⟨712414, by decide⟩ (by decide) (![⟨711537, by decide⟩,⟨711853, by decide⟩,⟨712138, by decide⟩,⟨712413, by decide⟩]) unmarked_context_10_5761_712414 node_context_10_5761_712414
  intro a
  fin_cases a
  · exact context_11_23044_711537
  · exact context_11_23045_711853
  · exact context_11_23046_712138
  · exact context_11_23047_712413

theorem selected_cut_28232 : selected 9 ⟨355612, by decide⟩
    (prefixPartial 12 92192) = some ⟨12, 1, 0, 355612, 92192, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92192_355612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92192 ⟨355612, by decide⟩ :=
  accepted_of_selected 12 92192 ⟨355612, by decide⟩ ⟨12, 1, 0, 355612, 92192, 1, 65536⟩
    (by decide) selected_cut_28232

theorem selected_cut_28233 : selected 9 ⟨712506, by decide⟩
    (prefixPartial 12 92193) = some ⟨12, 2, 0, 712506, 92193, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_92193_712506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92193 ⟨712506, by decide⟩ :=
  accepted_of_selected 12 92193 ⟨712506, by decide⟩ ⟨12, 2, 0, 712506, 92193, 3977, 65536⟩
    (by decide) selected_cut_28233

theorem selected_cut_28234 : selected 9 ⟨712586, by decide⟩
    (prefixPartial 12 92194) = some ⟨12, 2, 0, 712586, 92194, 3941, 65536⟩ := by
  decide +kernel

theorem context_12_92194_712586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92194 ⟨712586, by decide⟩ :=
  accepted_of_selected 12 92194 ⟨712586, by decide⟩ ⟨12, 2, 0, 712586, 92194, 3941, 65536⟩
    (by decide) selected_cut_28234

theorem selected_cut_28235 : selected 9 ⟨712667, by decide⟩
    (prefixPartial 12 92195) = some ⟨12, 2, 0, 712667, 92195, 3953, 65536⟩ := by
  decide +kernel

theorem context_12_92195_712667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92195 ⟨712667, by decide⟩ :=
  accepted_of_selected 12 92195 ⟨712667, by decide⟩ ⟨12, 2, 0, 712667, 92195, 3953, 65536⟩
    (by decide) selected_cut_28235

theorem unmarked_context_11_23048_712668 : frontier 10 ⟨712668, by decide⟩
    (prefixCache 11 23048) (prefixPartial 11 23048) = false := by
  decide +kernel

theorem node_context_11_23048_712668 : EJMOriginalGlobalDAGData.nodes 10 ⟨712668, by decide⟩ =
    .split (coordinate 11) (![⟨355612, by decide⟩,⟨712506, by decide⟩,⟨712586, by decide⟩,⟨712667, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23048_712668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23048 ⟨712668, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23048
    ⟨712668, by decide⟩ (by decide) (![⟨355612, by decide⟩,⟨712506, by decide⟩,⟨712586, by decide⟩,⟨712667, by decide⟩]) unmarked_context_11_23048_712668 node_context_11_23048_712668
  intro a
  fin_cases a
  · exact context_12_92192_355612
  · exact context_12_92193_712506
  · exact context_12_92194_712586
  · exact context_12_92195_712667

theorem selected_cut_28236 : selected 9 ⟨712742, by decide⟩
    (prefixPartial 12 92196) = some ⟨12, 2, 0, 712742, 92196, 3909, 65536⟩ := by
  decide +kernel

theorem context_12_92196_712742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92196 ⟨712742, by decide⟩ :=
  accepted_of_selected 12 92196 ⟨712742, by decide⟩ ⟨12, 2, 0, 712742, 92196, 3909, 65536⟩
    (by decide) selected_cut_28236

theorem selected_cut_28237 : selected 9 ⟨712818, by decide⟩
    (prefixPartial 12 92197) = some ⟨12, 2, 0, 712818, 92197, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_92197_712818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92197 ⟨712818, by decide⟩ :=
  accepted_of_selected 12 92197 ⟨712818, by decide⟩ ⟨12, 2, 0, 712818, 92197, 3933, 65536⟩
    (by decide) selected_cut_28237

theorem selected_cut_28238 : selected 8 ⟨712840, by decide⟩
    (prefixPartial 13 368792) = some ⟨13, 2, 0, 712840, 368792, 869, 16384⟩ := by
  decide +kernel

theorem context_13_368792_712840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368792 ⟨712840, by decide⟩ :=
  accepted_of_selected 13 368792 ⟨712840, by decide⟩ ⟨13, 2, 0, 712840, 368792, 869, 16384⟩
    (by decide) selected_cut_28238

theorem selected_cut_28239 : selected 8 ⟨712875, by decide⟩
    (prefixPartial 13 368793) = some ⟨13, 2, 0, 712875, 368793, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_368793_712875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368793 ⟨712875, by decide⟩ :=
  accepted_of_selected 13 368793 ⟨712875, by decide⟩ ⟨13, 2, 0, 712875, 368793, 1417, 16384⟩
    (by decide) selected_cut_28239

theorem selected_cut_28240 : selected 8 ⟨712889, by decide⟩
    (prefixPartial 13 368794) = some ⟨13, 2, 0, 712889, 368794, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_368794_712889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368794 ⟨712889, by decide⟩ :=
  accepted_of_selected 13 368794 ⟨712889, by decide⟩ ⟨13, 2, 0, 712889, 368794, 1109, 16384⟩
    (by decide) selected_cut_28240

theorem selected_cut_28241 : selected 8 ⟨712894, by decide⟩
    (prefixPartial 13 368795) = some ⟨13, 2, 0, 712894, 368795, 845, 16384⟩ := by
  decide +kernel

theorem context_13_368795_712894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368795 ⟨712894, by decide⟩ :=
  accepted_of_selected 13 368795 ⟨712894, by decide⟩ ⟨13, 2, 0, 712894, 368795, 845, 16384⟩
    (by decide) selected_cut_28241

theorem unmarked_context_12_92198_712895 : frontier 9 ⟨712895, by decide⟩
    (prefixCache 12 92198) (prefixPartial 12 92198) = false := by
  decide +kernel

theorem node_context_12_92198_712895 : EJMOriginalGlobalDAGData.nodes 9 ⟨712895, by decide⟩ =
    .split (coordinate 12) (![⟨712840, by decide⟩,⟨712875, by decide⟩,⟨712889, by decide⟩,⟨712894, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92198_712895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92198 ⟨712895, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92198
    ⟨712895, by decide⟩ (by decide) (![⟨712840, by decide⟩,⟨712875, by decide⟩,⟨712889, by decide⟩,⟨712894, by decide⟩]) unmarked_context_12_92198_712895 node_context_12_92198_712895
  intro a
  fin_cases a
  · exact context_13_368792_712840
  · exact context_13_368793_712875
  · exact context_13_368794_712889
  · exact context_13_368795_712894

theorem selected_cut_28242 : selected 8 ⟨712921, by decide⟩
    (prefixPartial 13 368796) = some ⟨13, 2, 0, 712921, 368796, 937, 16384⟩ := by
  decide +kernel

theorem context_13_368796_712921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368796 ⟨712921, by decide⟩ :=
  accepted_of_selected 13 368796 ⟨712921, by decide⟩ ⟨13, 2, 0, 712921, 368796, 937, 16384⟩
    (by decide) selected_cut_28242

theorem selected_cut_28243 : selected 8 ⟨712964, by decide⟩
    (prefixPartial 13 368797) = some ⟨13, 2, 0, 712964, 368797, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_368797_712964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368797 ⟨712964, by decide⟩ :=
  accepted_of_selected 13 368797 ⟨712964, by decide⟩ ⟨13, 2, 0, 712964, 368797, 1525, 16384⟩
    (by decide) selected_cut_28243

theorem selected_cut_28244 : selected 8 ⟨712979, by decide⟩
    (prefixPartial 13 368798) = some ⟨13, 2, 0, 712979, 368798, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_368798_712979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368798 ⟨712979, by decide⟩ :=
  accepted_of_selected 13 368798 ⟨712979, by decide⟩ ⟨13, 2, 0, 712979, 368798, 1113, 16384⟩
    (by decide) selected_cut_28244

theorem selected_cut_28245 : selected 8 ⟨712986, by decide⟩
    (prefixPartial 13 368799) = some ⟨13, 2, 0, 712986, 368799, 853, 16384⟩ := by
  decide +kernel

theorem context_13_368799_712986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368799 ⟨712986, by decide⟩ :=
  accepted_of_selected 13 368799 ⟨712986, by decide⟩ ⟨13, 2, 0, 712986, 368799, 853, 16384⟩
    (by decide) selected_cut_28245

theorem unmarked_context_12_92199_712987 : frontier 9 ⟨712987, by decide⟩
    (prefixCache 12 92199) (prefixPartial 12 92199) = false := by
  decide +kernel

theorem node_context_12_92199_712987 : EJMOriginalGlobalDAGData.nodes 9 ⟨712987, by decide⟩ =
    .split (coordinate 12) (![⟨712921, by decide⟩,⟨712964, by decide⟩,⟨712979, by decide⟩,⟨712986, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92199_712987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92199 ⟨712987, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92199
    ⟨712987, by decide⟩ (by decide) (![⟨712921, by decide⟩,⟨712964, by decide⟩,⟨712979, by decide⟩,⟨712986, by decide⟩]) unmarked_context_12_92199_712987 node_context_12_92199_712987
  intro a
  fin_cases a
  · exact context_13_368796_712921
  · exact context_13_368797_712964
  · exact context_13_368798_712979
  · exact context_13_368799_712986

theorem unmarked_context_11_23049_712988 : frontier 10 ⟨712988, by decide⟩
    (prefixCache 11 23049) (prefixPartial 11 23049) = false := by
  decide +kernel

theorem node_context_11_23049_712988 : EJMOriginalGlobalDAGData.nodes 10 ⟨712988, by decide⟩ =
    .split (coordinate 11) (![⟨712742, by decide⟩,⟨712818, by decide⟩,⟨712895, by decide⟩,⟨712987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23049_712988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23049 ⟨712988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23049
    ⟨712988, by decide⟩ (by decide) (![⟨712742, by decide⟩,⟨712818, by decide⟩,⟨712895, by decide⟩,⟨712987, by decide⟩]) unmarked_context_11_23049_712988 node_context_11_23049_712988
  intro a
  fin_cases a
  · exact context_12_92196_712742
  · exact context_12_92197_712818
  · exact context_12_92198_712895
  · exact context_12_92199_712987

theorem selected_cut_28246 : selected 10 ⟨356516, by decide⟩
    (prefixPartial 11 23050) = some ⟨11, 2, 0, 356516, 23050, 5, 262144⟩ := by
  decide +kernel

theorem context_11_23050_356516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23050 ⟨356516, by decide⟩ :=
  accepted_of_selected 11 23050 ⟨356516, by decide⟩ ⟨11, 2, 0, 356516, 23050, 5, 262144⟩
    (by decide) selected_cut_28246

theorem selected_cut_28247 : selected 9 ⟨713060, by decide⟩
    (prefixPartial 12 92204) = some ⟨12, 2, 0, 713060, 92204, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_92204_713060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92204 ⟨713060, by decide⟩ :=
  accepted_of_selected 12 92204 ⟨713060, by decide⟩ ⟨12, 2, 0, 713060, 92204, 3901, 65536⟩
    (by decide) selected_cut_28247

theorem selected_cut_28248 : selected 9 ⟨713134, by decide⟩
    (prefixPartial 12 92205) = some ⟨12, 2, 0, 713134, 92205, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_92205_713134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92205 ⟨713134, by decide⟩ :=
  accepted_of_selected 12 92205 ⟨713134, by decide⟩ ⟨12, 2, 0, 713134, 92205, 4089, 65536⟩
    (by decide) selected_cut_28248

theorem selected_cut_28249 : selected 8 ⟨713145, by decide⟩
    (prefixPartial 13 368824) = some ⟨13, 2, 0, 713145, 368824, 653, 16384⟩ := by
  decide +kernel

theorem context_13_368824_713145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368824 ⟨713145, by decide⟩ :=
  accepted_of_selected 13 368824 ⟨713145, by decide⟩ ⟨13, 2, 0, 713145, 368824, 653, 16384⟩
    (by decide) selected_cut_28249

theorem selected_cut_28250 : selected 8 ⟨713179, by decide⟩
    (prefixPartial 13 368825) = some ⟨13, 2, 0, 713179, 368825, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_368825_713179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368825 ⟨713179, by decide⟩ :=
  accepted_of_selected 13 368825 ⟨713179, by decide⟩ ⟨13, 2, 0, 713179, 368825, 1461, 16384⟩
    (by decide) selected_cut_28250

theorem selected_cut_28251 : selected 8 ⟨713197, by decide⟩
    (prefixPartial 13 368826) = some ⟨13, 2, 0, 713197, 368826, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_368826_713197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368826 ⟨713197, by decide⟩ :=
  accepted_of_selected 13 368826 ⟨713197, by decide⟩ ⟨13, 2, 0, 713197, 368826, 1201, 16384⟩
    (by decide) selected_cut_28251

theorem selected_cut_28252 : selected 8 ⟨713203, by decide⟩
    (prefixPartial 13 368827) = some ⟨13, 2, 0, 713203, 368827, 829, 16384⟩ := by
  decide +kernel

theorem context_13_368827_713203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368827 ⟨713203, by decide⟩ :=
  accepted_of_selected 13 368827 ⟨713203, by decide⟩ ⟨13, 2, 0, 713203, 368827, 829, 16384⟩
    (by decide) selected_cut_28252

theorem unmarked_context_12_92206_713204 : frontier 9 ⟨713204, by decide⟩
    (prefixCache 12 92206) (prefixPartial 12 92206) = false := by
  decide +kernel

theorem node_context_12_92206_713204 : EJMOriginalGlobalDAGData.nodes 9 ⟨713204, by decide⟩ =
    .split (coordinate 12) (![⟨713145, by decide⟩,⟨713179, by decide⟩,⟨713197, by decide⟩,⟨713203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92206_713204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92206 ⟨713204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92206
    ⟨713204, by decide⟩ (by decide) (![⟨713145, by decide⟩,⟨713179, by decide⟩,⟨713197, by decide⟩,⟨713203, by decide⟩]) unmarked_context_12_92206_713204 node_context_12_92206_713204
  intro a
  fin_cases a
  · exact context_13_368824_713145
  · exact context_13_368825_713179
  · exact context_13_368826_713197
  · exact context_13_368827_713203

theorem selected_cut_28253 : selected 9 ⟨713271, by decide⟩
    (prefixPartial 12 92207) = some ⟨12, 2, 0, 713271, 92207, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_92207_713271 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92207 ⟨713271, by decide⟩ :=
  accepted_of_selected 12 92207 ⟨713271, by decide⟩ ⟨12, 2, 0, 713271, 92207, 3825, 65536⟩
    (by decide) selected_cut_28253

theorem unmarked_context_11_23051_713272 : frontier 10 ⟨713272, by decide⟩
    (prefixCache 11 23051) (prefixPartial 11 23051) = false := by
  decide +kernel

theorem node_context_11_23051_713272 : EJMOriginalGlobalDAGData.nodes 10 ⟨713272, by decide⟩ =
    .split (coordinate 11) (![⟨713060, by decide⟩,⟨713134, by decide⟩,⟨713204, by decide⟩,⟨713271, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23051_713272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23051 ⟨713272, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23051
    ⟨713272, by decide⟩ (by decide) (![⟨713060, by decide⟩,⟨713134, by decide⟩,⟨713204, by decide⟩,⟨713271, by decide⟩]) unmarked_context_11_23051_713272 node_context_11_23051_713272
  intro a
  fin_cases a
  · exact context_12_92204_713060
  · exact context_12_92205_713134
  · exact context_12_92206_713204
  · exact context_12_92207_713271

theorem unmarked_context_10_5762_713273 : frontier 11 ⟨713273, by decide⟩
    (prefixCache 10 5762) (prefixPartial 10 5762) = false := by
  decide +kernel

theorem node_context_10_5762_713273 : EJMOriginalGlobalDAGData.nodes 11 ⟨713273, by decide⟩ =
    .split (coordinate 10) (![⟨712668, by decide⟩,⟨712988, by decide⟩,⟨356516, by decide⟩,⟨713272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5762_713273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5762 ⟨713273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5762
    ⟨713273, by decide⟩ (by decide) (![⟨712668, by decide⟩,⟨712988, by decide⟩,⟨356516, by decide⟩,⟨713272, by decide⟩]) unmarked_context_10_5762_713273 node_context_10_5762_713273
  intro a
  fin_cases a
  · exact context_11_23048_712668
  · exact context_11_23049_712988
  · exact context_11_23050_356516
  · exact context_11_23051_713272

theorem selected_cut_28254 : selected 9 ⟨641337, by decide⟩
    (prefixPartial 12 92208) = some ⟨12, 1, 0, 641337, 92208, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92208_641337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92208 ⟨641337, by decide⟩ :=
  accepted_of_selected 12 92208 ⟨641337, by decide⟩ ⟨12, 1, 0, 641337, 92208, 1, 65536⟩
    (by decide) selected_cut_28254

theorem selected_cut_28255 : selected 9 ⟨713352, by decide⟩
    (prefixPartial 12 92209) = some ⟨12, 2, 0, 713352, 92209, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_92209_713352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92209 ⟨713352, by decide⟩ :=
  accepted_of_selected 12 92209 ⟨713352, by decide⟩ ⟨12, 2, 0, 713352, 92209, 3825, 65536⟩
    (by decide) selected_cut_28255

theorem selected_cut_28256 : selected 9 ⟨713423, by decide⟩
    (prefixPartial 12 92210) = some ⟨12, 2, 0, 713423, 92210, 3865, 65536⟩ := by
  decide +kernel

theorem context_12_92210_713423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92210 ⟨713423, by decide⟩ :=
  accepted_of_selected 12 92210 ⟨713423, by decide⟩ ⟨12, 2, 0, 713423, 92210, 3865, 65536⟩
    (by decide) selected_cut_28256

theorem selected_cut_28257 : selected 8 ⟨713444, by decide⟩
    (prefixPartial 13 368844) = some ⟨13, 2, 0, 713444, 368844, 681, 16384⟩ := by
  decide +kernel

theorem context_13_368844_713444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368844 ⟨713444, by decide⟩ :=
  accepted_of_selected 13 368844 ⟨713444, by decide⟩ ⟨13, 2, 0, 713444, 368844, 681, 16384⟩
    (by decide) selected_cut_28257

theorem selected_cut_28258 : selected 8 ⟨713484, by decide⟩
    (prefixPartial 13 368845) = some ⟨13, 2, 0, 713484, 368845, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_368845_713484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368845 ⟨713484, by decide⟩ :=
  accepted_of_selected 13 368845 ⟨713484, by decide⟩ ⟨13, 2, 0, 713484, 368845, 1633, 16384⟩
    (by decide) selected_cut_28258

theorem selected_cut_28259 : selected 8 ⟨713496, by decide⟩
    (prefixPartial 13 368846) = some ⟨13, 2, 0, 713496, 368846, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_368846_713496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368846 ⟨713496, by decide⟩ :=
  accepted_of_selected 13 368846 ⟨713496, by decide⟩ ⟨13, 2, 0, 713496, 368846, 1093, 16384⟩
    (by decide) selected_cut_28259

theorem selected_cut_28260 : selected 8 ⟨713503, by decide⟩
    (prefixPartial 13 368847) = some ⟨13, 2, 0, 713503, 368847, 753, 16384⟩ := by
  decide +kernel

theorem context_13_368847_713503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368847 ⟨713503, by decide⟩ :=
  accepted_of_selected 13 368847 ⟨713503, by decide⟩ ⟨13, 2, 0, 713503, 368847, 753, 16384⟩
    (by decide) selected_cut_28260

theorem unmarked_context_12_92211_713504 : frontier 9 ⟨713504, by decide⟩
    (prefixCache 12 92211) (prefixPartial 12 92211) = false := by
  decide +kernel

theorem node_context_12_92211_713504 : EJMOriginalGlobalDAGData.nodes 9 ⟨713504, by decide⟩ =
    .split (coordinate 12) (![⟨713444, by decide⟩,⟨713484, by decide⟩,⟨713496, by decide⟩,⟨713503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92211_713504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92211 ⟨713504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92211
    ⟨713504, by decide⟩ (by decide) (![⟨713444, by decide⟩,⟨713484, by decide⟩,⟨713496, by decide⟩,⟨713503, by decide⟩]) unmarked_context_12_92211_713504 node_context_12_92211_713504
  intro a
  fin_cases a
  · exact context_13_368844_713444
  · exact context_13_368845_713484
  · exact context_13_368846_713496
  · exact context_13_368847_713503

theorem unmarked_context_11_23052_713505 : frontier 10 ⟨713505, by decide⟩
    (prefixCache 11 23052) (prefixPartial 11 23052) = false := by
  decide +kernel

theorem node_context_11_23052_713505 : EJMOriginalGlobalDAGData.nodes 10 ⟨713505, by decide⟩ =
    .split (coordinate 11) (![⟨641337, by decide⟩,⟨713352, by decide⟩,⟨713423, by decide⟩,⟨713504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23052_713505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23052 ⟨713505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23052
    ⟨713505, by decide⟩ (by decide) (![⟨641337, by decide⟩,⟨713352, by decide⟩,⟨713423, by decide⟩,⟨713504, by decide⟩]) unmarked_context_11_23052_713505 node_context_11_23052_713505
  intro a
  fin_cases a
  · exact context_12_92208_641337
  · exact context_12_92209_713352
  · exact context_12_92210_713423
  · exact context_12_92211_713504

theorem selected_cut_28261 : selected 9 ⟨713569, by decide⟩
    (prefixPartial 12 92212) = some ⟨12, 2, 0, 713569, 92212, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_92212_713569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92212 ⟨713569, by decide⟩ :=
  accepted_of_selected 12 92212 ⟨713569, by decide⟩ ⟨12, 2, 0, 713569, 92212, 3897, 65536⟩
    (by decide) selected_cut_28261

theorem selected_cut_28262 : selected 9 ⟨713638, by decide⟩
    (prefixPartial 12 92213) = some ⟨12, 2, 0, 713638, 92213, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_92213_713638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92213 ⟨713638, by decide⟩ :=
  accepted_of_selected 12 92213 ⟨713638, by decide⟩ ⟨12, 2, 0, 713638, 92213, 3889, 65536⟩
    (by decide) selected_cut_28262

theorem selected_cut_28263 : selected 9 ⟨713702, by decide⟩
    (prefixPartial 12 92214) = some ⟨12, 2, 0, 713702, 92214, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_92214_713702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92214 ⟨713702, by decide⟩ :=
  accepted_of_selected 12 92214 ⟨713702, by decide⟩ ⟨12, 2, 0, 713702, 92214, 4037, 65536⟩
    (by decide) selected_cut_28263

theorem selected_cut_28264 : selected 8 ⟨713718, by decide⟩
    (prefixPartial 13 368860) = some ⟨13, 2, 0, 713718, 368860, 569, 16384⟩ := by
  decide +kernel

theorem context_13_368860_713718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368860 ⟨713718, by decide⟩ :=
  accepted_of_selected 13 368860 ⟨713718, by decide⟩ ⟨13, 2, 0, 713718, 368860, 569, 16384⟩
    (by decide) selected_cut_28264

theorem selected_cut_28265 : selected 8 ⟨713757, by decide⟩
    (prefixPartial 13 368861) = some ⟨13, 2, 0, 713757, 368861, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_368861_713757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368861 ⟨713757, by decide⟩ :=
  accepted_of_selected 13 368861 ⟨713757, by decide⟩ ⟨13, 2, 0, 713757, 368861, 1789, 16384⟩
    (by decide) selected_cut_28265

theorem selected_cut_28266 : selected 8 ⟨713774, by decide⟩
    (prefixPartial 13 368862) = some ⟨13, 2, 0, 713774, 368862, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_368862_713774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368862 ⟨713774, by decide⟩ :=
  accepted_of_selected 13 368862 ⟨713774, by decide⟩ ⟨13, 2, 0, 713774, 368862, 1349, 16384⟩
    (by decide) selected_cut_28266

theorem selected_cut_28267 : selected 8 ⟨713782, by decide⟩
    (prefixPartial 13 368863) = some ⟨13, 2, 0, 713782, 368863, 793, 16384⟩ := by
  decide +kernel

theorem context_13_368863_713782 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 368863 ⟨713782, by decide⟩ :=
  accepted_of_selected 13 368863 ⟨713782, by decide⟩ ⟨13, 2, 0, 713782, 368863, 793, 16384⟩
    (by decide) selected_cut_28267

theorem unmarked_context_12_92215_713783 : frontier 9 ⟨713783, by decide⟩
    (prefixCache 12 92215) (prefixPartial 12 92215) = false := by
  decide +kernel

theorem node_context_12_92215_713783 : EJMOriginalGlobalDAGData.nodes 9 ⟨713783, by decide⟩ =
    .split (coordinate 12) (![⟨713718, by decide⟩,⟨713757, by decide⟩,⟨713774, by decide⟩,⟨713782, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92215_713783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92215 ⟨713783, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92215
    ⟨713783, by decide⟩ (by decide) (![⟨713718, by decide⟩,⟨713757, by decide⟩,⟨713774, by decide⟩,⟨713782, by decide⟩]) unmarked_context_12_92215_713783 node_context_12_92215_713783
  intro a
  fin_cases a
  · exact context_13_368860_713718
  · exact context_13_368861_713757
  · exact context_13_368862_713774
  · exact context_13_368863_713782

theorem unmarked_context_11_23053_713784 : frontier 10 ⟨713784, by decide⟩
    (prefixCache 11 23053) (prefixPartial 11 23053) = false := by
  decide +kernel

theorem node_context_11_23053_713784 : EJMOriginalGlobalDAGData.nodes 10 ⟨713784, by decide⟩ =
    .split (coordinate 11) (![⟨713569, by decide⟩,⟨713638, by decide⟩,⟨713702, by decide⟩,⟨713783, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23053_713784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23053 ⟨713784, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23053
    ⟨713784, by decide⟩ (by decide) (![⟨713569, by decide⟩,⟨713638, by decide⟩,⟨713702, by decide⟩,⟨713783, by decide⟩]) unmarked_context_11_23053_713784 node_context_11_23053_713784
  intro a
  fin_cases a
  · exact context_12_92212_713569
  · exact context_12_92213_713638
  · exact context_12_92214_713702
  · exact context_12_92215_713783

theorem selected_cut_28268 : selected 9 ⟨713837, by decide⟩
    (prefixPartial 12 92216) = some ⟨12, 2, 0, 713837, 92216, 3325, 65536⟩ := by
  decide +kernel

theorem context_12_92216_713837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92216 ⟨713837, by decide⟩ :=
  accepted_of_selected 12 92216 ⟨713837, by decide⟩ ⟨12, 2, 0, 713837, 92216, 3325, 65536⟩
    (by decide) selected_cut_28268

theorem selected_cut_28269 : selected 9 ⟨713899, by decide⟩
    (prefixPartial 12 92217) = some ⟨12, 2, 0, 713899, 92217, 3565, 65536⟩ := by
  decide +kernel

theorem context_12_92217_713899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92217 ⟨713899, by decide⟩ :=
  accepted_of_selected 12 92217 ⟨713899, by decide⟩ ⟨12, 2, 0, 713899, 92217, 3565, 65536⟩
    (by decide) selected_cut_28269

theorem selected_cut_28270 : selected 9 ⟨713950, by decide⟩
    (prefixPartial 12 92218) = some ⟨12, 2, 0, 713950, 92218, 3169, 65536⟩ := by
  decide +kernel

theorem context_12_92218_713950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92218 ⟨713950, by decide⟩ :=
  accepted_of_selected 12 92218 ⟨713950, by decide⟩ ⟨12, 2, 0, 713950, 92218, 3169, 65536⟩
    (by decide) selected_cut_28270

theorem selected_cut_28271 : selected 9 ⟨714021, by decide⟩
    (prefixPartial 12 92219) = some ⟨12, 2, 0, 714021, 92219, 3757, 65536⟩ := by
  decide +kernel

theorem context_12_92219_714021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92219 ⟨714021, by decide⟩ :=
  accepted_of_selected 12 92219 ⟨714021, by decide⟩ ⟨12, 2, 0, 714021, 92219, 3757, 65536⟩
    (by decide) selected_cut_28271

theorem unmarked_context_11_23054_714022 : frontier 10 ⟨714022, by decide⟩
    (prefixCache 11 23054) (prefixPartial 11 23054) = false := by
  decide +kernel

theorem node_context_11_23054_714022 : EJMOriginalGlobalDAGData.nodes 10 ⟨714022, by decide⟩ =
    .split (coordinate 11) (![⟨713837, by decide⟩,⟨713899, by decide⟩,⟨713950, by decide⟩,⟨714021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23054_714022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23054 ⟨714022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23054
    ⟨714022, by decide⟩ (by decide) (![⟨713837, by decide⟩,⟨713899, by decide⟩,⟨713950, by decide⟩,⟨714021, by decide⟩]) unmarked_context_11_23054_714022 node_context_11_23054_714022
  intro a
  fin_cases a
  · exact context_12_92216_713837
  · exact context_12_92217_713899
  · exact context_12_92218_713950
  · exact context_12_92219_714021

theorem selected_cut_28272 : selected 9 ⟨714076, by decide⟩
    (prefixPartial 12 92220) = some ⟨12, 2, 0, 714076, 92220, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_92220_714076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92220 ⟨714076, by decide⟩ :=
  accepted_of_selected 12 92220 ⟨714076, by decide⟩ ⟨12, 2, 0, 714076, 92220, 3409, 65536⟩
    (by decide) selected_cut_28272

theorem selected_cut_28273 : selected 9 ⟨714133, by decide⟩
    (prefixPartial 12 92221) = some ⟨12, 2, 0, 714133, 92221, 3641, 65536⟩ := by
  decide +kernel

theorem context_12_92221_714133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92221 ⟨714133, by decide⟩ :=
  accepted_of_selected 12 92221 ⟨714133, by decide⟩ ⟨12, 2, 0, 714133, 92221, 3641, 65536⟩
    (by decide) selected_cut_28273

theorem selected_cut_28274 : selected 9 ⟨714188, by decide⟩
    (prefixPartial 12 92222) = some ⟨12, 2, 0, 714188, 92222, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_92222_714188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92222 ⟨714188, by decide⟩ :=
  accepted_of_selected 12 92222 ⟨714188, by decide⟩ ⟨12, 2, 0, 714188, 92222, 3677, 65536⟩
    (by decide) selected_cut_28274

theorem selected_cut_28275 : selected 9 ⟨714248, by decide⟩
    (prefixPartial 12 92223) = some ⟨12, 2, 0, 714248, 92223, 3765, 65536⟩ := by
  decide +kernel

theorem context_12_92223_714248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92223 ⟨714248, by decide⟩ :=
  accepted_of_selected 12 92223 ⟨714248, by decide⟩ ⟨12, 2, 0, 714248, 92223, 3765, 65536⟩
    (by decide) selected_cut_28275

theorem unmarked_context_11_23055_714249 : frontier 10 ⟨714249, by decide⟩
    (prefixCache 11 23055) (prefixPartial 11 23055) = false := by
  decide +kernel

theorem node_context_11_23055_714249 : EJMOriginalGlobalDAGData.nodes 10 ⟨714249, by decide⟩ =
    .split (coordinate 11) (![⟨714076, by decide⟩,⟨714133, by decide⟩,⟨714188, by decide⟩,⟨714248, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23055_714249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23055 ⟨714249, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23055
    ⟨714249, by decide⟩ (by decide) (![⟨714076, by decide⟩,⟨714133, by decide⟩,⟨714188, by decide⟩,⟨714248, by decide⟩]) unmarked_context_11_23055_714249 node_context_11_23055_714249
  intro a
  fin_cases a
  · exact context_12_92220_714076
  · exact context_12_92221_714133
  · exact context_12_92222_714188
  · exact context_12_92223_714248

theorem unmarked_context_10_5763_714250 : frontier 11 ⟨714250, by decide⟩
    (prefixCache 10 5763) (prefixPartial 10 5763) = false := by
  decide +kernel

theorem node_context_10_5763_714250 : EJMOriginalGlobalDAGData.nodes 11 ⟨714250, by decide⟩ =
    .split (coordinate 10) (![⟨713505, by decide⟩,⟨713784, by decide⟩,⟨714022, by decide⟩,⟨714249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5763_714250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5763 ⟨714250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5763
    ⟨714250, by decide⟩ (by decide) (![⟨713505, by decide⟩,⟨713784, by decide⟩,⟨714022, by decide⟩,⟨714249, by decide⟩]) unmarked_context_10_5763_714250 node_context_10_5763_714250
  intro a
  fin_cases a
  · exact context_11_23052_713505
  · exact context_11_23053_713784
  · exact context_11_23054_714022
  · exact context_11_23055_714249

theorem unmarked_context_9_1440_714251 : frontier 12 ⟨714251, by decide⟩
    (prefixCache 9 1440) (prefixPartial 9 1440) = false := by
  decide +kernel

theorem node_context_9_1440_714251 : EJMOriginalGlobalDAGData.nodes 12 ⟨714251, by decide⟩ =
    .split (coordinate 9) (![⟨711324, by decide⟩,⟨712414, by decide⟩,⟨713273, by decide⟩,⟨714250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1440_714251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1440 ⟨714251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1440
    ⟨714251, by decide⟩ (by decide) (![⟨711324, by decide⟩,⟨712414, by decide⟩,⟨713273, by decide⟩,⟨714250, by decide⟩]) unmarked_context_9_1440_714251 node_context_9_1440_714251
  intro a
  fin_cases a
  · exact context_10_5760_711324
  · exact context_10_5761_712414
  · exact context_10_5762_713273
  · exact context_10_5763_714250

theorem selected_cut_28276 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 5764) = some ⟨10, 1, 0, 145424, 5764, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5764_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5764 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 5764 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 5764, 1, 1048576⟩
    (by decide) selected_cut_28276

theorem selected_cut_28277 : selected 9 ⟨266170, by decide⟩
    (prefixPartial 12 92240) = some ⟨12, 1, 0, 266170, 92240, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92240_266170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92240 ⟨266170, by decide⟩ :=
  accepted_of_selected 12 92240 ⟨266170, by decide⟩ ⟨12, 1, 0, 266170, 92240, 1, 65536⟩
    (by decide) selected_cut_28277

theorem selected_cut_28278 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 92241) = some ⟨12, 1, 0, 642341, 92241, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92241_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92241 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 92241 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 92241, 1, 65536⟩
    (by decide) selected_cut_28278

theorem selected_cut_28279 : selected 9 ⟨714319, by decide⟩
    (prefixPartial 12 92242) = some ⟨12, 2, 0, 714319, 92242, 2721, 65536⟩ := by
  decide +kernel

theorem context_12_92242_714319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92242 ⟨714319, by decide⟩ :=
  accepted_of_selected 12 92242 ⟨714319, by decide⟩ ⟨12, 2, 0, 714319, 92242, 2721, 65536⟩
    (by decide) selected_cut_28279

theorem selected_cut_28280 : selected 9 ⟨714384, by decide⟩
    (prefixPartial 12 92243) = some ⟨12, 2, 0, 714384, 92243, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_92243_714384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92243 ⟨714384, by decide⟩ :=
  accepted_of_selected 12 92243 ⟨714384, by decide⟩ ⟨12, 2, 0, 714384, 92243, 2633, 65536⟩
    (by decide) selected_cut_28280

theorem unmarked_context_11_23060_714385 : frontier 10 ⟨714385, by decide⟩
    (prefixCache 11 23060) (prefixPartial 11 23060) = false := by
  decide +kernel

theorem node_context_11_23060_714385 : EJMOriginalGlobalDAGData.nodes 10 ⟨714385, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨642341, by decide⟩,⟨714319, by decide⟩,⟨714384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23060_714385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23060 ⟨714385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23060
    ⟨714385, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨642341, by decide⟩,⟨714319, by decide⟩,⟨714384, by decide⟩]) unmarked_context_11_23060_714385 node_context_11_23060_714385
  intro a
  fin_cases a
  · exact context_12_92240_266170
  · exact context_12_92241_642341
  · exact context_12_92242_714319
  · exact context_12_92243_714384

theorem selected_cut_28281 : selected 9 ⟨714438, by decide⟩
    (prefixPartial 12 92244) = some ⟨12, 2, 0, 714438, 92244, 2645, 65536⟩ := by
  decide +kernel

theorem context_12_92244_714438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92244 ⟨714438, by decide⟩ :=
  accepted_of_selected 12 92244 ⟨714438, by decide⟩ ⟨12, 2, 0, 714438, 92244, 2645, 65536⟩
    (by decide) selected_cut_28281

theorem selected_cut_28282 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 92245) = some ⟨12, 1, 0, 642341, 92245, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92245_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92245 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 92245 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 92245, 1, 65536⟩
    (by decide) selected_cut_28282

theorem selected_cut_28283 : selected 9 ⟨714487, by decide⟩
    (prefixPartial 12 92246) = some ⟨12, 2, 0, 714487, 92246, 2821, 65536⟩ := by
  decide +kernel

theorem context_12_92246_714487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92246 ⟨714487, by decide⟩ :=
  accepted_of_selected 12 92246 ⟨714487, by decide⟩ ⟨12, 2, 0, 714487, 92246, 2821, 65536⟩
    (by decide) selected_cut_28283

theorem selected_cut_28284 : selected 9 ⟨714555, by decide⟩
    (prefixPartial 12 92247) = some ⟨12, 2, 0, 714555, 92247, 2789, 65536⟩ := by
  decide +kernel

theorem context_12_92247_714555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92247 ⟨714555, by decide⟩ :=
  accepted_of_selected 12 92247 ⟨714555, by decide⟩ ⟨12, 2, 0, 714555, 92247, 2789, 65536⟩
    (by decide) selected_cut_28284

theorem unmarked_context_11_23061_714556 : frontier 10 ⟨714556, by decide⟩
    (prefixCache 11 23061) (prefixPartial 11 23061) = false := by
  decide +kernel

theorem node_context_11_23061_714556 : EJMOriginalGlobalDAGData.nodes 10 ⟨714556, by decide⟩ =
    .split (coordinate 11) (![⟨714438, by decide⟩,⟨642341, by decide⟩,⟨714487, by decide⟩,⟨714555, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23061_714556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23061 ⟨714556, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23061
    ⟨714556, by decide⟩ (by decide) (![⟨714438, by decide⟩,⟨642341, by decide⟩,⟨714487, by decide⟩,⟨714555, by decide⟩]) unmarked_context_11_23061_714556 node_context_11_23061_714556
  intro a
  fin_cases a
  · exact context_12_92244_714438
  · exact context_12_92245_642341
  · exact context_12_92246_714487
  · exact context_12_92247_714555

theorem selected_cut_28285 : selected 9 ⟨714602, by decide⟩
    (prefixPartial 12 92248) = some ⟨12, 2, 0, 714602, 92248, 2297, 65536⟩ := by
  decide +kernel

theorem context_12_92248_714602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92248 ⟨714602, by decide⟩ :=
  accepted_of_selected 12 92248 ⟨714602, by decide⟩ ⟨12, 2, 0, 714602, 92248, 2297, 65536⟩
    (by decide) selected_cut_28285

theorem selected_cut_28286 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 92249) = some ⟨12, 1, 0, 642341, 92249, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92249_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92249 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 92249 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 92249, 1, 65536⟩
    (by decide) selected_cut_28286

theorem selected_cut_28287 : selected 9 ⟨714640, by decide⟩
    (prefixPartial 12 92250) = some ⟨12, 2, 0, 714640, 92250, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_92250_714640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92250 ⟨714640, by decide⟩ :=
  accepted_of_selected 12 92250 ⟨714640, by decide⟩ ⟨12, 2, 0, 714640, 92250, 2337, 65536⟩
    (by decide) selected_cut_28287

theorem selected_cut_28288 : selected 9 ⟨714684, by decide⟩
    (prefixPartial 12 92251) = some ⟨12, 2, 0, 714684, 92251, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_92251_714684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92251 ⟨714684, by decide⟩ :=
  accepted_of_selected 12 92251 ⟨714684, by decide⟩ ⟨12, 2, 0, 714684, 92251, 2249, 65536⟩
    (by decide) selected_cut_28288

theorem unmarked_context_11_23062_714685 : frontier 10 ⟨714685, by decide⟩
    (prefixCache 11 23062) (prefixPartial 11 23062) = false := by
  decide +kernel

theorem node_context_11_23062_714685 : EJMOriginalGlobalDAGData.nodes 10 ⟨714685, by decide⟩ =
    .split (coordinate 11) (![⟨714602, by decide⟩,⟨642341, by decide⟩,⟨714640, by decide⟩,⟨714684, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23062_714685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23062 ⟨714685, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23062
    ⟨714685, by decide⟩ (by decide) (![⟨714602, by decide⟩,⟨642341, by decide⟩,⟨714640, by decide⟩,⟨714684, by decide⟩]) unmarked_context_11_23062_714685 node_context_11_23062_714685
  intro a
  fin_cases a
  · exact context_12_92248_714602
  · exact context_12_92249_642341
  · exact context_12_92250_714640
  · exact context_12_92251_714684

theorem selected_cut_28289 : selected 9 ⟨714724, by decide⟩
    (prefixPartial 12 92252) = some ⟨12, 2, 0, 714724, 92252, 2109, 65536⟩ := by
  decide +kernel

theorem context_12_92252_714724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92252 ⟨714724, by decide⟩ :=
  accepted_of_selected 12 92252 ⟨714724, by decide⟩ ⟨12, 2, 0, 714724, 92252, 2109, 65536⟩
    (by decide) selected_cut_28289

theorem selected_cut_28290 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 92253) = some ⟨12, 1, 0, 642341, 92253, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92253_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92253 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 92253 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 92253, 1, 65536⟩
    (by decide) selected_cut_28290

theorem selected_cut_28291 : selected 9 ⟨714766, by decide⟩
    (prefixPartial 12 92254) = some ⟨12, 2, 0, 714766, 92254, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_92254_714766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92254 ⟨714766, by decide⟩ :=
  accepted_of_selected 12 92254 ⟨714766, by decide⟩ ⟨12, 2, 0, 714766, 92254, 2293, 65536⟩
    (by decide) selected_cut_28291

theorem selected_cut_28292 : selected 9 ⟨714801, by decide⟩
    (prefixPartial 12 92255) = some ⟨12, 2, 0, 714801, 92255, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_92255_714801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92255 ⟨714801, by decide⟩ :=
  accepted_of_selected 12 92255 ⟨714801, by decide⟩ ⟨12, 2, 0, 714801, 92255, 2145, 65536⟩
    (by decide) selected_cut_28292

theorem unmarked_context_11_23063_714802 : frontier 10 ⟨714802, by decide⟩
    (prefixCache 11 23063) (prefixPartial 11 23063) = false := by
  decide +kernel

theorem node_context_11_23063_714802 : EJMOriginalGlobalDAGData.nodes 10 ⟨714802, by decide⟩ =
    .split (coordinate 11) (![⟨714724, by decide⟩,⟨642341, by decide⟩,⟨714766, by decide⟩,⟨714801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23063_714802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23063 ⟨714802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23063
    ⟨714802, by decide⟩ (by decide) (![⟨714724, by decide⟩,⟨642341, by decide⟩,⟨714766, by decide⟩,⟨714801, by decide⟩]) unmarked_context_11_23063_714802 node_context_11_23063_714802
  intro a
  fin_cases a
  · exact context_12_92252_714724
  · exact context_12_92253_642341
  · exact context_12_92254_714766
  · exact context_12_92255_714801

theorem unmarked_context_10_5765_714803 : frontier 11 ⟨714803, by decide⟩
    (prefixCache 10 5765) (prefixPartial 10 5765) = false := by
  decide +kernel

theorem node_context_10_5765_714803 : EJMOriginalGlobalDAGData.nodes 11 ⟨714803, by decide⟩ =
    .split (coordinate 10) (![⟨714385, by decide⟩,⟨714556, by decide⟩,⟨714685, by decide⟩,⟨714802, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5765_714803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5765 ⟨714803, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5765
    ⟨714803, by decide⟩ (by decide) (![⟨714385, by decide⟩,⟨714556, by decide⟩,⟨714685, by decide⟩,⟨714802, by decide⟩]) unmarked_context_10_5765_714803 node_context_10_5765_714803
  intro a
  fin_cases a
  · exact context_11_23060_714385
  · exact context_11_23061_714556
  · exact context_11_23062_714685
  · exact context_11_23063_714802

theorem selected_cut_28293 : selected 9 ⟨714851, by decide⟩
    (prefixPartial 12 92256) = some ⟨12, 2, 0, 714851, 92256, 713, 65536⟩ := by
  decide +kernel

theorem context_12_92256_714851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92256 ⟨714851, by decide⟩ :=
  accepted_of_selected 12 92256 ⟨714851, by decide⟩ ⟨12, 2, 0, 714851, 92256, 713, 65536⟩
    (by decide) selected_cut_28293

theorem selected_cut_28294 : selected 9 ⟨219808, by decide⟩
    (prefixPartial 12 92257) = some ⟨12, 1, 0, 219808, 92257, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92257_219808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92257 ⟨219808, by decide⟩ :=
  accepted_of_selected 12 92257 ⟨219808, by decide⟩ ⟨12, 1, 0, 219808, 92257, 1, 65536⟩
    (by decide) selected_cut_28294

theorem selected_cut_28295 : selected 9 ⟨714890, by decide⟩
    (prefixPartial 12 92258) = some ⟨12, 2, 0, 714890, 92258, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_92258_714890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92258 ⟨714890, by decide⟩ :=
  accepted_of_selected 12 92258 ⟨714890, by decide⟩ ⟨12, 2, 0, 714890, 92258, 2057, 65536⟩
    (by decide) selected_cut_28295

theorem selected_cut_28296 : selected 9 ⟨714921, by decide⟩
    (prefixPartial 12 92259) = some ⟨12, 2, 0, 714921, 92259, 1865, 65536⟩ := by
  decide +kernel

theorem context_12_92259_714921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92259 ⟨714921, by decide⟩ :=
  accepted_of_selected 12 92259 ⟨714921, by decide⟩ ⟨12, 2, 0, 714921, 92259, 1865, 65536⟩
    (by decide) selected_cut_28296

theorem unmarked_context_11_23064_714922 : frontier 10 ⟨714922, by decide⟩
    (prefixCache 11 23064) (prefixPartial 11 23064) = false := by
  decide +kernel

theorem node_context_11_23064_714922 : EJMOriginalGlobalDAGData.nodes 10 ⟨714922, by decide⟩ =
    .split (coordinate 11) (![⟨714851, by decide⟩,⟨219808, by decide⟩,⟨714890, by decide⟩,⟨714921, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23064_714922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23064 ⟨714922, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23064
    ⟨714922, by decide⟩ (by decide) (![⟨714851, by decide⟩,⟨219808, by decide⟩,⟨714890, by decide⟩,⟨714921, by decide⟩]) unmarked_context_11_23064_714922 node_context_11_23064_714922
  intro a
  fin_cases a
  · exact context_12_92256_714851
  · exact context_12_92257_219808
  · exact context_12_92258_714890
  · exact context_12_92259_714921

theorem selected_cut_28297 : selected 10 ⟨714985, by decide⟩
    (prefixPartial 11 23065) = some ⟨11, 2, 0, 714985, 23065, 3289, 262144⟩ := by
  decide +kernel

theorem context_11_23065_714985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23065 ⟨714985, by decide⟩ :=
  accepted_of_selected 11 23065 ⟨714985, by decide⟩ ⟨11, 2, 0, 714985, 23065, 3289, 262144⟩
    (by decide) selected_cut_28297

theorem selected_cut_28298 : selected 10 ⟨715077, by decide⟩
    (prefixPartial 11 23066) = some ⟨11, 2, 0, 715077, 23066, 4061, 262144⟩ := by
  decide +kernel

theorem context_11_23066_715077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23066 ⟨715077, by decide⟩ :=
  accepted_of_selected 11 23066 ⟨715077, by decide⟩ ⟨11, 2, 0, 715077, 23066, 4061, 262144⟩
    (by decide) selected_cut_28298

theorem selected_cut_28299 : selected 10 ⟨715108, by decide⟩
    (prefixPartial 11 23067) = some ⟨11, 2, 0, 715108, 23067, 1049, 262144⟩ := by
  decide +kernel

theorem context_11_23067_715108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23067 ⟨715108, by decide⟩ :=
  accepted_of_selected 11 23067 ⟨715108, by decide⟩ ⟨11, 2, 0, 715108, 23067, 1049, 262144⟩
    (by decide) selected_cut_28299

theorem unmarked_context_10_5766_715109 : frontier 11 ⟨715109, by decide⟩
    (prefixCache 10 5766) (prefixPartial 10 5766) = false := by
  decide +kernel

theorem node_context_10_5766_715109 : EJMOriginalGlobalDAGData.nodes 11 ⟨715109, by decide⟩ =
    .split (coordinate 10) (![⟨714922, by decide⟩,⟨714985, by decide⟩,⟨715077, by decide⟩,⟨715108, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5766_715109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5766 ⟨715109, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5766
    ⟨715109, by decide⟩ (by decide) (![⟨714922, by decide⟩,⟨714985, by decide⟩,⟨715077, by decide⟩,⟨715108, by decide⟩]) unmarked_context_10_5766_715109 node_context_10_5766_715109
  intro a
  fin_cases a
  · exact context_11_23064_714922
  · exact context_11_23065_714985
  · exact context_11_23066_715077
  · exact context_11_23067_715108

theorem selected_cut_28300 : selected 9 ⟨715201, by decide⟩
    (prefixPartial 12 92272) = some ⟨12, 2, 0, 715201, 92272, 3089, 65536⟩ := by
  decide +kernel

theorem context_12_92272_715201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92272 ⟨715201, by decide⟩ :=
  accepted_of_selected 12 92272 ⟨715201, by decide⟩ ⟨12, 2, 0, 715201, 92272, 3089, 65536⟩
    (by decide) selected_cut_28300

theorem selected_cut_28301 : selected 9 ⟨355230, by decide⟩
    (prefixPartial 12 92273) = some ⟨12, 1, 0, 355230, 92273, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92273_355230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92273 ⟨355230, by decide⟩ :=
  accepted_of_selected 12 92273 ⟨355230, by decide⟩ ⟨12, 1, 0, 355230, 92273, 1, 65536⟩
    (by decide) selected_cut_28301

theorem selected_cut_28302 : selected 9 ⟨715232, by decide⟩
    (prefixPartial 12 92274) = some ⟨12, 2, 0, 715232, 92274, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_92274_715232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92274 ⟨715232, by decide⟩ :=
  accepted_of_selected 12 92274 ⟨715232, by decide⟩ ⟨12, 2, 0, 715232, 92274, 2057, 65536⟩
    (by decide) selected_cut_28302

theorem selected_cut_28303 : selected 9 ⟨715273, by decide⟩
    (prefixPartial 12 92275) = some ⟨12, 2, 0, 715273, 92275, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_92275_715273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92275 ⟨715273, by decide⟩ :=
  accepted_of_selected 12 92275 ⟨715273, by decide⟩ ⟨12, 2, 0, 715273, 92275, 1973, 65536⟩
    (by decide) selected_cut_28303

theorem unmarked_context_11_23068_715274 : frontier 10 ⟨715274, by decide⟩
    (prefixCache 11 23068) (prefixPartial 11 23068) = false := by
  decide +kernel

theorem node_context_11_23068_715274 : EJMOriginalGlobalDAGData.nodes 10 ⟨715274, by decide⟩ =
    .split (coordinate 11) (![⟨715201, by decide⟩,⟨355230, by decide⟩,⟨715232, by decide⟩,⟨715273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23068_715274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23068 ⟨715274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23068
    ⟨715274, by decide⟩ (by decide) (![⟨715201, by decide⟩,⟨355230, by decide⟩,⟨715232, by decide⟩,⟨715273, by decide⟩]) unmarked_context_11_23068_715274 node_context_11_23068_715274
  intro a
  fin_cases a
  · exact context_12_92272_715201
  · exact context_12_92273_355230
  · exact context_12_92274_715232
  · exact context_12_92275_715273

theorem selected_cut_28304 : selected 9 ⟨715306, by decide⟩
    (prefixPartial 12 92276) = some ⟨12, 2, 0, 715306, 92276, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_92276_715306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92276 ⟨715306, by decide⟩ :=
  accepted_of_selected 12 92276 ⟨715306, by decide⟩ ⟨12, 2, 0, 715306, 92276, 2061, 65536⟩
    (by decide) selected_cut_28304

theorem selected_cut_28305 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 92277) = some ⟨12, 1, 0, 642794, 92277, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92277_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92277 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 92277 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 92277, 1, 65536⟩
    (by decide) selected_cut_28305

theorem selected_cut_28306 : selected 9 ⟨715339, by decide⟩
    (prefixPartial 12 92278) = some ⟨12, 2, 0, 715339, 92278, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_92278_715339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92278 ⟨715339, by decide⟩ :=
  accepted_of_selected 12 92278 ⟨715339, by decide⟩ ⟨12, 2, 0, 715339, 92278, 2113, 65536⟩
    (by decide) selected_cut_28306

theorem selected_cut_28307 : selected 9 ⟨715374, by decide⟩
    (prefixPartial 12 92279) = some ⟨12, 2, 0, 715374, 92279, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_92279_715374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92279 ⟨715374, by decide⟩ :=
  accepted_of_selected 12 92279 ⟨715374, by decide⟩ ⟨12, 2, 0, 715374, 92279, 2049, 65536⟩
    (by decide) selected_cut_28307

theorem unmarked_context_11_23069_715375 : frontier 10 ⟨715375, by decide⟩
    (prefixCache 11 23069) (prefixPartial 11 23069) = false := by
  decide +kernel

theorem node_context_11_23069_715375 : EJMOriginalGlobalDAGData.nodes 10 ⟨715375, by decide⟩ =
    .split (coordinate 11) (![⟨715306, by decide⟩,⟨642794, by decide⟩,⟨715339, by decide⟩,⟨715374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23069_715375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23069 ⟨715375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23069
    ⟨715375, by decide⟩ (by decide) (![⟨715306, by decide⟩,⟨642794, by decide⟩,⟨715339, by decide⟩,⟨715374, by decide⟩]) unmarked_context_11_23069_715375 node_context_11_23069_715375
  intro a
  fin_cases a
  · exact context_12_92276_715306
  · exact context_12_92277_642794
  · exact context_12_92278_715339
  · exact context_12_92279_715374

theorem selected_cut_28308 : selected 9 ⟨715400, by decide⟩
    (prefixPartial 12 92280) = some ⟨12, 2, 0, 715400, 92280, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_92280_715400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92280 ⟨715400, by decide⟩ :=
  accepted_of_selected 12 92280 ⟨715400, by decide⟩ ⟨12, 2, 0, 715400, 92280, 1797, 65536⟩
    (by decide) selected_cut_28308

theorem selected_cut_28309 : selected 9 ⟨715438, by decide⟩
    (prefixPartial 12 92281) = some ⟨12, 2, 0, 715438, 92281, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_92281_715438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92281 ⟨715438, by decide⟩ :=
  accepted_of_selected 12 92281 ⟨715438, by decide⟩ ⟨12, 2, 0, 715438, 92281, 2025, 65536⟩
    (by decide) selected_cut_28309

theorem selected_cut_28310 : selected 9 ⟨715464, by decide⟩
    (prefixPartial 12 92282) = some ⟨12, 2, 0, 715464, 92282, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_92282_715464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92282 ⟨715464, by decide⟩ :=
  accepted_of_selected 12 92282 ⟨715464, by decide⟩ ⟨12, 2, 0, 715464, 92282, 1693, 65536⟩
    (by decide) selected_cut_28310

theorem selected_cut_28311 : selected 9 ⟨715484, by decide⟩
    (prefixPartial 12 92283) = some ⟨12, 2, 0, 715484, 92283, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_92283_715484 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92283 ⟨715484, by decide⟩ :=
  accepted_of_selected 12 92283 ⟨715484, by decide⟩ ⟨12, 2, 0, 715484, 92283, 1573, 65536⟩
    (by decide) selected_cut_28311

theorem unmarked_context_11_23070_715485 : frontier 10 ⟨715485, by decide⟩
    (prefixCache 11 23070) (prefixPartial 11 23070) = false := by
  decide +kernel

theorem node_context_11_23070_715485 : EJMOriginalGlobalDAGData.nodes 10 ⟨715485, by decide⟩ =
    .split (coordinate 11) (![⟨715400, by decide⟩,⟨715438, by decide⟩,⟨715464, by decide⟩,⟨715484, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23070_715485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23070 ⟨715485, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23070
    ⟨715485, by decide⟩ (by decide) (![⟨715400, by decide⟩,⟨715438, by decide⟩,⟨715464, by decide⟩,⟨715484, by decide⟩]) unmarked_context_11_23070_715485 node_context_11_23070_715485
  intro a
  fin_cases a
  · exact context_12_92280_715400
  · exact context_12_92281_715438
  · exact context_12_92282_715464
  · exact context_12_92283_715484

theorem selected_cut_28312 : selected 9 ⟨715502, by decide⟩
    (prefixPartial 12 92284) = some ⟨12, 2, 0, 715502, 92284, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_92284_715502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92284 ⟨715502, by decide⟩ :=
  accepted_of_selected 12 92284 ⟨715502, by decide⟩ ⟨12, 2, 0, 715502, 92284, 1465, 65536⟩
    (by decide) selected_cut_28312

theorem selected_cut_28313 : selected 9 ⟨715536, by decide⟩
    (prefixPartial 12 92285) = some ⟨12, 2, 0, 715536, 92285, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_92285_715536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92285 ⟨715536, by decide⟩ :=
  accepted_of_selected 12 92285 ⟨715536, by decide⟩ ⟨12, 2, 0, 715536, 92285, 1653, 65536⟩
    (by decide) selected_cut_28313

theorem selected_cut_28314 : selected 9 ⟨715555, by decide⟩
    (prefixPartial 12 92286) = some ⟨12, 2, 0, 715555, 92286, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_92286_715555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92286 ⟨715555, by decide⟩ :=
  accepted_of_selected 12 92286 ⟨715555, by decide⟩ ⟨12, 2, 0, 715555, 92286, 1461, 65536⟩
    (by decide) selected_cut_28314

theorem selected_cut_28315 : selected 9 ⟨715570, by decide⟩
    (prefixPartial 12 92287) = some ⟨12, 2, 0, 715570, 92287, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_92287_715570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92287 ⟨715570, by decide⟩ :=
  accepted_of_selected 12 92287 ⟨715570, by decide⟩ ⟨12, 2, 0, 715570, 92287, 1337, 65536⟩
    (by decide) selected_cut_28315

theorem unmarked_context_11_23071_715571 : frontier 10 ⟨715571, by decide⟩
    (prefixCache 11 23071) (prefixPartial 11 23071) = false := by
  decide +kernel

theorem node_context_11_23071_715571 : EJMOriginalGlobalDAGData.nodes 10 ⟨715571, by decide⟩ =
    .split (coordinate 11) (![⟨715502, by decide⟩,⟨715536, by decide⟩,⟨715555, by decide⟩,⟨715570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23071_715571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23071 ⟨715571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23071
    ⟨715571, by decide⟩ (by decide) (![⟨715502, by decide⟩,⟨715536, by decide⟩,⟨715555, by decide⟩,⟨715570, by decide⟩]) unmarked_context_11_23071_715571 node_context_11_23071_715571
  intro a
  fin_cases a
  · exact context_12_92284_715502
  · exact context_12_92285_715536
  · exact context_12_92286_715555
  · exact context_12_92287_715570

theorem unmarked_context_10_5767_715572 : frontier 11 ⟨715572, by decide⟩
    (prefixCache 10 5767) (prefixPartial 10 5767) = false := by
  decide +kernel

theorem node_context_10_5767_715572 : EJMOriginalGlobalDAGData.nodes 11 ⟨715572, by decide⟩ =
    .split (coordinate 10) (![⟨715274, by decide⟩,⟨715375, by decide⟩,⟨715485, by decide⟩,⟨715571, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5767_715572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5767 ⟨715572, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5767
    ⟨715572, by decide⟩ (by decide) (![⟨715274, by decide⟩,⟨715375, by decide⟩,⟨715485, by decide⟩,⟨715571, by decide⟩]) unmarked_context_10_5767_715572 node_context_10_5767_715572
  intro a
  fin_cases a
  · exact context_11_23068_715274
  · exact context_11_23069_715375
  · exact context_11_23070_715485
  · exact context_11_23071_715571

theorem unmarked_context_9_1441_715573 : frontier 12 ⟨715573, by decide⟩
    (prefixCache 9 1441) (prefixPartial 9 1441) = false := by
  decide +kernel

theorem node_context_9_1441_715573 : EJMOriginalGlobalDAGData.nodes 12 ⟨715573, by decide⟩ =
    .split (coordinate 9) (![⟨145424, by decide⟩,⟨714803, by decide⟩,⟨715109, by decide⟩,⟨715572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1441_715573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1441 ⟨715573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1441
    ⟨715573, by decide⟩ (by decide) (![⟨145424, by decide⟩,⟨714803, by decide⟩,⟨715109, by decide⟩,⟨715572, by decide⟩]) unmarked_context_9_1441_715573 node_context_9_1441_715573
  intro a
  fin_cases a
  · exact context_10_5764_145424
  · exact context_10_5765_714803
  · exact context_10_5766_715109
  · exact context_10_5767_715572

theorem selected_cut_28316 : selected 11 ⟨145424, by decide⟩
    (prefixPartial 10 5768) = some ⟨10, 1, 0, 145424, 5768, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_5768_145424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5768 ⟨145424, by decide⟩ :=
  accepted_of_selected 10 5768 ⟨145424, by decide⟩ ⟨10, 1, 0, 145424, 5768, 1, 1048576⟩
    (by decide) selected_cut_28316

theorem selected_cut_28317 : selected 9 ⟨715604, by decide⟩
    (prefixPartial 12 92304) = some ⟨12, 2, 0, 715604, 92304, 1025, 65536⟩ := by
  decide +kernel

theorem context_12_92304_715604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92304 ⟨715604, by decide⟩ :=
  accepted_of_selected 12 92304 ⟨715604, by decide⟩ ⟨12, 2, 0, 715604, 92304, 1025, 65536⟩
    (by decide) selected_cut_28317

theorem selected_cut_28318 : selected 9 ⟨715628, by decide⟩
    (prefixPartial 12 92305) = some ⟨12, 2, 0, 715628, 92305, 1149, 65536⟩ := by
  decide +kernel

theorem context_12_92305_715628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92305 ⟨715628, by decide⟩ :=
  accepted_of_selected 12 92305 ⟨715628, by decide⟩ ⟨12, 2, 0, 715628, 92305, 1149, 65536⟩
    (by decide) selected_cut_28318

theorem selected_cut_28319 : selected 9 ⟨715651, by decide⟩
    (prefixPartial 12 92306) = some ⟨12, 2, 0, 715651, 92306, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_92306_715651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92306 ⟨715651, by decide⟩ :=
  accepted_of_selected 12 92306 ⟨715651, by decide⟩ ⟨12, 2, 0, 715651, 92306, 1133, 65536⟩
    (by decide) selected_cut_28319

theorem selected_cut_28320 : selected 9 ⟨715668, by decide⟩
    (prefixPartial 12 92307) = some ⟨12, 2, 0, 715668, 92307, 953, 65536⟩ := by
  decide +kernel

theorem context_12_92307_715668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92307 ⟨715668, by decide⟩ :=
  accepted_of_selected 12 92307 ⟨715668, by decide⟩ ⟨12, 2, 0, 715668, 92307, 953, 65536⟩
    (by decide) selected_cut_28320

theorem unmarked_context_11_23076_715669 : frontier 10 ⟨715669, by decide⟩
    (prefixCache 11 23076) (prefixPartial 11 23076) = false := by
  decide +kernel

theorem node_context_11_23076_715669 : EJMOriginalGlobalDAGData.nodes 10 ⟨715669, by decide⟩ =
    .split (coordinate 11) (![⟨715604, by decide⟩,⟨715628, by decide⟩,⟨715651, by decide⟩,⟨715668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23076_715669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23076 ⟨715669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23076
    ⟨715669, by decide⟩ (by decide) (![⟨715604, by decide⟩,⟨715628, by decide⟩,⟨715651, by decide⟩,⟨715668, by decide⟩]) unmarked_context_11_23076_715669 node_context_11_23076_715669
  intro a
  fin_cases a
  · exact context_12_92304_715604
  · exact context_12_92305_715628
  · exact context_12_92306_715651
  · exact context_12_92307_715668

theorem selected_cut_28321 : selected 10 ⟨715725, by decide⟩
    (prefixPartial 11 23077) = some ⟨11, 2, 0, 715725, 23077, 2713, 262144⟩ := by
  decide +kernel

theorem context_11_23077_715725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23077 ⟨715725, by decide⟩ :=
  accepted_of_selected 11 23077 ⟨715725, by decide⟩ ⟨11, 2, 0, 715725, 23077, 2713, 262144⟩
    (by decide) selected_cut_28321

theorem selected_cut_28322 : selected 10 ⟨715756, by decide⟩
    (prefixPartial 11 23078) = some ⟨11, 2, 0, 715756, 23078, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_23078_715756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23078 ⟨715756, by decide⟩ :=
  accepted_of_selected 11 23078 ⟨715756, by decide⟩ ⟨11, 2, 0, 715756, 23078, 1461, 262144⟩
    (by decide) selected_cut_28322

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
