/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover168
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_16228 : selected 8 ⟨413829, by decide⟩
    (prefixPartial 13 112747) = some ⟨13, 2, 0, 413829, 112747, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_112747_413829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112747 ⟨413829, by decide⟩ :=
  accepted_of_selected 13 112747 ⟨413829, by decide⟩ ⟨13, 2, 0, 413829, 112747, 1145, 16384⟩
    (by decide) selected_cut_16228

theorem unmarked_context_12_28186_413830 : frontier 9 ⟨413830, by decide⟩
    (prefixCache 12 28186) (prefixPartial 12 28186) = false := by
  decide +kernel

theorem node_context_12_28186_413830 : EJMOriginalGlobalDAGData.nodes 9 ⟨413830, by decide⟩ =
    .split (coordinate 12) (![⟨413731, by decide⟩,⟨413798, by decide⟩,⟨413822, by decide⟩,⟨413829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28186_413830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28186 ⟨413830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28186
    ⟨413830, by decide⟩ (by decide) (![⟨413731, by decide⟩,⟨413798, by decide⟩,⟨413822, by decide⟩,⟨413829, by decide⟩]) unmarked_context_12_28186_413830 node_context_12_28186_413830
  intro a
  fin_cases a
  · exact context_13_112744_413731
  · exact context_13_112745_413798
  · exact context_13_112746_413822
  · exact context_13_112747_413829

theorem selected_cut_16229 : selected 8 ⟨413857, by decide⟩
    (prefixPartial 13 112748) = some ⟨13, 2, 0, 413857, 112748, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_112748_413857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112748 ⟨413857, by decide⟩ :=
  accepted_of_selected 13 112748 ⟨413857, by decide⟩ ⟨13, 2, 0, 413857, 112748, 1789, 16384⟩
    (by decide) selected_cut_16229

theorem selected_cut_16230 : selected 8 ⟨413894, by decide⟩
    (prefixPartial 13 112749) = some ⟨13, 2, 0, 413894, 112749, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_112749_413894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112749 ⟨413894, by decide⟩ :=
  accepted_of_selected 13 112749 ⟨413894, by decide⟩ ⟨13, 2, 0, 413894, 112749, 2637, 16384⟩
    (by decide) selected_cut_16230

theorem selected_cut_16231 : selected 8 ⟨413915, by decide⟩
    (prefixPartial 13 112750) = some ⟨13, 2, 0, 413915, 112750, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_112750_413915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112750 ⟨413915, by decide⟩ :=
  accepted_of_selected 13 112750 ⟨413915, by decide⟩ ⟨13, 2, 0, 413915, 112750, 1553, 16384⟩
    (by decide) selected_cut_16231

theorem selected_cut_16232 : selected 8 ⟨413923, by decide⟩
    (prefixPartial 13 112751) = some ⟨13, 2, 0, 413923, 112751, 1061, 16384⟩ := by
  decide +kernel

theorem context_13_112751_413923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112751 ⟨413923, by decide⟩ :=
  accepted_of_selected 13 112751 ⟨413923, by decide⟩ ⟨13, 2, 0, 413923, 112751, 1061, 16384⟩
    (by decide) selected_cut_16232

theorem unmarked_context_12_28187_413924 : frontier 9 ⟨413924, by decide⟩
    (prefixCache 12 28187) (prefixPartial 12 28187) = false := by
  decide +kernel

theorem node_context_12_28187_413924 : EJMOriginalGlobalDAGData.nodes 9 ⟨413924, by decide⟩ =
    .split (coordinate 12) (![⟨413857, by decide⟩,⟨413894, by decide⟩,⟨413915, by decide⟩,⟨413923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28187_413924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28187 ⟨413924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28187
    ⟨413924, by decide⟩ (by decide) (![⟨413857, by decide⟩,⟨413894, by decide⟩,⟨413915, by decide⟩,⟨413923, by decide⟩]) unmarked_context_12_28187_413924 node_context_12_28187_413924
  intro a
  fin_cases a
  · exact context_13_112748_413857
  · exact context_13_112749_413894
  · exact context_13_112750_413915
  · exact context_13_112751_413923

theorem unmarked_context_11_7046_413925 : frontier 10 ⟨413925, by decide⟩
    (prefixCache 11 7046) (prefixPartial 11 7046) = false := by
  decide +kernel

theorem node_context_11_7046_413925 : EJMOriginalGlobalDAGData.nodes 10 ⟨413925, by decide⟩ =
    .split (coordinate 11) (![⟨413612, by decide⟩,⟨413691, by decide⟩,⟨413830, by decide⟩,⟨413924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7046_413925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7046 ⟨413925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7046
    ⟨413925, by decide⟩ (by decide) (![⟨413612, by decide⟩,⟨413691, by decide⟩,⟨413830, by decide⟩,⟨413924, by decide⟩]) unmarked_context_11_7046_413925 node_context_11_7046_413925
  intro a
  fin_cases a
  · exact context_12_28184_413612
  · exact context_12_28185_413691
  · exact context_12_28186_413830
  · exact context_12_28187_413924

theorem selected_cut_16233 : selected 8 ⟨413939, by decide⟩
    (prefixPartial 13 112752) = some ⟨13, 2, 0, 413939, 112752, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_112752_413939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112752 ⟨413939, by decide⟩ :=
  accepted_of_selected 13 112752 ⟨413939, by decide⟩ ⟨13, 2, 0, 413939, 112752, 1269, 16384⟩
    (by decide) selected_cut_16233

theorem selected_cut_16234 : selected 8 ⟨413971, by decide⟩
    (prefixPartial 13 112753) = some ⟨13, 2, 0, 413971, 112753, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_112753_413971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112753 ⟨413971, by decide⟩ :=
  accepted_of_selected 13 112753 ⟨413971, by decide⟩ ⟨13, 2, 0, 413971, 112753, 2173, 16384⟩
    (by decide) selected_cut_16234

theorem selected_cut_16235 : selected 8 ⟨413985, by decide⟩
    (prefixPartial 13 112754) = some ⟨13, 2, 0, 413985, 112754, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_112754_413985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112754 ⟨413985, by decide⟩ :=
  accepted_of_selected 13 112754 ⟨413985, by decide⟩ ⟨13, 2, 0, 413985, 112754, 1209, 16384⟩
    (by decide) selected_cut_16235

theorem selected_cut_16236 : selected 8 ⟨413992, by decide⟩
    (prefixPartial 13 112755) = some ⟨13, 2, 0, 413992, 112755, 793, 16384⟩ := by
  decide +kernel

theorem context_13_112755_413992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112755 ⟨413992, by decide⟩ :=
  accepted_of_selected 13 112755 ⟨413992, by decide⟩ ⟨13, 2, 0, 413992, 112755, 793, 16384⟩
    (by decide) selected_cut_16236

theorem unmarked_context_12_28188_413993 : frontier 9 ⟨413993, by decide⟩
    (prefixCache 12 28188) (prefixPartial 12 28188) = false := by
  decide +kernel

theorem node_context_12_28188_413993 : EJMOriginalGlobalDAGData.nodes 9 ⟨413993, by decide⟩ =
    .split (coordinate 12) (![⟨413939, by decide⟩,⟨413971, by decide⟩,⟨413985, by decide⟩,⟨413992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28188_413993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28188 ⟨413993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28188
    ⟨413993, by decide⟩ (by decide) (![⟨413939, by decide⟩,⟨413971, by decide⟩,⟨413985, by decide⟩,⟨413992, by decide⟩]) unmarked_context_12_28188_413993 node_context_12_28188_413993
  intro a
  fin_cases a
  · exact context_13_112752_413939
  · exact context_13_112753_413971
  · exact context_13_112754_413985
  · exact context_13_112755_413992

theorem selected_cut_16237 : selected 8 ⟨414009, by decide⟩
    (prefixPartial 13 112756) = some ⟨13, 2, 0, 414009, 112756, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_112756_414009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112756 ⟨414009, by decide⟩ :=
  accepted_of_selected 13 112756 ⟨414009, by decide⟩ ⟨13, 2, 0, 414009, 112756, 1597, 16384⟩
    (by decide) selected_cut_16237

theorem selected_cut_16238 : selected 8 ⟨414042, by decide⟩
    (prefixPartial 13 112757) = some ⟨13, 2, 0, 414042, 112757, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_112757_414042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112757 ⟨414042, by decide⟩ :=
  accepted_of_selected 13 112757 ⟨414042, by decide⟩ ⟨13, 2, 0, 414042, 112757, 2169, 16384⟩
    (by decide) selected_cut_16238

theorem selected_cut_16239 : selected 8 ⟨414062, by decide⟩
    (prefixPartial 13 112758) = some ⟨13, 2, 0, 414062, 112758, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_112758_414062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112758 ⟨414062, by decide⟩ :=
  accepted_of_selected 13 112758 ⟨414062, by decide⟩ ⟨13, 2, 0, 414062, 112758, 1385, 16384⟩
    (by decide) selected_cut_16239

theorem selected_cut_16240 : selected 8 ⟨414071, by decide⟩
    (prefixPartial 13 112759) = some ⟨13, 2, 0, 414071, 112759, 917, 16384⟩ := by
  decide +kernel

theorem context_13_112759_414071 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112759 ⟨414071, by decide⟩ :=
  accepted_of_selected 13 112759 ⟨414071, by decide⟩ ⟨13, 2, 0, 414071, 112759, 917, 16384⟩
    (by decide) selected_cut_16240

theorem unmarked_context_12_28189_414072 : frontier 9 ⟨414072, by decide⟩
    (prefixCache 12 28189) (prefixPartial 12 28189) = false := by
  decide +kernel

theorem node_context_12_28189_414072 : EJMOriginalGlobalDAGData.nodes 9 ⟨414072, by decide⟩ =
    .split (coordinate 12) (![⟨414009, by decide⟩,⟨414042, by decide⟩,⟨414062, by decide⟩,⟨414071, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28189_414072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28189 ⟨414072, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28189
    ⟨414072, by decide⟩ (by decide) (![⟨414009, by decide⟩,⟨414042, by decide⟩,⟨414062, by decide⟩,⟨414071, by decide⟩]) unmarked_context_12_28189_414072 node_context_12_28189_414072
  intro a
  fin_cases a
  · exact context_13_112756_414009
  · exact context_13_112757_414042
  · exact context_13_112758_414062
  · exact context_13_112759_414071

theorem selected_cut_16241 : selected 8 ⟨414089, by decide⟩
    (prefixPartial 13 112760) = some ⟨13, 2, 0, 414089, 112760, 1369, 16384⟩ := by
  decide +kernel

theorem context_13_112760_414089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112760 ⟨414089, by decide⟩ :=
  accepted_of_selected 13 112760 ⟨414089, by decide⟩ ⟨13, 2, 0, 414089, 112760, 1369, 16384⟩
    (by decide) selected_cut_16241

theorem selected_cut_16242 : selected 8 ⟨414116, by decide⟩
    (prefixPartial 13 112761) = some ⟨13, 2, 0, 414116, 112761, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_112761_414116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112761 ⟨414116, by decide⟩ :=
  accepted_of_selected 13 112761 ⟨414116, by decide⟩ ⟨13, 2, 0, 414116, 112761, 2165, 16384⟩
    (by decide) selected_cut_16242

theorem selected_cut_16243 : selected 8 ⟨414133, by decide⟩
    (prefixPartial 13 112762) = some ⟨13, 2, 0, 414133, 112762, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_112762_414133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112762 ⟨414133, by decide⟩ :=
  accepted_of_selected 13 112762 ⟨414133, by decide⟩ ⟨13, 2, 0, 414133, 112762, 1257, 16384⟩
    (by decide) selected_cut_16243

theorem selected_cut_16244 : selected 8 ⟨414140, by decide⟩
    (prefixPartial 13 112763) = some ⟨13, 2, 0, 414140, 112763, 881, 16384⟩ := by
  decide +kernel

theorem context_13_112763_414140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112763 ⟨414140, by decide⟩ :=
  accepted_of_selected 13 112763 ⟨414140, by decide⟩ ⟨13, 2, 0, 414140, 112763, 881, 16384⟩
    (by decide) selected_cut_16244

theorem unmarked_context_12_28190_414141 : frontier 9 ⟨414141, by decide⟩
    (prefixCache 12 28190) (prefixPartial 12 28190) = false := by
  decide +kernel

theorem node_context_12_28190_414141 : EJMOriginalGlobalDAGData.nodes 9 ⟨414141, by decide⟩ =
    .split (coordinate 12) (![⟨414089, by decide⟩,⟨414116, by decide⟩,⟨414133, by decide⟩,⟨414140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28190_414141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28190 ⟨414141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28190
    ⟨414141, by decide⟩ (by decide) (![⟨414089, by decide⟩,⟨414116, by decide⟩,⟨414133, by decide⟩,⟨414140, by decide⟩]) unmarked_context_12_28190_414141 node_context_12_28190_414141
  intro a
  fin_cases a
  · exact context_13_112760_414089
  · exact context_13_112761_414116
  · exact context_13_112762_414133
  · exact context_13_112763_414140

theorem selected_cut_16245 : selected 8 ⟨414162, by decide⟩
    (prefixPartial 13 112764) = some ⟨13, 2, 0, 414162, 112764, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_112764_414162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112764 ⟨414162, by decide⟩ :=
  accepted_of_selected 13 112764 ⟨414162, by decide⟩ ⟨13, 2, 0, 414162, 112764, 1661, 16384⟩
    (by decide) selected_cut_16245

theorem selected_cut_16246 : selected 8 ⟨414195, by decide⟩
    (prefixPartial 13 112765) = some ⟨13, 2, 0, 414195, 112765, 2525, 16384⟩ := by
  decide +kernel

theorem context_13_112765_414195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112765 ⟨414195, by decide⟩ :=
  accepted_of_selected 13 112765 ⟨414195, by decide⟩ ⟨13, 2, 0, 414195, 112765, 2525, 16384⟩
    (by decide) selected_cut_16246

theorem selected_cut_16247 : selected 8 ⟨414212, by decide⟩
    (prefixPartial 13 112766) = some ⟨13, 2, 0, 414212, 112766, 1713, 16384⟩ := by
  decide +kernel

theorem context_13_112766_414212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112766 ⟨414212, by decide⟩ :=
  accepted_of_selected 13 112766 ⟨414212, by decide⟩ ⟨13, 2, 0, 414212, 112766, 1713, 16384⟩
    (by decide) selected_cut_16247

theorem selected_cut_16248 : selected 8 ⟨414218, by decide⟩
    (prefixPartial 13 112767) = some ⟨13, 2, 0, 414218, 112767, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_112767_414218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112767 ⟨414218, by decide⟩ :=
  accepted_of_selected 13 112767 ⟨414218, by decide⟩ ⟨13, 2, 0, 414218, 112767, 1049, 16384⟩
    (by decide) selected_cut_16248

theorem unmarked_context_12_28191_414219 : frontier 9 ⟨414219, by decide⟩
    (prefixCache 12 28191) (prefixPartial 12 28191) = false := by
  decide +kernel

theorem node_context_12_28191_414219 : EJMOriginalGlobalDAGData.nodes 9 ⟨414219, by decide⟩ =
    .split (coordinate 12) (![⟨414162, by decide⟩,⟨414195, by decide⟩,⟨414212, by decide⟩,⟨414218, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28191_414219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28191 ⟨414219, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28191
    ⟨414219, by decide⟩ (by decide) (![⟨414162, by decide⟩,⟨414195, by decide⟩,⟨414212, by decide⟩,⟨414218, by decide⟩]) unmarked_context_12_28191_414219 node_context_12_28191_414219
  intro a
  fin_cases a
  · exact context_13_112764_414162
  · exact context_13_112765_414195
  · exact context_13_112766_414212
  · exact context_13_112767_414218

theorem unmarked_context_11_7047_414220 : frontier 10 ⟨414220, by decide⟩
    (prefixCache 11 7047) (prefixPartial 11 7047) = false := by
  decide +kernel

theorem node_context_11_7047_414220 : EJMOriginalGlobalDAGData.nodes 10 ⟨414220, by decide⟩ =
    .split (coordinate 11) (![⟨413993, by decide⟩,⟨414072, by decide⟩,⟨414141, by decide⟩,⟨414219, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7047_414220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7047 ⟨414220, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7047
    ⟨414220, by decide⟩ (by decide) (![⟨413993, by decide⟩,⟨414072, by decide⟩,⟨414141, by decide⟩,⟨414219, by decide⟩]) unmarked_context_11_7047_414220 node_context_11_7047_414220
  intro a
  fin_cases a
  · exact context_12_28188_413993
  · exact context_12_28189_414072
  · exact context_12_28190_414141
  · exact context_12_28191_414219

theorem unmarked_context_10_1761_414221 : frontier 11 ⟨414221, by decide⟩
    (prefixCache 10 1761) (prefixPartial 10 1761) = false := by
  decide +kernel

theorem node_context_10_1761_414221 : EJMOriginalGlobalDAGData.nodes 11 ⟨414221, by decide⟩ =
    .split (coordinate 10) (![⟨413209, by decide⟩,⟨413542, by decide⟩,⟨413925, by decide⟩,⟨414220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1761_414221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1761 ⟨414221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1761
    ⟨414221, by decide⟩ (by decide) (![⟨413209, by decide⟩,⟨413542, by decide⟩,⟨413925, by decide⟩,⟨414220, by decide⟩]) unmarked_context_10_1761_414221 node_context_10_1761_414221
  intro a
  fin_cases a
  · exact context_11_7044_413209
  · exact context_11_7045_413542
  · exact context_11_7046_413925
  · exact context_11_7047_414220

theorem selected_cut_16249 : selected 8 ⟨414234, by decide⟩
    (prefixPartial 13 112768) = some ⟨13, 2, 0, 414234, 112768, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_112768_414234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112768 ⟨414234, by decide⟩ :=
  accepted_of_selected 13 112768 ⟨414234, by decide⟩ ⟨13, 2, 0, 414234, 112768, 1141, 16384⟩
    (by decide) selected_cut_16249

theorem selected_cut_16250 : selected 8 ⟨414258, by decide⟩
    (prefixPartial 13 112769) = some ⟨13, 2, 0, 414258, 112769, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_112769_414258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112769 ⟨414258, by decide⟩ :=
  accepted_of_selected 13 112769 ⟨414258, by decide⟩ ⟨13, 2, 0, 414258, 112769, 1993, 16384⟩
    (by decide) selected_cut_16250

theorem selected_cut_16251 : selected 8 ⟨414273, by decide⟩
    (prefixPartial 13 112770) = some ⟨13, 2, 0, 414273, 112770, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_112770_414273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112770 ⟨414273, by decide⟩ :=
  accepted_of_selected 13 112770 ⟨414273, by decide⟩ ⟨13, 2, 0, 414273, 112770, 1137, 16384⟩
    (by decide) selected_cut_16251

theorem selected_cut_16252 : selected 8 ⟨414280, by decide⟩
    (prefixPartial 13 112771) = some ⟨13, 2, 0, 414280, 112771, 649, 16384⟩ := by
  decide +kernel

theorem context_13_112771_414280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112771 ⟨414280, by decide⟩ :=
  accepted_of_selected 13 112771 ⟨414280, by decide⟩ ⟨13, 2, 0, 414280, 112771, 649, 16384⟩
    (by decide) selected_cut_16252

theorem unmarked_context_12_28192_414281 : frontier 9 ⟨414281, by decide⟩
    (prefixCache 12 28192) (prefixPartial 12 28192) = false := by
  decide +kernel

theorem node_context_12_28192_414281 : EJMOriginalGlobalDAGData.nodes 9 ⟨414281, by decide⟩ =
    .split (coordinate 12) (![⟨414234, by decide⟩,⟨414258, by decide⟩,⟨414273, by decide⟩,⟨414280, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28192_414281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28192 ⟨414281, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28192
    ⟨414281, by decide⟩ (by decide) (![⟨414234, by decide⟩,⟨414258, by decide⟩,⟨414273, by decide⟩,⟨414280, by decide⟩]) unmarked_context_12_28192_414281 node_context_12_28192_414281
  intro a
  fin_cases a
  · exact context_13_112768_414234
  · exact context_13_112769_414258
  · exact context_13_112770_414273
  · exact context_13_112771_414280

theorem selected_cut_16253 : selected 8 ⟨414295, by decide⟩
    (prefixPartial 13 112772) = some ⟨13, 2, 0, 414295, 112772, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_112772_414295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112772 ⟨414295, by decide⟩ :=
  accepted_of_selected 13 112772 ⟨414295, by decide⟩ ⟨13, 2, 0, 414295, 112772, 1337, 16384⟩
    (by decide) selected_cut_16253

theorem selected_cut_16254 : selected 8 ⟨414330, by decide⟩
    (prefixPartial 13 112773) = some ⟨13, 2, 0, 414330, 112773, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_112773_414330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112773 ⟨414330, by decide⟩ :=
  accepted_of_selected 13 112773 ⟨414330, by decide⟩ ⟨13, 2, 0, 414330, 112773, 2425, 16384⟩
    (by decide) selected_cut_16254

theorem selected_cut_16255 : selected 8 ⟨414349, by decide⟩
    (prefixPartial 13 112774) = some ⟨13, 2, 0, 414349, 112774, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_112774_414349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112774 ⟨414349, by decide⟩ :=
  accepted_of_selected 13 112774 ⟨414349, by decide⟩ ⟨13, 2, 0, 414349, 112774, 1593, 16384⟩
    (by decide) selected_cut_16255

theorem selected_cut_16256 : selected 8 ⟨414355, by decide⟩
    (prefixPartial 13 112775) = some ⟨13, 2, 0, 414355, 112775, 897, 16384⟩ := by
  decide +kernel

theorem context_13_112775_414355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112775 ⟨414355, by decide⟩ :=
  accepted_of_selected 13 112775 ⟨414355, by decide⟩ ⟨13, 2, 0, 414355, 112775, 897, 16384⟩
    (by decide) selected_cut_16256

theorem unmarked_context_12_28193_414356 : frontier 9 ⟨414356, by decide⟩
    (prefixCache 12 28193) (prefixPartial 12 28193) = false := by
  decide +kernel

theorem node_context_12_28193_414356 : EJMOriginalGlobalDAGData.nodes 9 ⟨414356, by decide⟩ =
    .split (coordinate 12) (![⟨414295, by decide⟩,⟨414330, by decide⟩,⟨414349, by decide⟩,⟨414355, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28193_414356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28193 ⟨414356, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28193
    ⟨414356, by decide⟩ (by decide) (![⟨414295, by decide⟩,⟨414330, by decide⟩,⟨414349, by decide⟩,⟨414355, by decide⟩]) unmarked_context_12_28193_414356 node_context_12_28193_414356
  intro a
  fin_cases a
  · exact context_13_112772_414295
  · exact context_13_112773_414330
  · exact context_13_112774_414349
  · exact context_13_112775_414355

theorem selected_cut_16257 : selected 8 ⟨414369, by decide⟩
    (prefixPartial 13 112776) = some ⟨13, 2, 0, 414369, 112776, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_112776_414369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112776 ⟨414369, by decide⟩ :=
  accepted_of_selected 13 112776 ⟨414369, by decide⟩ ⟨13, 2, 0, 414369, 112776, 1173, 16384⟩
    (by decide) selected_cut_16257

theorem selected_cut_16258 : selected 8 ⟨414392, by decide⟩
    (prefixPartial 13 112777) = some ⟨13, 2, 0, 414392, 112777, 2017, 16384⟩ := by
  decide +kernel

theorem context_13_112777_414392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112777 ⟨414392, by decide⟩ :=
  accepted_of_selected 13 112777 ⟨414392, by decide⟩ ⟨13, 2, 0, 414392, 112777, 2017, 16384⟩
    (by decide) selected_cut_16258

theorem selected_cut_16259 : selected 8 ⟨414406, by decide⟩
    (prefixPartial 13 112778) = some ⟨13, 2, 0, 414406, 112778, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_112778_414406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112778 ⟨414406, by decide⟩ :=
  accepted_of_selected 13 112778 ⟨414406, by decide⟩ ⟨13, 2, 0, 414406, 112778, 1145, 16384⟩
    (by decide) selected_cut_16259

theorem selected_cut_16260 : selected 8 ⟨414413, by decide⟩
    (prefixPartial 13 112779) = some ⟨13, 2, 0, 414413, 112779, 833, 16384⟩ := by
  decide +kernel

theorem context_13_112779_414413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112779 ⟨414413, by decide⟩ :=
  accepted_of_selected 13 112779 ⟨414413, by decide⟩ ⟨13, 2, 0, 414413, 112779, 833, 16384⟩
    (by decide) selected_cut_16260

theorem unmarked_context_12_28194_414414 : frontier 9 ⟨414414, by decide⟩
    (prefixCache 12 28194) (prefixPartial 12 28194) = false := by
  decide +kernel

theorem node_context_12_28194_414414 : EJMOriginalGlobalDAGData.nodes 9 ⟨414414, by decide⟩ =
    .split (coordinate 12) (![⟨414369, by decide⟩,⟨414392, by decide⟩,⟨414406, by decide⟩,⟨414413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28194_414414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28194 ⟨414414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28194
    ⟨414414, by decide⟩ (by decide) (![⟨414369, by decide⟩,⟨414392, by decide⟩,⟨414406, by decide⟩,⟨414413, by decide⟩]) unmarked_context_12_28194_414414 node_context_12_28194_414414
  intro a
  fin_cases a
  · exact context_13_112776_414369
  · exact context_13_112777_414392
  · exact context_13_112778_414406
  · exact context_13_112779_414413

theorem selected_cut_16261 : selected 8 ⟨414428, by decide⟩
    (prefixPartial 13 112780) = some ⟨13, 2, 0, 414428, 112780, 1389, 16384⟩ := by
  decide +kernel

theorem context_13_112780_414428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112780 ⟨414428, by decide⟩ :=
  accepted_of_selected 13 112780 ⟨414428, by decide⟩ ⟨13, 2, 0, 414428, 112780, 1389, 16384⟩
    (by decide) selected_cut_16261

theorem selected_cut_16262 : selected 8 ⟨414469, by decide⟩
    (prefixPartial 13 112781) = some ⟨13, 2, 0, 414469, 112781, 2657, 16384⟩ := by
  decide +kernel

theorem context_13_112781_414469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112781 ⟨414469, by decide⟩ :=
  accepted_of_selected 13 112781 ⟨414469, by decide⟩ ⟨13, 2, 0, 414469, 112781, 2657, 16384⟩
    (by decide) selected_cut_16262

theorem selected_cut_16263 : selected 8 ⟨414496, by decide⟩
    (prefixPartial 13 112782) = some ⟨13, 2, 0, 414496, 112782, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_112782_414496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112782 ⟨414496, by decide⟩ :=
  accepted_of_selected 13 112782 ⟨414496, by decide⟩ ⟨13, 2, 0, 414496, 112782, 1741, 16384⟩
    (by decide) selected_cut_16263

theorem selected_cut_16264 : selected 8 ⟨414507, by decide⟩
    (prefixPartial 13 112783) = some ⟨13, 2, 0, 414507, 112783, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_112783_414507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112783 ⟨414507, by decide⟩ :=
  accepted_of_selected 13 112783 ⟨414507, by decide⟩ ⟨13, 2, 0, 414507, 112783, 1009, 16384⟩
    (by decide) selected_cut_16264

theorem unmarked_context_12_28195_414508 : frontier 9 ⟨414508, by decide⟩
    (prefixCache 12 28195) (prefixPartial 12 28195) = false := by
  decide +kernel

theorem node_context_12_28195_414508 : EJMOriginalGlobalDAGData.nodes 9 ⟨414508, by decide⟩ =
    .split (coordinate 12) (![⟨414428, by decide⟩,⟨414469, by decide⟩,⟨414496, by decide⟩,⟨414507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28195_414508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28195 ⟨414508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28195
    ⟨414508, by decide⟩ (by decide) (![⟨414428, by decide⟩,⟨414469, by decide⟩,⟨414496, by decide⟩,⟨414507, by decide⟩]) unmarked_context_12_28195_414508 node_context_12_28195_414508
  intro a
  fin_cases a
  · exact context_13_112780_414428
  · exact context_13_112781_414469
  · exact context_13_112782_414496
  · exact context_13_112783_414507

theorem unmarked_context_11_7048_414509 : frontier 10 ⟨414509, by decide⟩
    (prefixCache 11 7048) (prefixPartial 11 7048) = false := by
  decide +kernel

theorem node_context_11_7048_414509 : EJMOriginalGlobalDAGData.nodes 10 ⟨414509, by decide⟩ =
    .split (coordinate 11) (![⟨414281, by decide⟩,⟨414356, by decide⟩,⟨414414, by decide⟩,⟨414508, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7048_414509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7048 ⟨414509, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7048
    ⟨414509, by decide⟩ (by decide) (![⟨414281, by decide⟩,⟨414356, by decide⟩,⟨414414, by decide⟩,⟨414508, by decide⟩]) unmarked_context_11_7048_414509 node_context_11_7048_414509
  intro a
  fin_cases a
  · exact context_12_28192_414281
  · exact context_12_28193_414356
  · exact context_12_28194_414414
  · exact context_12_28195_414508

theorem selected_cut_16265 : selected 8 ⟨414521, by decide⟩
    (prefixPartial 13 112784) = some ⟨13, 2, 0, 414521, 112784, 969, 16384⟩ := by
  decide +kernel

theorem context_13_112784_414521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112784 ⟨414521, by decide⟩ :=
  accepted_of_selected 13 112784 ⟨414521, by decide⟩ ⟨13, 2, 0, 414521, 112784, 969, 16384⟩
    (by decide) selected_cut_16265

theorem selected_cut_16266 : selected 8 ⟨414547, by decide⟩
    (prefixPartial 13 112785) = some ⟨13, 2, 0, 414547, 112785, 2145, 16384⟩ := by
  decide +kernel

theorem context_13_112785_414547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112785 ⟨414547, by decide⟩ :=
  accepted_of_selected 13 112785 ⟨414547, by decide⟩ ⟨13, 2, 0, 414547, 112785, 2145, 16384⟩
    (by decide) selected_cut_16266

theorem selected_cut_16267 : selected 8 ⟨414562, by decide⟩
    (prefixPartial 13 112786) = some ⟨13, 2, 0, 414562, 112786, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_112786_414562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112786 ⟨414562, by decide⟩ :=
  accepted_of_selected 13 112786 ⟨414562, by decide⟩ ⟨13, 2, 0, 414562, 112786, 1237, 16384⟩
    (by decide) selected_cut_16267

theorem selected_cut_16268 : selected 8 ⟨414570, by decide⟩
    (prefixPartial 13 112787) = some ⟨13, 2, 0, 414570, 112787, 673, 16384⟩ := by
  decide +kernel

theorem context_13_112787_414570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112787 ⟨414570, by decide⟩ :=
  accepted_of_selected 13 112787 ⟨414570, by decide⟩ ⟨13, 2, 0, 414570, 112787, 673, 16384⟩
    (by decide) selected_cut_16268

theorem unmarked_context_12_28196_414571 : frontier 9 ⟨414571, by decide⟩
    (prefixCache 12 28196) (prefixPartial 12 28196) = false := by
  decide +kernel

theorem node_context_12_28196_414571 : EJMOriginalGlobalDAGData.nodes 9 ⟨414571, by decide⟩ =
    .split (coordinate 12) (![⟨414521, by decide⟩,⟨414547, by decide⟩,⟨414562, by decide⟩,⟨414570, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28196_414571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28196 ⟨414571, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28196
    ⟨414571, by decide⟩ (by decide) (![⟨414521, by decide⟩,⟨414547, by decide⟩,⟨414562, by decide⟩,⟨414570, by decide⟩]) unmarked_context_12_28196_414571 node_context_12_28196_414571
  intro a
  fin_cases a
  · exact context_13_112784_414521
  · exact context_13_112785_414547
  · exact context_13_112786_414562
  · exact context_13_112787_414570

theorem selected_cut_16269 : selected 8 ⟨414583, by decide⟩
    (prefixPartial 13 112788) = some ⟨13, 2, 0, 414583, 112788, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_112788_414583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112788 ⟨414583, by decide⟩ :=
  accepted_of_selected 13 112788 ⟨414583, by decide⟩ ⟨13, 2, 0, 414583, 112788, 1073, 16384⟩
    (by decide) selected_cut_16269

theorem selected_cut_16270 : selected 8 ⟨414608, by decide⟩
    (prefixPartial 13 112789) = some ⟨13, 2, 0, 414608, 112789, 2021, 16384⟩ := by
  decide +kernel

theorem context_13_112789_414608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112789 ⟨414608, by decide⟩ :=
  accepted_of_selected 13 112789 ⟨414608, by decide⟩ ⟨13, 2, 0, 414608, 112789, 2021, 16384⟩
    (by decide) selected_cut_16270

theorem selected_cut_16271 : selected 8 ⟨414623, by decide⟩
    (prefixPartial 13 112790) = some ⟨13, 2, 0, 414623, 112790, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_112790_414623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112790 ⟨414623, by decide⟩ :=
  accepted_of_selected 13 112790 ⟨414623, by decide⟩ ⟨13, 2, 0, 414623, 112790, 1509, 16384⟩
    (by decide) selected_cut_16271

theorem selected_cut_16272 : selected 8 ⟨414632, by decide⟩
    (prefixPartial 13 112791) = some ⟨13, 2, 0, 414632, 112791, 833, 16384⟩ := by
  decide +kernel

theorem context_13_112791_414632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112791 ⟨414632, by decide⟩ :=
  accepted_of_selected 13 112791 ⟨414632, by decide⟩ ⟨13, 2, 0, 414632, 112791, 833, 16384⟩
    (by decide) selected_cut_16272

theorem unmarked_context_12_28197_414633 : frontier 9 ⟨414633, by decide⟩
    (prefixCache 12 28197) (prefixPartial 12 28197) = false := by
  decide +kernel

theorem node_context_12_28197_414633 : EJMOriginalGlobalDAGData.nodes 9 ⟨414633, by decide⟩ =
    .split (coordinate 12) (![⟨414583, by decide⟩,⟨414608, by decide⟩,⟨414623, by decide⟩,⟨414632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28197_414633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28197 ⟨414633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28197
    ⟨414633, by decide⟩ (by decide) (![⟨414583, by decide⟩,⟨414608, by decide⟩,⟨414623, by decide⟩,⟨414632, by decide⟩]) unmarked_context_12_28197_414633 node_context_12_28197_414633
  intro a
  fin_cases a
  · exact context_13_112788_414583
  · exact context_13_112789_414608
  · exact context_13_112790_414623
  · exact context_13_112791_414632

theorem selected_cut_16273 : selected 8 ⟨414645, by decide⟩
    (prefixPartial 13 112792) = some ⟨13, 2, 0, 414645, 112792, 973, 16384⟩ := by
  decide +kernel

theorem context_13_112792_414645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112792 ⟨414645, by decide⟩ :=
  accepted_of_selected 13 112792 ⟨414645, by decide⟩ ⟨13, 2, 0, 414645, 112792, 973, 16384⟩
    (by decide) selected_cut_16273

theorem selected_cut_16274 : selected 8 ⟨414669, by decide⟩
    (prefixPartial 13 112793) = some ⟨13, 2, 0, 414669, 112793, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_112793_414669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112793 ⟨414669, by decide⟩ :=
  accepted_of_selected 13 112793 ⟨414669, by decide⟩ ⟨13, 2, 0, 414669, 112793, 1753, 16384⟩
    (by decide) selected_cut_16274

theorem selected_cut_16275 : selected 8 ⟨414683, by decide⟩
    (prefixPartial 13 112794) = some ⟨13, 2, 0, 414683, 112794, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_112794_414683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112794 ⟨414683, by decide⟩ :=
  accepted_of_selected 13 112794 ⟨414683, by decide⟩ ⟨13, 2, 0, 414683, 112794, 1129, 16384⟩
    (by decide) selected_cut_16275

theorem selected_cut_16276 : selected 8 ⟨414693, by decide⟩
    (prefixPartial 13 112795) = some ⟨13, 2, 0, 414693, 112795, 833, 16384⟩ := by
  decide +kernel

theorem context_13_112795_414693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112795 ⟨414693, by decide⟩ :=
  accepted_of_selected 13 112795 ⟨414693, by decide⟩ ⟨13, 2, 0, 414693, 112795, 833, 16384⟩
    (by decide) selected_cut_16276

theorem unmarked_context_12_28198_414694 : frontier 9 ⟨414694, by decide⟩
    (prefixCache 12 28198) (prefixPartial 12 28198) = false := by
  decide +kernel

theorem node_context_12_28198_414694 : EJMOriginalGlobalDAGData.nodes 9 ⟨414694, by decide⟩ =
    .split (coordinate 12) (![⟨414645, by decide⟩,⟨414669, by decide⟩,⟨414683, by decide⟩,⟨414693, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28198_414694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28198 ⟨414694, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28198
    ⟨414694, by decide⟩ (by decide) (![⟨414645, by decide⟩,⟨414669, by decide⟩,⟨414683, by decide⟩,⟨414693, by decide⟩]) unmarked_context_12_28198_414694 node_context_12_28198_414694
  intro a
  fin_cases a
  · exact context_13_112792_414645
  · exact context_13_112793_414669
  · exact context_13_112794_414683
  · exact context_13_112795_414693

theorem selected_cut_16277 : selected 8 ⟨414706, by decide⟩
    (prefixPartial 13 112796) = some ⟨13, 2, 0, 414706, 112796, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_112796_414706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112796 ⟨414706, by decide⟩ :=
  accepted_of_selected 13 112796 ⟨414706, by decide⟩ ⟨13, 2, 0, 414706, 112796, 1141, 16384⟩
    (by decide) selected_cut_16277

theorem selected_cut_16278 : selected 8 ⟨414734, by decide⟩
    (prefixPartial 13 112797) = some ⟨13, 2, 0, 414734, 112797, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_112797_414734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112797 ⟨414734, by decide⟩ :=
  accepted_of_selected 13 112797 ⟨414734, by decide⟩ ⟨13, 2, 0, 414734, 112797, 2345, 16384⟩
    (by decide) selected_cut_16278

theorem selected_cut_16279 : selected 8 ⟨414755, by decide⟩
    (prefixPartial 13 112798) = some ⟨13, 2, 0, 414755, 112798, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_112798_414755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112798 ⟨414755, by decide⟩ :=
  accepted_of_selected 13 112798 ⟨414755, by decide⟩ ⟨13, 2, 0, 414755, 112798, 1597, 16384⟩
    (by decide) selected_cut_16279

theorem selected_cut_16280 : selected 8 ⟨414765, by decide⟩
    (prefixPartial 13 112799) = some ⟨13, 2, 0, 414765, 112799, 965, 16384⟩ := by
  decide +kernel

theorem context_13_112799_414765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112799 ⟨414765, by decide⟩ :=
  accepted_of_selected 13 112799 ⟨414765, by decide⟩ ⟨13, 2, 0, 414765, 112799, 965, 16384⟩
    (by decide) selected_cut_16280

theorem unmarked_context_12_28199_414766 : frontier 9 ⟨414766, by decide⟩
    (prefixCache 12 28199) (prefixPartial 12 28199) = false := by
  decide +kernel

theorem node_context_12_28199_414766 : EJMOriginalGlobalDAGData.nodes 9 ⟨414766, by decide⟩ =
    .split (coordinate 12) (![⟨414706, by decide⟩,⟨414734, by decide⟩,⟨414755, by decide⟩,⟨414765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28199_414766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28199 ⟨414766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28199
    ⟨414766, by decide⟩ (by decide) (![⟨414706, by decide⟩,⟨414734, by decide⟩,⟨414755, by decide⟩,⟨414765, by decide⟩]) unmarked_context_12_28199_414766 node_context_12_28199_414766
  intro a
  fin_cases a
  · exact context_13_112796_414706
  · exact context_13_112797_414734
  · exact context_13_112798_414755
  · exact context_13_112799_414765

theorem unmarked_context_11_7049_414767 : frontier 10 ⟨414767, by decide⟩
    (prefixCache 11 7049) (prefixPartial 11 7049) = false := by
  decide +kernel

theorem node_context_11_7049_414767 : EJMOriginalGlobalDAGData.nodes 10 ⟨414767, by decide⟩ =
    .split (coordinate 11) (![⟨414571, by decide⟩,⟨414633, by decide⟩,⟨414694, by decide⟩,⟨414766, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7049_414767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7049 ⟨414767, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7049
    ⟨414767, by decide⟩ (by decide) (![⟨414571, by decide⟩,⟨414633, by decide⟩,⟨414694, by decide⟩,⟨414766, by decide⟩]) unmarked_context_11_7049_414767 node_context_11_7049_414767
  intro a
  fin_cases a
  · exact context_12_28196_414571
  · exact context_12_28197_414633
  · exact context_12_28198_414694
  · exact context_12_28199_414766

theorem selected_cut_16281 : selected 8 ⟨414778, by decide⟩
    (prefixPartial 13 112800) = some ⟨13, 2, 0, 414778, 112800, 693, 16384⟩ := by
  decide +kernel

theorem context_13_112800_414778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112800 ⟨414778, by decide⟩ :=
  accepted_of_selected 13 112800 ⟨414778, by decide⟩ ⟨13, 2, 0, 414778, 112800, 693, 16384⟩
    (by decide) selected_cut_16281

theorem selected_cut_16282 : selected 8 ⟨414807, by decide⟩
    (prefixPartial 13 112801) = some ⟨13, 2, 0, 414807, 112801, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_112801_414807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112801 ⟨414807, by decide⟩ :=
  accepted_of_selected 13 112801 ⟨414807, by decide⟩ ⟨13, 2, 0, 414807, 112801, 1809, 16384⟩
    (by decide) selected_cut_16282

theorem selected_cut_16283 : selected 8 ⟨414821, by decide⟩
    (prefixPartial 13 112802) = some ⟨13, 2, 0, 414821, 112802, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_112802_414821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112802 ⟨414821, by decide⟩ :=
  accepted_of_selected 13 112802 ⟨414821, by decide⟩ ⟨13, 2, 0, 414821, 112802, 1017, 16384⟩
    (by decide) selected_cut_16283

theorem selected_cut_16284 : selected 8 ⟨414828, by decide⟩
    (prefixPartial 13 112803) = some ⟨13, 2, 0, 414828, 112803, 617, 16384⟩ := by
  decide +kernel

theorem context_13_112803_414828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112803 ⟨414828, by decide⟩ :=
  accepted_of_selected 13 112803 ⟨414828, by decide⟩ ⟨13, 2, 0, 414828, 112803, 617, 16384⟩
    (by decide) selected_cut_16284

theorem unmarked_context_12_28200_414829 : frontier 9 ⟨414829, by decide⟩
    (prefixCache 12 28200) (prefixPartial 12 28200) = false := by
  decide +kernel

theorem node_context_12_28200_414829 : EJMOriginalGlobalDAGData.nodes 9 ⟨414829, by decide⟩ =
    .split (coordinate 12) (![⟨414778, by decide⟩,⟨414807, by decide⟩,⟨414821, by decide⟩,⟨414828, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28200_414829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28200 ⟨414829, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28200
    ⟨414829, by decide⟩ (by decide) (![⟨414778, by decide⟩,⟨414807, by decide⟩,⟨414821, by decide⟩,⟨414828, by decide⟩]) unmarked_context_12_28200_414829 node_context_12_28200_414829
  intro a
  fin_cases a
  · exact context_13_112800_414778
  · exact context_13_112801_414807
  · exact context_13_112802_414821
  · exact context_13_112803_414828

theorem selected_cut_16285 : selected 8 ⟨414839, by decide⟩
    (prefixPartial 13 112804) = some ⟨13, 2, 0, 414839, 112804, 765, 16384⟩ := by
  decide +kernel

theorem context_13_112804_414839 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112804 ⟨414839, by decide⟩ :=
  accepted_of_selected 13 112804 ⟨414839, by decide⟩ ⟨13, 2, 0, 414839, 112804, 765, 16384⟩
    (by decide) selected_cut_16285

theorem selected_cut_16286 : selected 8 ⟨414871, by decide⟩
    (prefixPartial 13 112805) = some ⟨13, 2, 0, 414871, 112805, 2041, 16384⟩ := by
  decide +kernel

theorem context_13_112805_414871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112805 ⟨414871, by decide⟩ :=
  accepted_of_selected 13 112805 ⟨414871, by decide⟩ ⟨13, 2, 0, 414871, 112805, 2041, 16384⟩
    (by decide) selected_cut_16286

theorem selected_cut_16287 : selected 8 ⟨414889, by decide⟩
    (prefixPartial 13 112806) = some ⟨13, 2, 0, 414889, 112806, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_112806_414889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112806 ⟨414889, by decide⟩ :=
  accepted_of_selected 13 112806 ⟨414889, by decide⟩ ⟨13, 2, 0, 414889, 112806, 1281, 16384⟩
    (by decide) selected_cut_16287

theorem selected_cut_16288 : selected 8 ⟨414898, by decide⟩
    (prefixPartial 13 112807) = some ⟨13, 2, 0, 414898, 112807, 809, 16384⟩ := by
  decide +kernel

theorem context_13_112807_414898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112807 ⟨414898, by decide⟩ :=
  accepted_of_selected 13 112807 ⟨414898, by decide⟩ ⟨13, 2, 0, 414898, 112807, 809, 16384⟩
    (by decide) selected_cut_16288

theorem unmarked_context_12_28201_414899 : frontier 9 ⟨414899, by decide⟩
    (prefixCache 12 28201) (prefixPartial 12 28201) = false := by
  decide +kernel

theorem node_context_12_28201_414899 : EJMOriginalGlobalDAGData.nodes 9 ⟨414899, by decide⟩ =
    .split (coordinate 12) (![⟨414839, by decide⟩,⟨414871, by decide⟩,⟨414889, by decide⟩,⟨414898, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28201_414899 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28201 ⟨414899, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28201
    ⟨414899, by decide⟩ (by decide) (![⟨414839, by decide⟩,⟨414871, by decide⟩,⟨414889, by decide⟩,⟨414898, by decide⟩]) unmarked_context_12_28201_414899 node_context_12_28201_414899
  intro a
  fin_cases a
  · exact context_13_112804_414839
  · exact context_13_112805_414871
  · exact context_13_112806_414889
  · exact context_13_112807_414898

theorem selected_cut_16289 : selected 9 ⟨415122, by decide⟩
    (prefixPartial 12 28202) = some ⟨12, 2, 0, 415122, 28202, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_28202_415122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28202 ⟨415122, by decide⟩ :=
  accepted_of_selected 12 28202 ⟨415122, by decide⟩ ⟨12, 2, 0, 415122, 28202, 4089, 65536⟩
    (by decide) selected_cut_16289

theorem selected_cut_16290 : selected 8 ⟨415132, by decide⟩
    (prefixPartial 13 112812) = some ⟨13, 2, 0, 415132, 112812, 777, 16384⟩ := by
  decide +kernel

theorem context_13_112812_415132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112812 ⟨415132, by decide⟩ :=
  accepted_of_selected 13 112812 ⟨415132, by decide⟩ ⟨13, 2, 0, 415132, 112812, 777, 16384⟩
    (by decide) selected_cut_16290

theorem selected_cut_16291 : selected 8 ⟨415163, by decide⟩
    (prefixPartial 13 112813) = some ⟨13, 2, 0, 415163, 112813, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_112813_415163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112813 ⟨415163, by decide⟩ :=
  accepted_of_selected 13 112813 ⟨415163, by decide⟩ ⟨13, 2, 0, 415163, 112813, 2309, 16384⟩
    (by decide) selected_cut_16291

theorem selected_cut_16292 : selected 8 ⟨415181, by decide⟩
    (prefixPartial 13 112814) = some ⟨13, 2, 0, 415181, 112814, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_112814_415181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112814 ⟨415181, by decide⟩ :=
  accepted_of_selected 13 112814 ⟨415181, by decide⟩ ⟨13, 2, 0, 415181, 112814, 1293, 16384⟩
    (by decide) selected_cut_16292

theorem selected_cut_16293 : selected 8 ⟨415189, by decide⟩
    (prefixPartial 13 112815) = some ⟨13, 2, 0, 415189, 112815, 849, 16384⟩ := by
  decide +kernel

theorem context_13_112815_415189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112815 ⟨415189, by decide⟩ :=
  accepted_of_selected 13 112815 ⟨415189, by decide⟩ ⟨13, 2, 0, 415189, 112815, 849, 16384⟩
    (by decide) selected_cut_16293

theorem unmarked_context_12_28203_415190 : frontier 9 ⟨415190, by decide⟩
    (prefixCache 12 28203) (prefixPartial 12 28203) = false := by
  decide +kernel

theorem node_context_12_28203_415190 : EJMOriginalGlobalDAGData.nodes 9 ⟨415190, by decide⟩ =
    .split (coordinate 12) (![⟨415132, by decide⟩,⟨415163, by decide⟩,⟨415181, by decide⟩,⟨415189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28203_415190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28203 ⟨415190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28203
    ⟨415190, by decide⟩ (by decide) (![⟨415132, by decide⟩,⟨415163, by decide⟩,⟨415181, by decide⟩,⟨415189, by decide⟩]) unmarked_context_12_28203_415190 node_context_12_28203_415190
  intro a
  fin_cases a
  · exact context_13_112812_415132
  · exact context_13_112813_415163
  · exact context_13_112814_415181
  · exact context_13_112815_415189

theorem unmarked_context_11_7050_415191 : frontier 10 ⟨415191, by decide⟩
    (prefixCache 11 7050) (prefixPartial 11 7050) = false := by
  decide +kernel

theorem node_context_11_7050_415191 : EJMOriginalGlobalDAGData.nodes 10 ⟨415191, by decide⟩ =
    .split (coordinate 11) (![⟨414829, by decide⟩,⟨414899, by decide⟩,⟨415122, by decide⟩,⟨415190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7050_415191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7050 ⟨415191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7050
    ⟨415191, by decide⟩ (by decide) (![⟨414829, by decide⟩,⟨414899, by decide⟩,⟨415122, by decide⟩,⟨415190, by decide⟩]) unmarked_context_11_7050_415191 node_context_11_7050_415191
  intro a
  fin_cases a
  · exact context_12_28200_414829
  · exact context_12_28201_414899
  · exact context_12_28202_415122
  · exact context_12_28203_415190

theorem selected_cut_16294 : selected 8 ⟨415204, by decide⟩
    (prefixPartial 13 112816) = some ⟨13, 2, 0, 415204, 112816, 597, 16384⟩ := by
  decide +kernel

theorem context_13_112816_415204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112816 ⟨415204, by decide⟩ :=
  accepted_of_selected 13 112816 ⟨415204, by decide⟩ ⟨13, 2, 0, 415204, 112816, 597, 16384⟩
    (by decide) selected_cut_16294

theorem selected_cut_16295 : selected 8 ⟨415245, by decide⟩
    (prefixPartial 13 112817) = some ⟨13, 2, 0, 415245, 112817, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_112817_415245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112817 ⟨415245, by decide⟩ :=
  accepted_of_selected 13 112817 ⟨415245, by decide⟩ ⟨13, 2, 0, 415245, 112817, 2089, 16384⟩
    (by decide) selected_cut_16295

theorem selected_cut_16296 : selected 8 ⟨415259, by decide⟩
    (prefixPartial 13 112818) = some ⟨13, 2, 0, 415259, 112818, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_112818_415259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112818 ⟨415259, by decide⟩ :=
  accepted_of_selected 13 112818 ⟨415259, by decide⟩ ⟨13, 2, 0, 415259, 112818, 1249, 16384⟩
    (by decide) selected_cut_16296

theorem selected_cut_16297 : selected 8 ⟨415266, by decide⟩
    (prefixPartial 13 112819) = some ⟨13, 2, 0, 415266, 112819, 725, 16384⟩ := by
  decide +kernel

theorem context_13_112819_415266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112819 ⟨415266, by decide⟩ :=
  accepted_of_selected 13 112819 ⟨415266, by decide⟩ ⟨13, 2, 0, 415266, 112819, 725, 16384⟩
    (by decide) selected_cut_16297

theorem unmarked_context_12_28204_415267 : frontier 9 ⟨415267, by decide⟩
    (prefixCache 12 28204) (prefixPartial 12 28204) = false := by
  decide +kernel

theorem node_context_12_28204_415267 : EJMOriginalGlobalDAGData.nodes 9 ⟨415267, by decide⟩ =
    .split (coordinate 12) (![⟨415204, by decide⟩,⟨415245, by decide⟩,⟨415259, by decide⟩,⟨415266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28204_415267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28204 ⟨415267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28204
    ⟨415267, by decide⟩ (by decide) (![⟨415204, by decide⟩,⟨415245, by decide⟩,⟨415259, by decide⟩,⟨415266, by decide⟩]) unmarked_context_12_28204_415267 node_context_12_28204_415267
  intro a
  fin_cases a
  · exact context_13_112816_415204
  · exact context_13_112817_415245
  · exact context_13_112818_415259
  · exact context_13_112819_415266

theorem selected_cut_16298 : selected 8 ⟨415281, by decide⟩
    (prefixPartial 13 112820) = some ⟨13, 2, 0, 415281, 112820, 705, 16384⟩ := by
  decide +kernel

theorem context_13_112820_415281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112820 ⟨415281, by decide⟩ :=
  accepted_of_selected 13 112820 ⟨415281, by decide⟩ ⟨13, 2, 0, 415281, 112820, 705, 16384⟩
    (by decide) selected_cut_16298

theorem selected_cut_16299 : selected 8 ⟨415318, by decide⟩
    (prefixPartial 13 112821) = some ⟨13, 2, 0, 415318, 112821, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_112821_415318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112821 ⟨415318, by decide⟩ :=
  accepted_of_selected 13 112821 ⟨415318, by decide⟩ ⟨13, 2, 0, 415318, 112821, 2429, 16384⟩
    (by decide) selected_cut_16299

theorem selected_cut_16300 : selected 8 ⟨415335, by decide⟩
    (prefixPartial 13 112822) = some ⟨13, 2, 0, 415335, 112822, 1513, 16384⟩ := by
  decide +kernel

theorem context_13_112822_415335 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112822 ⟨415335, by decide⟩ :=
  accepted_of_selected 13 112822 ⟨415335, by decide⟩ ⟨13, 2, 0, 415335, 112822, 1513, 16384⟩
    (by decide) selected_cut_16300

theorem selected_cut_16301 : selected 8 ⟨415343, by decide⟩
    (prefixPartial 13 112823) = some ⟨13, 2, 0, 415343, 112823, 881, 16384⟩ := by
  decide +kernel

theorem context_13_112823_415343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112823 ⟨415343, by decide⟩ :=
  accepted_of_selected 13 112823 ⟨415343, by decide⟩ ⟨13, 2, 0, 415343, 112823, 881, 16384⟩
    (by decide) selected_cut_16301

theorem unmarked_context_12_28205_415344 : frontier 9 ⟨415344, by decide⟩
    (prefixCache 12 28205) (prefixPartial 12 28205) = false := by
  decide +kernel

theorem node_context_12_28205_415344 : EJMOriginalGlobalDAGData.nodes 9 ⟨415344, by decide⟩ =
    .split (coordinate 12) (![⟨415281, by decide⟩,⟨415318, by decide⟩,⟨415335, by decide⟩,⟨415343, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28205_415344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28205 ⟨415344, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28205
    ⟨415344, by decide⟩ (by decide) (![⟨415281, by decide⟩,⟨415318, by decide⟩,⟨415335, by decide⟩,⟨415343, by decide⟩]) unmarked_context_12_28205_415344 node_context_12_28205_415344
  intro a
  fin_cases a
  · exact context_13_112820_415281
  · exact context_13_112821_415318
  · exact context_13_112822_415335
  · exact context_13_112823_415343

theorem selected_cut_16302 : selected 8 ⟨415353, by decide⟩
    (prefixPartial 13 112824) = some ⟨13, 2, 0, 415353, 112824, 553, 16384⟩ := by
  decide +kernel

theorem context_13_112824_415353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112824 ⟨415353, by decide⟩ :=
  accepted_of_selected 13 112824 ⟨415353, by decide⟩ ⟨13, 2, 0, 415353, 112824, 553, 16384⟩
    (by decide) selected_cut_16302

theorem selected_cut_16303 : selected 8 ⟨415376, by decide⟩
    (prefixPartial 13 112825) = some ⟨13, 2, 0, 415376, 112825, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_112825_415376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112825 ⟨415376, by decide⟩ :=
  accepted_of_selected 13 112825 ⟨415376, by decide⟩ ⟨13, 2, 0, 415376, 112825, 1957, 16384⟩
    (by decide) selected_cut_16303

theorem selected_cut_16304 : selected 8 ⟨415390, by decide⟩
    (prefixPartial 13 112826) = some ⟨13, 2, 0, 415390, 112826, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_112826_415390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112826 ⟨415390, by decide⟩ :=
  accepted_of_selected 13 112826 ⟨415390, by decide⟩ ⟨13, 2, 0, 415390, 112826, 1069, 16384⟩
    (by decide) selected_cut_16304

theorem selected_cut_16305 : selected 8 ⟨415398, by decide⟩
    (prefixPartial 13 112827) = some ⟨13, 2, 0, 415398, 112827, 793, 16384⟩ := by
  decide +kernel

theorem context_13_112827_415398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112827 ⟨415398, by decide⟩ :=
  accepted_of_selected 13 112827 ⟨415398, by decide⟩ ⟨13, 2, 0, 415398, 112827, 793, 16384⟩
    (by decide) selected_cut_16305

theorem unmarked_context_12_28206_415399 : frontier 9 ⟨415399, by decide⟩
    (prefixCache 12 28206) (prefixPartial 12 28206) = false := by
  decide +kernel

theorem node_context_12_28206_415399 : EJMOriginalGlobalDAGData.nodes 9 ⟨415399, by decide⟩ =
    .split (coordinate 12) (![⟨415353, by decide⟩,⟨415376, by decide⟩,⟨415390, by decide⟩,⟨415398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28206_415399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28206 ⟨415399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28206
    ⟨415399, by decide⟩ (by decide) (![⟨415353, by decide⟩,⟨415376, by decide⟩,⟨415390, by decide⟩,⟨415398, by decide⟩]) unmarked_context_12_28206_415399 node_context_12_28206_415399
  intro a
  fin_cases a
  · exact context_13_112824_415353
  · exact context_13_112825_415376
  · exact context_13_112826_415390
  · exact context_13_112827_415398

theorem selected_cut_16306 : selected 8 ⟨415409, by decide⟩
    (prefixPartial 13 112828) = some ⟨13, 2, 0, 415409, 112828, 693, 16384⟩ := by
  decide +kernel

theorem context_13_112828_415409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112828 ⟨415409, by decide⟩ :=
  accepted_of_selected 13 112828 ⟨415409, by decide⟩ ⟨13, 2, 0, 415409, 112828, 693, 16384⟩
    (by decide) selected_cut_16306

theorem selected_cut_16307 : selected 8 ⟨415448, by decide⟩
    (prefixPartial 13 112829) = some ⟨13, 2, 0, 415448, 112829, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_112829_415448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112829 ⟨415448, by decide⟩ :=
  accepted_of_selected 13 112829 ⟨415448, by decide⟩ ⟨13, 2, 0, 415448, 112829, 2493, 16384⟩
    (by decide) selected_cut_16307

theorem selected_cut_16308 : selected 8 ⟨415469, by decide⟩
    (prefixPartial 13 112830) = some ⟨13, 2, 0, 415469, 112830, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_112830_415469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112830 ⟨415469, by decide⟩ :=
  accepted_of_selected 13 112830 ⟨415469, by decide⟩ ⟨13, 2, 0, 415469, 112830, 1585, 16384⟩
    (by decide) selected_cut_16308

theorem selected_cut_16309 : selected 8 ⟨415477, by decide⟩
    (prefixPartial 13 112831) = some ⟨13, 2, 0, 415477, 112831, 945, 16384⟩ := by
  decide +kernel

theorem context_13_112831_415477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112831 ⟨415477, by decide⟩ :=
  accepted_of_selected 13 112831 ⟨415477, by decide⟩ ⟨13, 2, 0, 415477, 112831, 945, 16384⟩
    (by decide) selected_cut_16309

theorem unmarked_context_12_28207_415478 : frontier 9 ⟨415478, by decide⟩
    (prefixCache 12 28207) (prefixPartial 12 28207) = false := by
  decide +kernel

theorem node_context_12_28207_415478 : EJMOriginalGlobalDAGData.nodes 9 ⟨415478, by decide⟩ =
    .split (coordinate 12) (![⟨415409, by decide⟩,⟨415448, by decide⟩,⟨415469, by decide⟩,⟨415477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28207_415478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28207 ⟨415478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28207
    ⟨415478, by decide⟩ (by decide) (![⟨415409, by decide⟩,⟨415448, by decide⟩,⟨415469, by decide⟩,⟨415477, by decide⟩]) unmarked_context_12_28207_415478 node_context_12_28207_415478
  intro a
  fin_cases a
  · exact context_13_112828_415409
  · exact context_13_112829_415448
  · exact context_13_112830_415469
  · exact context_13_112831_415477

theorem unmarked_context_11_7051_415479 : frontier 10 ⟨415479, by decide⟩
    (prefixCache 11 7051) (prefixPartial 11 7051) = false := by
  decide +kernel

theorem node_context_11_7051_415479 : EJMOriginalGlobalDAGData.nodes 10 ⟨415479, by decide⟩ =
    .split (coordinate 11) (![⟨415267, by decide⟩,⟨415344, by decide⟩,⟨415399, by decide⟩,⟨415478, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_7051_415479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 7051 ⟨415479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 7051
    ⟨415479, by decide⟩ (by decide) (![⟨415267, by decide⟩,⟨415344, by decide⟩,⟨415399, by decide⟩,⟨415478, by decide⟩]) unmarked_context_11_7051_415479 node_context_11_7051_415479
  intro a
  fin_cases a
  · exact context_12_28204_415267
  · exact context_12_28205_415344
  · exact context_12_28206_415399
  · exact context_12_28207_415478

theorem unmarked_context_10_1762_415480 : frontier 11 ⟨415480, by decide⟩
    (prefixCache 10 1762) (prefixPartial 10 1762) = false := by
  decide +kernel

theorem node_context_10_1762_415480 : EJMOriginalGlobalDAGData.nodes 11 ⟨415480, by decide⟩ =
    .split (coordinate 10) (![⟨414509, by decide⟩,⟨414767, by decide⟩,⟨415191, by decide⟩,⟨415479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1762_415480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1762 ⟨415480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1762
    ⟨415480, by decide⟩ (by decide) (![⟨414509, by decide⟩,⟨414767, by decide⟩,⟨415191, by decide⟩,⟨415479, by decide⟩]) unmarked_context_10_1762_415480 node_context_10_1762_415480
  intro a
  fin_cases a
  · exact context_11_7048_414509
  · exact context_11_7049_414767
  · exact context_11_7050_415191
  · exact context_11_7051_415479

theorem selected_cut_16310 : selected 8 ⟨415486, by decide⟩
    (prefixPartial 13 112832) = some ⟨13, 2, 0, 415486, 112832, 753, 16384⟩ := by
  decide +kernel

theorem context_13_112832_415486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112832 ⟨415486, by decide⟩ :=
  accepted_of_selected 13 112832 ⟨415486, by decide⟩ ⟨13, 2, 0, 415486, 112832, 753, 16384⟩
    (by decide) selected_cut_16310

theorem selected_cut_16311 : selected 8 ⟨415509, by decide⟩
    (prefixPartial 13 112833) = some ⟨13, 2, 0, 415509, 112833, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_112833_415509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112833 ⟨415509, by decide⟩ :=
  accepted_of_selected 13 112833 ⟨415509, by decide⟩ ⟨13, 2, 0, 415509, 112833, 2209, 16384⟩
    (by decide) selected_cut_16311

theorem selected_cut_16312 : selected 8 ⟨415524, by decide⟩
    (prefixPartial 13 112834) = some ⟨13, 2, 0, 415524, 112834, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_112834_415524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112834 ⟨415524, by decide⟩ :=
  accepted_of_selected 13 112834 ⟨415524, by decide⟩ ⟨13, 2, 0, 415524, 112834, 1213, 16384⟩
    (by decide) selected_cut_16312

theorem selected_cut_16313 : selected 8 ⟨415532, by decide⟩
    (prefixPartial 13 112835) = some ⟨13, 2, 0, 415532, 112835, 657, 16384⟩ := by
  decide +kernel

theorem context_13_112835_415532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112835 ⟨415532, by decide⟩ :=
  accepted_of_selected 13 112835 ⟨415532, by decide⟩ ⟨13, 2, 0, 415532, 112835, 657, 16384⟩
    (by decide) selected_cut_16313

theorem unmarked_context_12_28208_415533 : frontier 9 ⟨415533, by decide⟩
    (prefixCache 12 28208) (prefixPartial 12 28208) = false := by
  decide +kernel

theorem node_context_12_28208_415533 : EJMOriginalGlobalDAGData.nodes 9 ⟨415533, by decide⟩ =
    .split (coordinate 12) (![⟨415486, by decide⟩,⟨415509, by decide⟩,⟨415524, by decide⟩,⟨415532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28208_415533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28208 ⟨415533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28208
    ⟨415533, by decide⟩ (by decide) (![⟨415486, by decide⟩,⟨415509, by decide⟩,⟨415524, by decide⟩,⟨415532, by decide⟩]) unmarked_context_12_28208_415533 node_context_12_28208_415533
  intro a
  fin_cases a
  · exact context_13_112832_415486
  · exact context_13_112833_415509
  · exact context_13_112834_415524
  · exact context_13_112835_415532

theorem selected_cut_16314 : selected 8 ⟨415540, by decide⟩
    (prefixPartial 13 112836) = some ⟨13, 2, 0, 415540, 112836, 805, 16384⟩ := by
  decide +kernel

theorem context_13_112836_415540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112836 ⟨415540, by decide⟩ :=
  accepted_of_selected 13 112836 ⟨415540, by decide⟩ ⟨13, 2, 0, 415540, 112836, 805, 16384⟩
    (by decide) selected_cut_16314

theorem selected_cut_16315 : selected 8 ⟨415573, by decide⟩
    (prefixPartial 13 112837) = some ⟨13, 2, 0, 415573, 112837, 2541, 16384⟩ := by
  decide +kernel

theorem context_13_112837_415573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112837 ⟨415573, by decide⟩ :=
  accepted_of_selected 13 112837 ⟨415573, by decide⟩ ⟨13, 2, 0, 415573, 112837, 2541, 16384⟩
    (by decide) selected_cut_16315

theorem selected_cut_16316 : selected 8 ⟨415591, by decide⟩
    (prefixPartial 13 112838) = some ⟨13, 2, 0, 415591, 112838, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_112838_415591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112838 ⟨415591, by decide⟩ :=
  accepted_of_selected 13 112838 ⟨415591, by decide⟩ ⟨13, 2, 0, 415591, 112838, 1529, 16384⟩
    (by decide) selected_cut_16316

theorem selected_cut_16317 : selected 8 ⟨415598, by decide⟩
    (prefixPartial 13 112839) = some ⟨13, 2, 0, 415598, 112839, 793, 16384⟩ := by
  decide +kernel

theorem context_13_112839_415598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112839 ⟨415598, by decide⟩ :=
  accepted_of_selected 13 112839 ⟨415598, by decide⟩ ⟨13, 2, 0, 415598, 112839, 793, 16384⟩
    (by decide) selected_cut_16317

theorem unmarked_context_12_28209_415599 : frontier 9 ⟨415599, by decide⟩
    (prefixCache 12 28209) (prefixPartial 12 28209) = false := by
  decide +kernel

theorem node_context_12_28209_415599 : EJMOriginalGlobalDAGData.nodes 9 ⟨415599, by decide⟩ =
    .split (coordinate 12) (![⟨415540, by decide⟩,⟨415573, by decide⟩,⟨415591, by decide⟩,⟨415598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28209_415599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28209 ⟨415599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28209
    ⟨415599, by decide⟩ (by decide) (![⟨415540, by decide⟩,⟨415573, by decide⟩,⟨415591, by decide⟩,⟨415598, by decide⟩]) unmarked_context_12_28209_415599 node_context_12_28209_415599
  intro a
  fin_cases a
  · exact context_13_112836_415540
  · exact context_13_112837_415573
  · exact context_13_112838_415591
  · exact context_13_112839_415598

theorem selected_cut_16318 : selected 8 ⟨415607, by decide⟩
    (prefixPartial 13 112840) = some ⟨13, 2, 0, 415607, 112840, 657, 16384⟩ := by
  decide +kernel

theorem context_13_112840_415607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112840 ⟨415607, by decide⟩ :=
  accepted_of_selected 13 112840 ⟨415607, by decide⟩ ⟨13, 2, 0, 415607, 112840, 657, 16384⟩
    (by decide) selected_cut_16318

theorem selected_cut_16319 : selected 8 ⟨415632, by decide⟩
    (prefixPartial 13 112841) = some ⟨13, 2, 0, 415632, 112841, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_112841_415632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112841 ⟨415632, by decide⟩ :=
  accepted_of_selected 13 112841 ⟨415632, by decide⟩ ⟨13, 2, 0, 415632, 112841, 2161, 16384⟩
    (by decide) selected_cut_16319

theorem selected_cut_16320 : selected 8 ⟨415647, by decide⟩
    (prefixPartial 13 112842) = some ⟨13, 2, 0, 415647, 112842, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_112842_415647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112842 ⟨415647, by decide⟩ :=
  accepted_of_selected 13 112842 ⟨415647, by decide⟩ ⟨13, 2, 0, 415647, 112842, 1201, 16384⟩
    (by decide) selected_cut_16320

theorem selected_cut_16321 : selected 8 ⟨415652, by decide⟩
    (prefixPartial 13 112843) = some ⟨13, 2, 0, 415652, 112843, 749, 16384⟩ := by
  decide +kernel

theorem context_13_112843_415652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112843 ⟨415652, by decide⟩ :=
  accepted_of_selected 13 112843 ⟨415652, by decide⟩ ⟨13, 2, 0, 415652, 112843, 749, 16384⟩
    (by decide) selected_cut_16321

theorem unmarked_context_12_28210_415653 : frontier 9 ⟨415653, by decide⟩
    (prefixCache 12 28210) (prefixPartial 12 28210) = false := by
  decide +kernel

theorem node_context_12_28210_415653 : EJMOriginalGlobalDAGData.nodes 9 ⟨415653, by decide⟩ =
    .split (coordinate 12) (![⟨415607, by decide⟩,⟨415632, by decide⟩,⟨415647, by decide⟩,⟨415652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_28210_415653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 28210 ⟨415653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 28210
    ⟨415653, by decide⟩ (by decide) (![⟨415607, by decide⟩,⟨415632, by decide⟩,⟨415647, by decide⟩,⟨415652, by decide⟩]) unmarked_context_12_28210_415653 node_context_12_28210_415653
  intro a
  fin_cases a
  · exact context_13_112840_415607
  · exact context_13_112841_415632
  · exact context_13_112842_415647
  · exact context_13_112843_415652

theorem selected_cut_16322 : selected 8 ⟨415664, by decide⟩
    (prefixPartial 13 112844) = some ⟨13, 2, 0, 415664, 112844, 813, 16384⟩ := by
  decide +kernel

theorem context_13_112844_415664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112844 ⟨415664, by decide⟩ :=
  accepted_of_selected 13 112844 ⟨415664, by decide⟩ ⟨13, 2, 0, 415664, 112844, 813, 16384⟩
    (by decide) selected_cut_16322

theorem selected_cut_16323 : selected 8 ⟨415713, by decide⟩
    (prefixPartial 13 112845) = some ⟨13, 2, 0, 415713, 112845, 2761, 16384⟩ := by
  decide +kernel

theorem context_13_112845_415713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 112845 ⟨415713, by decide⟩ :=
  accepted_of_selected 13 112845 ⟨415713, by decide⟩ ⟨13, 2, 0, 415713, 112845, 2761, 16384⟩
    (by decide) selected_cut_16323

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
