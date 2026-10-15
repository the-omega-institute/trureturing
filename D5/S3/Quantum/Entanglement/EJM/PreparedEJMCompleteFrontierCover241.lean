/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover240
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_23139 : selected 9 ⟨585990, by decide⟩
    (prefixPartial 12 76170) = some ⟨12, 2, 0, 585990, 76170, 2169, 65536⟩ := by
  decide +kernel

theorem context_12_76170_585990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76170 ⟨585990, by decide⟩ :=
  accepted_of_selected 12 76170 ⟨585990, by decide⟩ ⟨12, 2, 0, 585990, 76170, 2169, 65536⟩
    (by decide) selected_cut_23139

theorem selected_cut_23140 : selected 9 ⟨586012, by decide⟩
    (prefixPartial 12 76171) = some ⟨12, 2, 0, 586012, 76171, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_76171_586012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76171 ⟨586012, by decide⟩ :=
  accepted_of_selected 12 76171 ⟨586012, by decide⟩ ⟨12, 2, 0, 586012, 76171, 2045, 65536⟩
    (by decide) selected_cut_23140

theorem unmarked_context_11_19042_586013 : frontier 10 ⟨586013, by decide⟩
    (prefixCache 11 19042) (prefixPartial 11 19042) = false := by
  decide +kernel

theorem node_context_11_19042_586013 : EJMOriginalGlobalDAGData.nodes 10 ⟨586013, by decide⟩ =
    .split (coordinate 11) (![⟨585942, by decide⟩,⟨585966, by decide⟩,⟨585990, by decide⟩,⟨586012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19042_586013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19042 ⟨586013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19042
    ⟨586013, by decide⟩ (by decide) (![⟨585942, by decide⟩,⟨585966, by decide⟩,⟨585990, by decide⟩,⟨586012, by decide⟩]) unmarked_context_11_19042_586013 node_context_11_19042_586013
  intro a
  fin_cases a
  · exact context_12_76168_585942
  · exact context_12_76169_585966
  · exact context_12_76170_585990
  · exact context_12_76171_586012

theorem selected_cut_23141 : selected 9 ⟨586036, by decide⟩
    (prefixPartial 12 76172) = some ⟨12, 2, 0, 586036, 76172, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_76172_586036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76172 ⟨586036, by decide⟩ :=
  accepted_of_selected 12 76172 ⟨586036, by decide⟩ ⟨12, 2, 0, 586036, 76172, 2093, 65536⟩
    (by decide) selected_cut_23141

theorem selected_cut_23142 : selected 9 ⟨586062, by decide⟩
    (prefixPartial 12 76173) = some ⟨12, 2, 0, 586062, 76173, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_76173_586062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76173 ⟨586062, by decide⟩ :=
  accepted_of_selected 12 76173 ⟨586062, by decide⟩ ⟨12, 2, 0, 586062, 76173, 2073, 65536⟩
    (by decide) selected_cut_23142

theorem selected_cut_23143 : selected 9 ⟨586088, by decide⟩
    (prefixPartial 12 76174) = some ⟨12, 2, 0, 586088, 76174, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_76174_586088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76174 ⟨586088, by decide⟩ :=
  accepted_of_selected 12 76174 ⟨586088, by decide⟩ ⟨12, 2, 0, 586088, 76174, 2509, 65536⟩
    (by decide) selected_cut_23143

theorem selected_cut_23144 : selected 9 ⟨586111, by decide⟩
    (prefixPartial 12 76175) = some ⟨12, 2, 0, 586111, 76175, 2209, 65536⟩ := by
  decide +kernel

theorem context_12_76175_586111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76175 ⟨586111, by decide⟩ :=
  accepted_of_selected 12 76175 ⟨586111, by decide⟩ ⟨12, 2, 0, 586111, 76175, 2209, 65536⟩
    (by decide) selected_cut_23144

theorem unmarked_context_11_19043_586112 : frontier 10 ⟨586112, by decide⟩
    (prefixCache 11 19043) (prefixPartial 11 19043) = false := by
  decide +kernel

theorem node_context_11_19043_586112 : EJMOriginalGlobalDAGData.nodes 10 ⟨586112, by decide⟩ =
    .split (coordinate 11) (![⟨586036, by decide⟩,⟨586062, by decide⟩,⟨586088, by decide⟩,⟨586111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19043_586112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19043 ⟨586112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19043
    ⟨586112, by decide⟩ (by decide) (![⟨586036, by decide⟩,⟨586062, by decide⟩,⟨586088, by decide⟩,⟨586111, by decide⟩]) unmarked_context_11_19043_586112 node_context_11_19043_586112
  intro a
  fin_cases a
  · exact context_12_76172_586036
  · exact context_12_76173_586062
  · exact context_12_76174_586088
  · exact context_12_76175_586111

theorem unmarked_context_10_4760_586113 : frontier 11 ⟨586113, by decide⟩
    (prefixCache 10 4760) (prefixPartial 10 4760) = false := by
  decide +kernel

theorem node_context_10_4760_586113 : EJMOriginalGlobalDAGData.nodes 11 ⟨586113, by decide⟩ =
    .split (coordinate 10) (![⟨585825, by decide⟩,⟨585917, by decide⟩,⟨586013, by decide⟩,⟨586112, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4760_586113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4760 ⟨586113, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4760
    ⟨586113, by decide⟩ (by decide) (![⟨585825, by decide⟩,⟨585917, by decide⟩,⟨586013, by decide⟩,⟨586112, by decide⟩]) unmarked_context_10_4760_586113 node_context_10_4760_586113
  intro a
  fin_cases a
  · exact context_11_19040_585825
  · exact context_11_19041_585917
  · exact context_11_19042_586013
  · exact context_11_19043_586112

theorem selected_cut_23145 : selected 9 ⟨586134, by decide⟩
    (prefixPartial 12 76176) = some ⟨12, 2, 0, 586134, 76176, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_76176_586134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76176 ⟨586134, by decide⟩ :=
  accepted_of_selected 12 76176 ⟨586134, by decide⟩ ⟨12, 2, 0, 586134, 76176, 1977, 65536⟩
    (by decide) selected_cut_23145

theorem selected_cut_23146 : selected 9 ⟨586153, by decide⟩
    (prefixPartial 12 76177) = some ⟨12, 2, 0, 586153, 76177, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_76177_586153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76177 ⟨586153, by decide⟩ :=
  accepted_of_selected 12 76177 ⟨586153, by decide⟩ ⟨12, 2, 0, 586153, 76177, 2233, 65536⟩
    (by decide) selected_cut_23146

theorem selected_cut_23147 : selected 9 ⟨586181, by decide⟩
    (prefixPartial 12 76178) = some ⟨12, 2, 0, 586181, 76178, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_76178_586181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76178 ⟨586181, by decide⟩ :=
  accepted_of_selected 12 76178 ⟨586181, by decide⟩ ⟨12, 2, 0, 586181, 76178, 2513, 65536⟩
    (by decide) selected_cut_23147

theorem selected_cut_23148 : selected 9 ⟨586197, by decide⟩
    (prefixPartial 12 76179) = some ⟨12, 2, 0, 586197, 76179, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_76179_586197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76179 ⟨586197, by decide⟩ :=
  accepted_of_selected 12 76179 ⟨586197, by decide⟩ ⟨12, 2, 0, 586197, 76179, 2265, 65536⟩
    (by decide) selected_cut_23148

theorem unmarked_context_11_19044_586198 : frontier 10 ⟨586198, by decide⟩
    (prefixCache 11 19044) (prefixPartial 11 19044) = false := by
  decide +kernel

theorem node_context_11_19044_586198 : EJMOriginalGlobalDAGData.nodes 10 ⟨586198, by decide⟩ =
    .split (coordinate 11) (![⟨586134, by decide⟩,⟨586153, by decide⟩,⟨586181, by decide⟩,⟨586197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19044_586198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19044 ⟨586198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19044
    ⟨586198, by decide⟩ (by decide) (![⟨586134, by decide⟩,⟨586153, by decide⟩,⟨586181, by decide⟩,⟨586197, by decide⟩]) unmarked_context_11_19044_586198 node_context_11_19044_586198
  intro a
  fin_cases a
  · exact context_12_76176_586134
  · exact context_12_76177_586153
  · exact context_12_76178_586181
  · exact context_12_76179_586197

theorem selected_cut_23149 : selected 9 ⟨586216, by decide⟩
    (prefixPartial 12 76180) = some ⟨12, 2, 0, 586216, 76180, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_76180_586216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76180 ⟨586216, by decide⟩ :=
  accepted_of_selected 12 76180 ⟨586216, by decide⟩ ⟨12, 2, 0, 586216, 76180, 1777, 65536⟩
    (by decide) selected_cut_23149

theorem selected_cut_23150 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 76181) = some ⟨12, 1, 0, 439069, 76181, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76181_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76181 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 76181 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 76181, 1, 65536⟩
    (by decide) selected_cut_23150

theorem selected_cut_23151 : selected 9 ⟨586235, by decide⟩
    (prefixPartial 12 76182) = some ⟨12, 2, 0, 586235, 76182, 2293, 65536⟩ := by
  decide +kernel

theorem context_12_76182_586235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76182 ⟨586235, by decide⟩ :=
  accepted_of_selected 12 76182 ⟨586235, by decide⟩ ⟨12, 2, 0, 586235, 76182, 2293, 65536⟩
    (by decide) selected_cut_23151

theorem selected_cut_23152 : selected 9 ⟨586252, by decide⟩
    (prefixPartial 12 76183) = some ⟨12, 2, 0, 586252, 76183, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_76183_586252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76183 ⟨586252, by decide⟩ :=
  accepted_of_selected 12 76183 ⟨586252, by decide⟩ ⟨12, 2, 0, 586252, 76183, 2073, 65536⟩
    (by decide) selected_cut_23152

theorem unmarked_context_11_19045_586253 : frontier 10 ⟨586253, by decide⟩
    (prefixCache 11 19045) (prefixPartial 11 19045) = false := by
  decide +kernel

theorem node_context_11_19045_586253 : EJMOriginalGlobalDAGData.nodes 10 ⟨586253, by decide⟩ =
    .split (coordinate 11) (![⟨586216, by decide⟩,⟨439069, by decide⟩,⟨586235, by decide⟩,⟨586252, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19045_586253 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19045 ⟨586253, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19045
    ⟨586253, by decide⟩ (by decide) (![⟨586216, by decide⟩,⟨439069, by decide⟩,⟨586235, by decide⟩,⟨586252, by decide⟩]) unmarked_context_11_19045_586253 node_context_11_19045_586253
  intro a
  fin_cases a
  · exact context_12_76180_586216
  · exact context_12_76181_439069
  · exact context_12_76182_586235
  · exact context_12_76183_586252

theorem selected_cut_23153 : selected 9 ⟨586270, by decide⟩
    (prefixPartial 12 76184) = some ⟨12, 2, 0, 586270, 76184, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_76184_586270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76184 ⟨586270, by decide⟩ :=
  accepted_of_selected 12 76184 ⟨586270, by decide⟩ ⟨12, 2, 0, 586270, 76184, 1841, 65536⟩
    (by decide) selected_cut_23153

theorem selected_cut_23154 : selected 9 ⟨586290, by decide⟩
    (prefixPartial 12 76185) = some ⟨12, 2, 0, 586290, 76185, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_76185_586290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76185 ⟨586290, by decide⟩ :=
  accepted_of_selected 12 76185 ⟨586290, by decide⟩ ⟨12, 2, 0, 586290, 76185, 2057, 65536⟩
    (by decide) selected_cut_23154

theorem selected_cut_23155 : selected 9 ⟨586312, by decide⟩
    (prefixPartial 12 76186) = some ⟨12, 2, 0, 586312, 76186, 2189, 65536⟩ := by
  decide +kernel

theorem context_12_76186_586312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76186 ⟨586312, by decide⟩ :=
  accepted_of_selected 12 76186 ⟨586312, by decide⟩ ⟨12, 2, 0, 586312, 76186, 2189, 65536⟩
    (by decide) selected_cut_23155

theorem selected_cut_23156 : selected 9 ⟨586326, by decide⟩
    (prefixPartial 12 76187) = some ⟨12, 2, 0, 586326, 76187, 1881, 65536⟩ := by
  decide +kernel

theorem context_12_76187_586326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76187 ⟨586326, by decide⟩ :=
  accepted_of_selected 12 76187 ⟨586326, by decide⟩ ⟨12, 2, 0, 586326, 76187, 1881, 65536⟩
    (by decide) selected_cut_23156

theorem unmarked_context_11_19046_586327 : frontier 10 ⟨586327, by decide⟩
    (prefixCache 11 19046) (prefixPartial 11 19046) = false := by
  decide +kernel

theorem node_context_11_19046_586327 : EJMOriginalGlobalDAGData.nodes 10 ⟨586327, by decide⟩ =
    .split (coordinate 11) (![⟨586270, by decide⟩,⟨586290, by decide⟩,⟨586312, by decide⟩,⟨586326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19046_586327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19046 ⟨586327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19046
    ⟨586327, by decide⟩ (by decide) (![⟨586270, by decide⟩,⟨586290, by decide⟩,⟨586312, by decide⟩,⟨586326, by decide⟩]) unmarked_context_11_19046_586327 node_context_11_19046_586327
  intro a
  fin_cases a
  · exact context_12_76184_586270
  · exact context_12_76185_586290
  · exact context_12_76186_586312
  · exact context_12_76187_586326

theorem selected_cut_23157 : selected 9 ⟨586344, by decide⟩
    (prefixPartial 12 76188) = some ⟨12, 2, 0, 586344, 76188, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_76188_586344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76188 ⟨586344, by decide⟩ :=
  accepted_of_selected 12 76188 ⟨586344, by decide⟩ ⟨12, 2, 0, 586344, 76188, 1965, 65536⟩
    (by decide) selected_cut_23157

theorem selected_cut_23158 : selected 9 ⟨586359, by decide⟩
    (prefixPartial 12 76189) = some ⟨12, 2, 0, 586359, 76189, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_76189_586359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76189 ⟨586359, by decide⟩ :=
  accepted_of_selected 12 76189 ⟨586359, by decide⟩ ⟨12, 2, 0, 586359, 76189, 2001, 65536⟩
    (by decide) selected_cut_23158

theorem selected_cut_23159 : selected 9 ⟨586382, by decide⟩
    (prefixPartial 12 76190) = some ⟨12, 2, 0, 586382, 76190, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_76190_586382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76190 ⟨586382, by decide⟩ :=
  accepted_of_selected 12 76190 ⟨586382, by decide⟩ ⟨12, 2, 0, 586382, 76190, 2301, 65536⟩
    (by decide) selected_cut_23159

theorem selected_cut_23160 : selected 9 ⟨586397, by decide⟩
    (prefixPartial 12 76191) = some ⟨12, 2, 0, 586397, 76191, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_76191_586397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76191 ⟨586397, by decide⟩ :=
  accepted_of_selected 12 76191 ⟨586397, by decide⟩ ⟨12, 2, 0, 586397, 76191, 1929, 65536⟩
    (by decide) selected_cut_23160

theorem unmarked_context_11_19047_586398 : frontier 10 ⟨586398, by decide⟩
    (prefixCache 11 19047) (prefixPartial 11 19047) = false := by
  decide +kernel

theorem node_context_11_19047_586398 : EJMOriginalGlobalDAGData.nodes 10 ⟨586398, by decide⟩ =
    .split (coordinate 11) (![⟨586344, by decide⟩,⟨586359, by decide⟩,⟨586382, by decide⟩,⟨586397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19047_586398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19047 ⟨586398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19047
    ⟨586398, by decide⟩ (by decide) (![⟨586344, by decide⟩,⟨586359, by decide⟩,⟨586382, by decide⟩,⟨586397, by decide⟩]) unmarked_context_11_19047_586398 node_context_11_19047_586398
  intro a
  fin_cases a
  · exact context_12_76188_586344
  · exact context_12_76189_586359
  · exact context_12_76190_586382
  · exact context_12_76191_586397

theorem unmarked_context_10_4761_586399 : frontier 11 ⟨586399, by decide⟩
    (prefixCache 10 4761) (prefixPartial 10 4761) = false := by
  decide +kernel

theorem node_context_10_4761_586399 : EJMOriginalGlobalDAGData.nodes 11 ⟨586399, by decide⟩ =
    .split (coordinate 10) (![⟨586198, by decide⟩,⟨586253, by decide⟩,⟨586327, by decide⟩,⟨586398, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4761_586399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4761 ⟨586399, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4761
    ⟨586399, by decide⟩ (by decide) (![⟨586198, by decide⟩,⟨586253, by decide⟩,⟨586327, by decide⟩,⟨586398, by decide⟩]) unmarked_context_10_4761_586399 node_context_10_4761_586399
  intro a
  fin_cases a
  · exact context_11_19044_586198
  · exact context_11_19045_586253
  · exact context_11_19046_586327
  · exact context_11_19047_586398

theorem selected_cut_23161 : selected 9 ⟨586415, by decide⟩
    (prefixPartial 12 76192) = some ⟨12, 2, 0, 586415, 76192, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_76192_586415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76192 ⟨586415, by decide⟩ :=
  accepted_of_selected 12 76192 ⟨586415, by decide⟩ ⟨12, 2, 0, 586415, 76192, 1297, 65536⟩
    (by decide) selected_cut_23161

theorem selected_cut_23162 : selected 9 ⟨586431, by decide⟩
    (prefixPartial 12 76193) = some ⟨12, 2, 0, 586431, 76193, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_76193_586431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76193 ⟨586431, by decide⟩ :=
  accepted_of_selected 12 76193 ⟨586431, by decide⟩ ⟨12, 2, 0, 586431, 76193, 1361, 65536⟩
    (by decide) selected_cut_23162

theorem selected_cut_23163 : selected 9 ⟨586446, by decide⟩
    (prefixPartial 12 76194) = some ⟨12, 2, 0, 586446, 76194, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_76194_586446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76194 ⟨586446, by decide⟩ :=
  accepted_of_selected 12 76194 ⟨586446, by decide⟩ ⟨12, 2, 0, 586446, 76194, 1517, 65536⟩
    (by decide) selected_cut_23163

theorem selected_cut_23164 : selected 9 ⟨586459, by decide⟩
    (prefixPartial 12 76195) = some ⟨12, 2, 0, 586459, 76195, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_76195_586459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76195 ⟨586459, by decide⟩ :=
  accepted_of_selected 12 76195 ⟨586459, by decide⟩ ⟨12, 2, 0, 586459, 76195, 1437, 65536⟩
    (by decide) selected_cut_23164

theorem unmarked_context_11_19048_586460 : frontier 10 ⟨586460, by decide⟩
    (prefixCache 11 19048) (prefixPartial 11 19048) = false := by
  decide +kernel

theorem node_context_11_19048_586460 : EJMOriginalGlobalDAGData.nodes 10 ⟨586460, by decide⟩ =
    .split (coordinate 11) (![⟨586415, by decide⟩,⟨586431, by decide⟩,⟨586446, by decide⟩,⟨586459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19048_586460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19048 ⟨586460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19048
    ⟨586460, by decide⟩ (by decide) (![⟨586415, by decide⟩,⟨586431, by decide⟩,⟨586446, by decide⟩,⟨586459, by decide⟩]) unmarked_context_11_19048_586460 node_context_11_19048_586460
  intro a
  fin_cases a
  · exact context_12_76192_586415
  · exact context_12_76193_586431
  · exact context_12_76194_586446
  · exact context_12_76195_586459

theorem selected_cut_23165 : selected 9 ⟨586474, by decide⟩
    (prefixPartial 12 76196) = some ⟨12, 2, 0, 586474, 76196, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_76196_586474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76196 ⟨586474, by decide⟩ :=
  accepted_of_selected 12 76196 ⟨586474, by decide⟩ ⟨12, 2, 0, 586474, 76196, 1237, 65536⟩
    (by decide) selected_cut_23165

theorem selected_cut_23166 : selected 9 ⟨586489, by decide⟩
    (prefixPartial 12 76197) = some ⟨12, 2, 0, 586489, 76197, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_76197_586489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76197 ⟨586489, by decide⟩ :=
  accepted_of_selected 12 76197 ⟨586489, by decide⟩ ⟨12, 2, 0, 586489, 76197, 1997, 65536⟩
    (by decide) selected_cut_23166

theorem selected_cut_23167 : selected 9 ⟨586503, by decide⟩
    (prefixPartial 12 76198) = some ⟨12, 2, 0, 586503, 76198, 1413, 65536⟩ := by
  decide +kernel

theorem context_12_76198_586503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76198 ⟨586503, by decide⟩ :=
  accepted_of_selected 12 76198 ⟨586503, by decide⟩ ⟨12, 2, 0, 586503, 76198, 1413, 65536⟩
    (by decide) selected_cut_23167

theorem selected_cut_23168 : selected 9 ⟨586513, by decide⟩
    (prefixPartial 12 76199) = some ⟨12, 2, 0, 586513, 76199, 1233, 65536⟩ := by
  decide +kernel

theorem context_12_76199_586513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76199 ⟨586513, by decide⟩ :=
  accepted_of_selected 12 76199 ⟨586513, by decide⟩ ⟨12, 2, 0, 586513, 76199, 1233, 65536⟩
    (by decide) selected_cut_23168

theorem unmarked_context_11_19049_586514 : frontier 10 ⟨586514, by decide⟩
    (prefixCache 11 19049) (prefixPartial 11 19049) = false := by
  decide +kernel

theorem node_context_11_19049_586514 : EJMOriginalGlobalDAGData.nodes 10 ⟨586514, by decide⟩ =
    .split (coordinate 11) (![⟨586474, by decide⟩,⟨586489, by decide⟩,⟨586503, by decide⟩,⟨586513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19049_586514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19049 ⟨586514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19049
    ⟨586514, by decide⟩ (by decide) (![⟨586474, by decide⟩,⟨586489, by decide⟩,⟨586503, by decide⟩,⟨586513, by decide⟩]) unmarked_context_11_19049_586514 node_context_11_19049_586514
  intro a
  fin_cases a
  · exact context_12_76196_586474
  · exact context_12_76197_586489
  · exact context_12_76198_586503
  · exact context_12_76199_586513

theorem selected_cut_23169 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 19050) = some ⟨11, 1, 0, 479708, 19050, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19050_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19050 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 19050 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 19050, 1, 262144⟩
    (by decide) selected_cut_23169

theorem selected_cut_23170 : selected 9 ⟨586527, by decide⟩
    (prefixPartial 12 76204) = some ⟨12, 2, 0, 586527, 76204, 1381, 65536⟩ := by
  decide +kernel

theorem context_12_76204_586527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76204 ⟨586527, by decide⟩ :=
  accepted_of_selected 12 76204 ⟨586527, by decide⟩ ⟨12, 2, 0, 586527, 76204, 1381, 65536⟩
    (by decide) selected_cut_23170

theorem selected_cut_23171 : selected 9 ⟨586542, by decide⟩
    (prefixPartial 12 76205) = some ⟨12, 2, 0, 586542, 76205, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_76205_586542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76205 ⟨586542, by decide⟩ :=
  accepted_of_selected 12 76205 ⟨586542, by decide⟩ ⟨12, 2, 0, 586542, 76205, 1341, 65536⟩
    (by decide) selected_cut_23171

theorem selected_cut_23172 : selected 9 ⟨586557, by decide⟩
    (prefixPartial 12 76206) = some ⟨12, 2, 0, 586557, 76206, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_76206_586557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76206 ⟨586557, by decide⟩ :=
  accepted_of_selected 12 76206 ⟨586557, by decide⟩ ⟨12, 2, 0, 586557, 76206, 1473, 65536⟩
    (by decide) selected_cut_23172

theorem selected_cut_23173 : selected 9 ⟨586568, by decide⟩
    (prefixPartial 12 76207) = some ⟨12, 2, 0, 586568, 76207, 1313, 65536⟩ := by
  decide +kernel

theorem context_12_76207_586568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76207 ⟨586568, by decide⟩ :=
  accepted_of_selected 12 76207 ⟨586568, by decide⟩ ⟨12, 2, 0, 586568, 76207, 1313, 65536⟩
    (by decide) selected_cut_23173

theorem unmarked_context_11_19051_586569 : frontier 10 ⟨586569, by decide⟩
    (prefixCache 11 19051) (prefixPartial 11 19051) = false := by
  decide +kernel

theorem node_context_11_19051_586569 : EJMOriginalGlobalDAGData.nodes 10 ⟨586569, by decide⟩ =
    .split (coordinate 11) (![⟨586527, by decide⟩,⟨586542, by decide⟩,⟨586557, by decide⟩,⟨586568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19051_586569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19051 ⟨586569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19051
    ⟨586569, by decide⟩ (by decide) (![⟨586527, by decide⟩,⟨586542, by decide⟩,⟨586557, by decide⟩,⟨586568, by decide⟩]) unmarked_context_11_19051_586569 node_context_11_19051_586569
  intro a
  fin_cases a
  · exact context_12_76204_586527
  · exact context_12_76205_586542
  · exact context_12_76206_586557
  · exact context_12_76207_586568

theorem unmarked_context_10_4762_586570 : frontier 11 ⟨586570, by decide⟩
    (prefixCache 10 4762) (prefixPartial 10 4762) = false := by
  decide +kernel

theorem node_context_10_4762_586570 : EJMOriginalGlobalDAGData.nodes 11 ⟨586570, by decide⟩ =
    .split (coordinate 10) (![⟨586460, by decide⟩,⟨586514, by decide⟩,⟨479708, by decide⟩,⟨586569, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4762_586570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4762 ⟨586570, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4762
    ⟨586570, by decide⟩ (by decide) (![⟨586460, by decide⟩,⟨586514, by decide⟩,⟨479708, by decide⟩,⟨586569, by decide⟩]) unmarked_context_10_4762_586570 node_context_10_4762_586570
  intro a
  fin_cases a
  · exact context_11_19048_586460
  · exact context_11_19049_586514
  · exact context_11_19050_479708
  · exact context_11_19051_586569

theorem selected_cut_23174 : selected 9 ⟨586581, by decide⟩
    (prefixPartial 12 76208) = some ⟨12, 2, 0, 586581, 76208, 1237, 65536⟩ := by
  decide +kernel

theorem context_12_76208_586581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76208 ⟨586581, by decide⟩ :=
  accepted_of_selected 12 76208 ⟨586581, by decide⟩ ⟨12, 2, 0, 586581, 76208, 1237, 65536⟩
    (by decide) selected_cut_23174

theorem selected_cut_23175 : selected 9 ⟨586592, by decide⟩
    (prefixPartial 12 76209) = some ⟨12, 2, 0, 586592, 76209, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_76209_586592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76209 ⟨586592, by decide⟩ :=
  accepted_of_selected 12 76209 ⟨586592, by decide⟩ ⟨12, 2, 0, 586592, 76209, 1301, 65536⟩
    (by decide) selected_cut_23175

theorem selected_cut_23176 : selected 9 ⟨586608, by decide⟩
    (prefixPartial 12 76210) = some ⟨12, 2, 0, 586608, 76210, 1473, 65536⟩ := by
  decide +kernel

theorem context_12_76210_586608 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76210 ⟨586608, by decide⟩ :=
  accepted_of_selected 12 76210 ⟨586608, by decide⟩ ⟨12, 2, 0, 586608, 76210, 1473, 65536⟩
    (by decide) selected_cut_23176

theorem selected_cut_23177 : selected 9 ⟨586620, by decide⟩
    (prefixPartial 12 76211) = some ⟨12, 2, 0, 586620, 76211, 1213, 65536⟩ := by
  decide +kernel

theorem context_12_76211_586620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76211 ⟨586620, by decide⟩ :=
  accepted_of_selected 12 76211 ⟨586620, by decide⟩ ⟨12, 2, 0, 586620, 76211, 1213, 65536⟩
    (by decide) selected_cut_23177

theorem unmarked_context_11_19052_586621 : frontier 10 ⟨586621, by decide⟩
    (prefixCache 11 19052) (prefixPartial 11 19052) = false := by
  decide +kernel

theorem node_context_11_19052_586621 : EJMOriginalGlobalDAGData.nodes 10 ⟨586621, by decide⟩ =
    .split (coordinate 11) (![⟨586581, by decide⟩,⟨586592, by decide⟩,⟨586608, by decide⟩,⟨586620, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19052_586621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19052 ⟨586621, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19052
    ⟨586621, by decide⟩ (by decide) (![⟨586581, by decide⟩,⟨586592, by decide⟩,⟨586608, by decide⟩,⟨586620, by decide⟩]) unmarked_context_11_19052_586621 node_context_11_19052_586621
  intro a
  fin_cases a
  · exact context_12_76208_586581
  · exact context_12_76209_586592
  · exact context_12_76210_586608
  · exact context_12_76211_586620

theorem selected_cut_23178 : selected 9 ⟨586632, by decide⟩
    (prefixPartial 12 76212) = some ⟨12, 2, 0, 586632, 76212, 1141, 65536⟩ := by
  decide +kernel

theorem context_12_76212_586632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76212 ⟨586632, by decide⟩ :=
  accepted_of_selected 12 76212 ⟨586632, by decide⟩ ⟨12, 2, 0, 586632, 76212, 1141, 65536⟩
    (by decide) selected_cut_23178

theorem selected_cut_23179 : selected 9 ⟨586648, by decide⟩
    (prefixPartial 12 76213) = some ⟨12, 2, 0, 586648, 76213, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_76213_586648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76213 ⟨586648, by decide⟩ :=
  accepted_of_selected 12 76213 ⟨586648, by decide⟩ ⟨12, 2, 0, 586648, 76213, 1721, 65536⟩
    (by decide) selected_cut_23179

theorem selected_cut_23180 : selected 9 ⟨586656, by decide⟩
    (prefixPartial 12 76214) = some ⟨12, 2, 0, 586656, 76214, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_76214_586656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76214 ⟨586656, by decide⟩ :=
  accepted_of_selected 12 76214 ⟨586656, by decide⟩ ⟨12, 2, 0, 586656, 76214, 1309, 65536⟩
    (by decide) selected_cut_23180

theorem selected_cut_23181 : selected 9 ⟨586665, by decide⟩
    (prefixPartial 12 76215) = some ⟨12, 2, 0, 586665, 76215, 969, 65536⟩ := by
  decide +kernel

theorem context_12_76215_586665 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76215 ⟨586665, by decide⟩ :=
  accepted_of_selected 12 76215 ⟨586665, by decide⟩ ⟨12, 2, 0, 586665, 76215, 969, 65536⟩
    (by decide) selected_cut_23181

theorem unmarked_context_11_19053_586666 : frontier 10 ⟨586666, by decide⟩
    (prefixCache 11 19053) (prefixPartial 11 19053) = false := by
  decide +kernel

theorem node_context_11_19053_586666 : EJMOriginalGlobalDAGData.nodes 10 ⟨586666, by decide⟩ =
    .split (coordinate 11) (![⟨586632, by decide⟩,⟨586648, by decide⟩,⟨586656, by decide⟩,⟨586665, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19053_586666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19053 ⟨586666, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19053
    ⟨586666, by decide⟩ (by decide) (![⟨586632, by decide⟩,⟨586648, by decide⟩,⟨586656, by decide⟩,⟨586665, by decide⟩]) unmarked_context_11_19053_586666 node_context_11_19053_586666
  intro a
  fin_cases a
  · exact context_12_76212_586632
  · exact context_12_76213_586648
  · exact context_12_76214_586656
  · exact context_12_76215_586665

theorem selected_cut_23182 : selected 9 ⟨586679, by decide⟩
    (prefixPartial 12 76216) = some ⟨12, 2, 0, 586679, 76216, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_76216_586679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76216 ⟨586679, by decide⟩ :=
  accepted_of_selected 12 76216 ⟨586679, by decide⟩ ⟨12, 2, 0, 586679, 76216, 1049, 65536⟩
    (by decide) selected_cut_23182

theorem selected_cut_23183 : selected 9 ⟨586688, by decide⟩
    (prefixPartial 12 76217) = some ⟨12, 2, 0, 586688, 76217, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_76217_586688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76217 ⟨586688, by decide⟩ :=
  accepted_of_selected 12 76217 ⟨586688, by decide⟩ ⟨12, 2, 0, 586688, 76217, 1153, 65536⟩
    (by decide) selected_cut_23183

theorem selected_cut_23184 : selected 9 ⟨586701, by decide⟩
    (prefixPartial 12 76218) = some ⟨12, 2, 0, 586701, 76218, 1097, 65536⟩ := by
  decide +kernel

theorem context_12_76218_586701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76218 ⟨586701, by decide⟩ :=
  accepted_of_selected 12 76218 ⟨586701, by decide⟩ ⟨12, 2, 0, 586701, 76218, 1097, 65536⟩
    (by decide) selected_cut_23184

theorem selected_cut_23185 : selected 9 ⟨586710, by decide⟩
    (prefixPartial 12 76219) = some ⟨12, 2, 0, 586710, 76219, 857, 65536⟩ := by
  decide +kernel

theorem context_12_76219_586710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76219 ⟨586710, by decide⟩ :=
  accepted_of_selected 12 76219 ⟨586710, by decide⟩ ⟨12, 2, 0, 586710, 76219, 857, 65536⟩
    (by decide) selected_cut_23185

theorem unmarked_context_11_19054_586711 : frontier 10 ⟨586711, by decide⟩
    (prefixCache 11 19054) (prefixPartial 11 19054) = false := by
  decide +kernel

theorem node_context_11_19054_586711 : EJMOriginalGlobalDAGData.nodes 10 ⟨586711, by decide⟩ =
    .split (coordinate 11) (![⟨586679, by decide⟩,⟨586688, by decide⟩,⟨586701, by decide⟩,⟨586710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19054_586711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19054 ⟨586711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19054
    ⟨586711, by decide⟩ (by decide) (![⟨586679, by decide⟩,⟨586688, by decide⟩,⟨586701, by decide⟩,⟨586710, by decide⟩]) unmarked_context_11_19054_586711 node_context_11_19054_586711
  intro a
  fin_cases a
  · exact context_12_76216_586679
  · exact context_12_76217_586688
  · exact context_12_76218_586701
  · exact context_12_76219_586710

theorem selected_cut_23186 : selected 9 ⟨586721, by decide⟩
    (prefixPartial 12 76220) = some ⟨12, 2, 0, 586721, 76220, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_76220_586721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76220 ⟨586721, by decide⟩ :=
  accepted_of_selected 12 76220 ⟨586721, by decide⟩ ⟨12, 2, 0, 586721, 76220, 1077, 65536⟩
    (by decide) selected_cut_23186

theorem selected_cut_23187 : selected 9 ⟨586731, by decide⟩
    (prefixPartial 12 76221) = some ⟨12, 2, 0, 586731, 76221, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_76221_586731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76221 ⟨586731, by decide⟩ :=
  accepted_of_selected 12 76221 ⟨586731, by decide⟩ ⟨12, 2, 0, 586731, 76221, 1077, 65536⟩
    (by decide) selected_cut_23187

theorem selected_cut_23188 : selected 9 ⟨586744, by decide⟩
    (prefixPartial 12 76222) = some ⟨12, 2, 0, 586744, 76222, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_76222_586744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76222 ⟨586744, by decide⟩ :=
  accepted_of_selected 12 76222 ⟨586744, by decide⟩ ⟨12, 2, 0, 586744, 76222, 1189, 65536⟩
    (by decide) selected_cut_23188

theorem selected_cut_23189 : selected 9 ⟨586754, by decide⟩
    (prefixPartial 12 76223) = some ⟨12, 2, 0, 586754, 76223, 873, 65536⟩ := by
  decide +kernel

theorem context_12_76223_586754 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76223 ⟨586754, by decide⟩ :=
  accepted_of_selected 12 76223 ⟨586754, by decide⟩ ⟨12, 2, 0, 586754, 76223, 873, 65536⟩
    (by decide) selected_cut_23189

theorem unmarked_context_11_19055_586755 : frontier 10 ⟨586755, by decide⟩
    (prefixCache 11 19055) (prefixPartial 11 19055) = false := by
  decide +kernel

theorem node_context_11_19055_586755 : EJMOriginalGlobalDAGData.nodes 10 ⟨586755, by decide⟩ =
    .split (coordinate 11) (![⟨586721, by decide⟩,⟨586731, by decide⟩,⟨586744, by decide⟩,⟨586754, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19055_586755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19055 ⟨586755, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19055
    ⟨586755, by decide⟩ (by decide) (![⟨586721, by decide⟩,⟨586731, by decide⟩,⟨586744, by decide⟩,⟨586754, by decide⟩]) unmarked_context_11_19055_586755 node_context_11_19055_586755
  intro a
  fin_cases a
  · exact context_12_76220_586721
  · exact context_12_76221_586731
  · exact context_12_76222_586744
  · exact context_12_76223_586754

theorem unmarked_context_10_4763_586756 : frontier 11 ⟨586756, by decide⟩
    (prefixCache 10 4763) (prefixPartial 10 4763) = false := by
  decide +kernel

theorem node_context_10_4763_586756 : EJMOriginalGlobalDAGData.nodes 11 ⟨586756, by decide⟩ =
    .split (coordinate 10) (![⟨586621, by decide⟩,⟨586666, by decide⟩,⟨586711, by decide⟩,⟨586755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4763_586756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4763 ⟨586756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4763
    ⟨586756, by decide⟩ (by decide) (![⟨586621, by decide⟩,⟨586666, by decide⟩,⟨586711, by decide⟩,⟨586755, by decide⟩]) unmarked_context_10_4763_586756 node_context_10_4763_586756
  intro a
  fin_cases a
  · exact context_11_19052_586621
  · exact context_11_19053_586666
  · exact context_11_19054_586711
  · exact context_11_19055_586755

theorem unmarked_context_9_1190_586757 : frontier 12 ⟨586757, by decide⟩
    (prefixCache 9 1190) (prefixPartial 9 1190) = false := by
  decide +kernel

theorem node_context_9_1190_586757 : EJMOriginalGlobalDAGData.nodes 12 ⟨586757, by decide⟩ =
    .split (coordinate 9) (![⟨586113, by decide⟩,⟨586399, by decide⟩,⟨586570, by decide⟩,⟨586756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1190_586757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1190 ⟨586757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1190
    ⟨586757, by decide⟩ (by decide) (![⟨586113, by decide⟩,⟨586399, by decide⟩,⟨586570, by decide⟩,⟨586756, by decide⟩]) unmarked_context_9_1190_586757 node_context_9_1190_586757
  intro a
  fin_cases a
  · exact context_10_4760_586113
  · exact context_10_4761_586399
  · exact context_10_4762_586570
  · exact context_10_4763_586756

theorem selected_cut_23190 : selected 10 ⟨586784, by decide⟩
    (prefixPartial 11 19056) = some ⟨11, 2, 0, 586784, 19056, 3949, 262144⟩ := by
  decide +kernel

theorem context_11_19056_586784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19056 ⟨586784, by decide⟩ :=
  accepted_of_selected 11 19056 ⟨586784, by decide⟩ ⟨11, 2, 0, 586784, 19056, 3949, 262144⟩
    (by decide) selected_cut_23190

theorem selected_cut_23191 : selected 10 ⟨586812, by decide⟩
    (prefixPartial 11 19057) = some ⟨11, 2, 0, 586812, 19057, 3409, 262144⟩ := by
  decide +kernel

theorem context_11_19057_586812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19057 ⟨586812, by decide⟩ :=
  accepted_of_selected 11 19057 ⟨586812, by decide⟩ ⟨11, 2, 0, 586812, 19057, 3409, 262144⟩
    (by decide) selected_cut_23191

theorem selected_cut_23192 : selected 10 ⟨586841, by decide⟩
    (prefixPartial 11 19058) = some ⟨11, 2, 0, 586841, 19058, 3069, 262144⟩ := by
  decide +kernel

theorem context_11_19058_586841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19058 ⟨586841, by decide⟩ :=
  accepted_of_selected 11 19058 ⟨586841, by decide⟩ ⟨11, 2, 0, 586841, 19058, 3069, 262144⟩
    (by decide) selected_cut_23192

theorem selected_cut_23193 : selected 10 ⟨586867, by decide⟩
    (prefixPartial 11 19059) = some ⟨11, 2, 0, 586867, 19059, 3237, 262144⟩ := by
  decide +kernel

theorem context_11_19059_586867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19059 ⟨586867, by decide⟩ :=
  accepted_of_selected 11 19059 ⟨586867, by decide⟩ ⟨11, 2, 0, 586867, 19059, 3237, 262144⟩
    (by decide) selected_cut_23193

theorem unmarked_context_10_4764_586868 : frontier 11 ⟨586868, by decide⟩
    (prefixCache 10 4764) (prefixPartial 10 4764) = false := by
  decide +kernel

theorem node_context_10_4764_586868 : EJMOriginalGlobalDAGData.nodes 11 ⟨586868, by decide⟩ =
    .split (coordinate 10) (![⟨586784, by decide⟩,⟨586812, by decide⟩,⟨586841, by decide⟩,⟨586867, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4764_586868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4764 ⟨586868, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4764
    ⟨586868, by decide⟩ (by decide) (![⟨586784, by decide⟩,⟨586812, by decide⟩,⟨586841, by decide⟩,⟨586867, by decide⟩]) unmarked_context_10_4764_586868 node_context_10_4764_586868
  intro a
  fin_cases a
  · exact context_11_19056_586784
  · exact context_11_19057_586812
  · exact context_11_19058_586841
  · exact context_11_19059_586867

theorem selected_cut_23194 : selected 10 ⟨586890, by decide⟩
    (prefixPartial 11 19060) = some ⟨11, 2, 0, 586890, 19060, 2681, 262144⟩ := by
  decide +kernel

theorem context_11_19060_586890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19060 ⟨586890, by decide⟩ :=
  accepted_of_selected 11 19060 ⟨586890, by decide⟩ ⟨11, 2, 0, 586890, 19060, 2681, 262144⟩
    (by decide) selected_cut_23194

theorem selected_cut_23195 : selected 10 ⟨586906, by decide⟩
    (prefixPartial 11 19061) = some ⟨11, 2, 0, 586906, 19061, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_19061_586906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19061 ⟨586906, by decide⟩ :=
  accepted_of_selected 11 19061 ⟨586906, by decide⟩ ⟨11, 2, 0, 586906, 19061, 1849, 262144⟩
    (by decide) selected_cut_23195

theorem selected_cut_23196 : selected 10 ⟨586929, by decide⟩
    (prefixPartial 11 19062) = some ⟨11, 2, 0, 586929, 19062, 2201, 262144⟩ := by
  decide +kernel

theorem context_11_19062_586929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19062 ⟨586929, by decide⟩ :=
  accepted_of_selected 11 19062 ⟨586929, by decide⟩ ⟨11, 2, 0, 586929, 19062, 2201, 262144⟩
    (by decide) selected_cut_23196

theorem selected_cut_23197 : selected 10 ⟨586954, by decide⟩
    (prefixPartial 11 19063) = some ⟨11, 2, 0, 586954, 19063, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_19063_586954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19063 ⟨586954, by decide⟩ :=
  accepted_of_selected 11 19063 ⟨586954, by decide⟩ ⟨11, 2, 0, 586954, 19063, 2193, 262144⟩
    (by decide) selected_cut_23197

theorem unmarked_context_10_4765_586955 : frontier 11 ⟨586955, by decide⟩
    (prefixCache 10 4765) (prefixPartial 10 4765) = false := by
  decide +kernel

theorem node_context_10_4765_586955 : EJMOriginalGlobalDAGData.nodes 11 ⟨586955, by decide⟩ =
    .split (coordinate 10) (![⟨586890, by decide⟩,⟨586906, by decide⟩,⟨586929, by decide⟩,⟨586954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4765_586955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4765 ⟨586955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4765
    ⟨586955, by decide⟩ (by decide) (![⟨586890, by decide⟩,⟨586906, by decide⟩,⟨586929, by decide⟩,⟨586954, by decide⟩]) unmarked_context_10_4765_586955 node_context_10_4765_586955
  intro a
  fin_cases a
  · exact context_11_19060_586890
  · exact context_11_19061_586906
  · exact context_11_19062_586929
  · exact context_11_19063_586954

theorem selected_cut_23198 : selected 10 ⟨586970, by decide⟩
    (prefixPartial 11 19064) = some ⟨11, 2, 0, 586970, 19064, 1477, 262144⟩ := by
  decide +kernel

theorem context_11_19064_586970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19064 ⟨586970, by decide⟩ :=
  accepted_of_selected 11 19064 ⟨586970, by decide⟩ ⟨11, 2, 0, 586970, 19064, 1477, 262144⟩
    (by decide) selected_cut_23198

theorem selected_cut_23199 : selected 10 ⟨586988, by decide⟩
    (prefixPartial 11 19065) = some ⟨11, 2, 0, 586988, 19065, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_19065_586988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19065 ⟨586988, by decide⟩ :=
  accepted_of_selected 11 19065 ⟨586988, by decide⟩ ⟨11, 2, 0, 586988, 19065, 1461, 262144⟩
    (by decide) selected_cut_23199

theorem selected_cut_23200 : selected 10 ⟨586998, by decide⟩
    (prefixPartial 11 19066) = some ⟨11, 2, 0, 586998, 19066, 981, 262144⟩ := by
  decide +kernel

theorem context_11_19066_586998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19066 ⟨586998, by decide⟩ :=
  accepted_of_selected 11 19066 ⟨586998, by decide⟩ ⟨11, 2, 0, 586998, 19066, 981, 262144⟩
    (by decide) selected_cut_23200

theorem selected_cut_23201 : selected 10 ⟨587012, by decide⟩
    (prefixPartial 11 19067) = some ⟨11, 2, 0, 587012, 19067, 937, 262144⟩ := by
  decide +kernel

theorem context_11_19067_587012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19067 ⟨587012, by decide⟩ :=
  accepted_of_selected 11 19067 ⟨587012, by decide⟩ ⟨11, 2, 0, 587012, 19067, 937, 262144⟩
    (by decide) selected_cut_23201

theorem unmarked_context_10_4766_587013 : frontier 11 ⟨587013, by decide⟩
    (prefixCache 10 4766) (prefixPartial 10 4766) = false := by
  decide +kernel

theorem node_context_10_4766_587013 : EJMOriginalGlobalDAGData.nodes 11 ⟨587013, by decide⟩ =
    .split (coordinate 10) (![⟨586970, by decide⟩,⟨586988, by decide⟩,⟨586998, by decide⟩,⟨587012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4766_587013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4766 ⟨587013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4766
    ⟨587013, by decide⟩ (by decide) (![⟨586970, by decide⟩,⟨586988, by decide⟩,⟨586998, by decide⟩,⟨587012, by decide⟩]) unmarked_context_10_4766_587013 node_context_10_4766_587013
  intro a
  fin_cases a
  · exact context_11_19064_586970
  · exact context_11_19065_586988
  · exact context_11_19066_586998
  · exact context_11_19067_587012

theorem selected_cut_23202 : selected 11 ⟨587042, by decide⟩
    (prefixPartial 10 4767) = some ⟨10, 2, 0, 587042, 4767, 1785, 1048576⟩ := by
  decide +kernel

theorem context_10_4767_587042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4767 ⟨587042, by decide⟩ :=
  accepted_of_selected 10 4767 ⟨587042, by decide⟩ ⟨10, 2, 0, 587042, 4767, 1785, 1048576⟩
    (by decide) selected_cut_23202

theorem unmarked_context_9_1191_587043 : frontier 12 ⟨587043, by decide⟩
    (prefixCache 9 1191) (prefixPartial 9 1191) = false := by
  decide +kernel

theorem node_context_9_1191_587043 : EJMOriginalGlobalDAGData.nodes 12 ⟨587043, by decide⟩ =
    .split (coordinate 9) (![⟨586868, by decide⟩,⟨586955, by decide⟩,⟨587013, by decide⟩,⟨587042, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1191_587043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1191 ⟨587043, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1191
    ⟨587043, by decide⟩ (by decide) (![⟨586868, by decide⟩,⟨586955, by decide⟩,⟨587013, by decide⟩,⟨587042, by decide⟩]) unmarked_context_9_1191_587043 node_context_9_1191_587043
  intro a
  fin_cases a
  · exact context_10_4764_586868
  · exact context_10_4765_586955
  · exact context_10_4766_587013
  · exact context_10_4767_587042

theorem unmarked_context_8_297_587044 : frontier 13 ⟨587044, by decide⟩
    (prefixCache 8 297) (prefixPartial 8 297) = false := by
  decide +kernel

theorem node_context_8_297_587044 : EJMOriginalGlobalDAGData.nodes 13 ⟨587044, by decide⟩ =
    .split (coordinate 8) (![⟨583334, by decide⟩,⟨585718, by decide⟩,⟨586757, by decide⟩,⟨587043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_297_587044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 297 ⟨587044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 297
    ⟨587044, by decide⟩ (by decide) (![⟨583334, by decide⟩,⟨585718, by decide⟩,⟨586757, by decide⟩,⟨587043, by decide⟩]) unmarked_context_8_297_587044 node_context_8_297_587044
  intro a
  fin_cases a
  · exact context_9_1188_583334
  · exact context_9_1189_585718
  · exact context_9_1190_586757
  · exact context_9_1191_587043

theorem selected_cut_23203 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 19072) = some ⟨11, 1, 0, 434745, 19072, 1, 262144⟩ := by
  decide +kernel

theorem context_11_19072_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19072 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 19072 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 19072, 1, 262144⟩
    (by decide) selected_cut_23203

theorem selected_cut_23204 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76292) = some ⟨12, 1, 0, 448748, 76292, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76292_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76292 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76292 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76292, 1, 65536⟩
    (by decide) selected_cut_23204

theorem selected_cut_23205 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 76293) = some ⟨12, 1, 0, 34034, 76293, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76293_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76293 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 76293 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 76293, 1, 65536⟩
    (by decide) selected_cut_23205

theorem selected_cut_23206 : selected 9 ⟨88909, by decide⟩
    (prefixPartial 12 76294) = some ⟨12, 1, 0, 88909, 76294, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76294_88909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76294 ⟨88909, by decide⟩ :=
  accepted_of_selected 12 76294 ⟨88909, by decide⟩ ⟨12, 1, 0, 88909, 76294, 1, 65536⟩
    (by decide) selected_cut_23206

theorem selected_cut_23207 : selected 8 ⟨587164, by decide⟩
    (prefixPartial 13 305180) = some ⟨13, 2, 0, 587164, 305180, 3561, 16384⟩ := by
  decide +kernel

theorem context_13_305180_587164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305180 ⟨587164, by decide⟩ :=
  accepted_of_selected 13 305180 ⟨587164, by decide⟩ ⟨13, 2, 0, 587164, 305180, 3561, 16384⟩
    (by decide) selected_cut_23207

theorem selected_cut_23208 : selected 8 ⟨587216, by decide⟩
    (prefixPartial 13 305181) = some ⟨13, 2, 0, 587216, 305181, 2937, 16384⟩ := by
  decide +kernel

theorem context_13_305181_587216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305181 ⟨587216, by decide⟩ :=
  accepted_of_selected 13 305181 ⟨587216, by decide⟩ ⟨13, 2, 0, 587216, 305181, 2937, 16384⟩
    (by decide) selected_cut_23208

theorem selected_cut_23209 : selected 8 ⟨587243, by decide⟩
    (prefixPartial 13 305182) = some ⟨13, 2, 0, 587243, 305182, 1661, 16384⟩ := by
  decide +kernel

theorem context_13_305182_587243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305182 ⟨587243, by decide⟩ :=
  accepted_of_selected 13 305182 ⟨587243, by decide⟩ ⟨13, 2, 0, 587243, 305182, 1661, 16384⟩
    (by decide) selected_cut_23209

theorem selected_cut_23210 : selected 8 ⟨587289, by decide⟩
    (prefixPartial 13 305183) = some ⟨13, 2, 0, 587289, 305183, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_305183_587289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305183 ⟨587289, by decide⟩ :=
  accepted_of_selected 13 305183 ⟨587289, by decide⟩ ⟨13, 2, 0, 587289, 305183, 1221, 16384⟩
    (by decide) selected_cut_23210

theorem unmarked_context_12_76295_587290 : frontier 9 ⟨587290, by decide⟩
    (prefixCache 12 76295) (prefixPartial 12 76295) = false := by
  decide +kernel

theorem node_context_12_76295_587290 : EJMOriginalGlobalDAGData.nodes 9 ⟨587290, by decide⟩ =
    .split (coordinate 12) (![⟨587164, by decide⟩,⟨587216, by decide⟩,⟨587243, by decide⟩,⟨587289, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76295_587290 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76295 ⟨587290, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76295
    ⟨587290, by decide⟩ (by decide) (![⟨587164, by decide⟩,⟨587216, by decide⟩,⟨587243, by decide⟩,⟨587289, by decide⟩]) unmarked_context_12_76295_587290 node_context_12_76295_587290
  intro a
  fin_cases a
  · exact context_13_305180_587164
  · exact context_13_305181_587216
  · exact context_13_305182_587243
  · exact context_13_305183_587289

theorem unmarked_context_11_19073_587291 : frontier 10 ⟨587291, by decide⟩
    (prefixCache 11 19073) (prefixPartial 11 19073) = false := by
  decide +kernel

theorem node_context_11_19073_587291 : EJMOriginalGlobalDAGData.nodes 10 ⟨587291, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨88909, by decide⟩,⟨587290, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19073_587291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19073 ⟨587291, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19073
    ⟨587291, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨88909, by decide⟩,⟨587290, by decide⟩]) unmarked_context_11_19073_587291 node_context_11_19073_587291
  intro a
  fin_cases a
  · exact context_12_76292_448748
  · exact context_12_76293_34034
  · exact context_12_76294_88909
  · exact context_12_76295_587290

theorem selected_cut_23211 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76296) = some ⟨12, 1, 0, 448748, 76296, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76296_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76296 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76296 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76296, 1, 65536⟩
    (by decide) selected_cut_23211

theorem selected_cut_23212 : selected 8 ⟨587391, by decide⟩
    (prefixPartial 13 305188) = some ⟨13, 2, 0, 587391, 305188, 3357, 16384⟩ := by
  decide +kernel

theorem context_13_305188_587391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305188 ⟨587391, by decide⟩ :=
  accepted_of_selected 13 305188 ⟨587391, by decide⟩ ⟨13, 2, 0, 587391, 305188, 3357, 16384⟩
    (by decide) selected_cut_23212

theorem selected_cut_23213 : selected 8 ⟨587429, by decide⟩
    (prefixPartial 13 305189) = some ⟨13, 2, 0, 587429, 305189, 2397, 16384⟩ := by
  decide +kernel

theorem context_13_305189_587429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305189 ⟨587429, by decide⟩ :=
  accepted_of_selected 13 305189 ⟨587429, by decide⟩ ⟨13, 2, 0, 587429, 305189, 2397, 16384⟩
    (by decide) selected_cut_23213

theorem selected_cut_23214 : selected 8 ⟨587456, by decide⟩
    (prefixPartial 13 305190) = some ⟨13, 2, 0, 587456, 305190, 1517, 16384⟩ := by
  decide +kernel

theorem context_13_305190_587456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305190 ⟨587456, by decide⟩ :=
  accepted_of_selected 13 305190 ⟨587456, by decide⟩ ⟨13, 2, 0, 587456, 305190, 1517, 16384⟩
    (by decide) selected_cut_23214

theorem selected_cut_23215 : selected 8 ⟨587490, by decide⟩
    (prefixPartial 13 305191) = some ⟨13, 2, 0, 587490, 305191, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_305191_587490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305191 ⟨587490, by decide⟩ :=
  accepted_of_selected 13 305191 ⟨587490, by decide⟩ ⟨13, 2, 0, 587490, 305191, 1201, 16384⟩
    (by decide) selected_cut_23215

theorem unmarked_context_12_76297_587491 : frontier 9 ⟨587491, by decide⟩
    (prefixCache 12 76297) (prefixPartial 12 76297) = false := by
  decide +kernel

theorem node_context_12_76297_587491 : EJMOriginalGlobalDAGData.nodes 9 ⟨587491, by decide⟩ =
    .split (coordinate 12) (![⟨587391, by decide⟩,⟨587429, by decide⟩,⟨587456, by decide⟩,⟨587490, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76297_587491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76297 ⟨587491, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76297
    ⟨587491, by decide⟩ (by decide) (![⟨587391, by decide⟩,⟨587429, by decide⟩,⟨587456, by decide⟩,⟨587490, by decide⟩]) unmarked_context_12_76297_587491 node_context_12_76297_587491
  intro a
  fin_cases a
  · exact context_13_305188_587391
  · exact context_13_305189_587429
  · exact context_13_305190_587456
  · exact context_13_305191_587490

theorem selected_cut_23216 : selected 9 ⟨524302, by decide⟩
    (prefixPartial 12 76298) = some ⟨12, 1, 0, 524302, 76298, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76298_524302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76298 ⟨524302, by decide⟩ :=
  accepted_of_selected 12 76298 ⟨524302, by decide⟩ ⟨12, 1, 0, 524302, 76298, 1, 65536⟩
    (by decide) selected_cut_23216

theorem selected_cut_23217 : selected 8 ⟨587541, by decide⟩
    (prefixPartial 13 305196) = some ⟨13, 2, 0, 587541, 305196, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_305196_587541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305196 ⟨587541, by decide⟩ :=
  accepted_of_selected 13 305196 ⟨587541, by decide⟩ ⟨13, 2, 0, 587541, 305196, 1541, 16384⟩
    (by decide) selected_cut_23217

theorem selected_cut_23218 : selected 8 ⟨587597, by decide⟩
    (prefixPartial 13 305197) = some ⟨13, 2, 0, 587597, 305197, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_305197_587597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305197 ⟨587597, by decide⟩ :=
  accepted_of_selected 13 305197 ⟨587597, by decide⟩ ⟨13, 2, 0, 587597, 305197, 2453, 16384⟩
    (by decide) selected_cut_23218

theorem selected_cut_23219 : selected 8 ⟨587614, by decide⟩
    (prefixPartial 13 305198) = some ⟨13, 2, 0, 587614, 305198, 277, 16384⟩ := by
  decide +kernel

theorem context_13_305198_587614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305198 ⟨587614, by decide⟩ :=
  accepted_of_selected 13 305198 ⟨587614, by decide⟩ ⟨13, 2, 0, 587614, 305198, 277, 16384⟩
    (by decide) selected_cut_23219

theorem selected_cut_23220 : selected 8 ⟨51129, by decide⟩
    (prefixPartial 13 305199) = some ⟨13, 1, 0, 51129, 305199, 1, 16384⟩ := by
  decide +kernel

theorem context_13_305199_51129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305199 ⟨51129, by decide⟩ :=
  accepted_of_selected 13 305199 ⟨51129, by decide⟩ ⟨13, 1, 0, 51129, 305199, 1, 16384⟩
    (by decide) selected_cut_23220

theorem unmarked_context_12_76299_587615 : frontier 9 ⟨587615, by decide⟩
    (prefixCache 12 76299) (prefixPartial 12 76299) = false := by
  decide +kernel

theorem node_context_12_76299_587615 : EJMOriginalGlobalDAGData.nodes 9 ⟨587615, by decide⟩ =
    .split (coordinate 12) (![⟨587541, by decide⟩,⟨587597, by decide⟩,⟨587614, by decide⟩,⟨51129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76299_587615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76299 ⟨587615, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76299
    ⟨587615, by decide⟩ (by decide) (![⟨587541, by decide⟩,⟨587597, by decide⟩,⟨587614, by decide⟩,⟨51129, by decide⟩]) unmarked_context_12_76299_587615 node_context_12_76299_587615
  intro a
  fin_cases a
  · exact context_13_305196_587541
  · exact context_13_305197_587597
  · exact context_13_305198_587614
  · exact context_13_305199_51129

theorem unmarked_context_11_19074_587616 : frontier 10 ⟨587616, by decide⟩
    (prefixCache 11 19074) (prefixPartial 11 19074) = false := by
  decide +kernel

theorem node_context_11_19074_587616 : EJMOriginalGlobalDAGData.nodes 10 ⟨587616, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨587491, by decide⟩,⟨524302, by decide⟩,⟨587615, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19074_587616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19074 ⟨587616, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19074
    ⟨587616, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨587491, by decide⟩,⟨524302, by decide⟩,⟨587615, by decide⟩]) unmarked_context_11_19074_587616 node_context_11_19074_587616
  intro a
  fin_cases a
  · exact context_12_76296_448748
  · exact context_12_76297_587491
  · exact context_12_76298_524302
  · exact context_12_76299_587615

theorem selected_cut_23221 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 76300) = some ⟨12, 1, 0, 448748, 76300, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76300_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76300 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 76300 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 76300, 1, 65536⟩
    (by decide) selected_cut_23221

theorem selected_cut_23222 : selected 8 ⟨587710, by decide⟩
    (prefixPartial 13 305204) = some ⟨13, 2, 0, 587710, 305204, 3533, 16384⟩ := by
  decide +kernel

theorem context_13_305204_587710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305204 ⟨587710, by decide⟩ :=
  accepted_of_selected 13 305204 ⟨587710, by decide⟩ ⟨13, 2, 0, 587710, 305204, 3533, 16384⟩
    (by decide) selected_cut_23222

theorem selected_cut_23223 : selected 8 ⟨587763, by decide⟩
    (prefixPartial 13 305205) = some ⟨13, 2, 0, 587763, 305205, 3073, 16384⟩ := by
  decide +kernel

theorem context_13_305205_587763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305205 ⟨587763, by decide⟩ :=
  accepted_of_selected 13 305205 ⟨587763, by decide⟩ ⟨13, 2, 0, 587763, 305205, 3073, 16384⟩
    (by decide) selected_cut_23223

theorem selected_cut_23224 : selected 8 ⟨587786, by decide⟩
    (prefixPartial 13 305206) = some ⟨13, 2, 0, 587786, 305206, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_305206_587786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305206 ⟨587786, by decide⟩ :=
  accepted_of_selected 13 305206 ⟨587786, by decide⟩ ⟨13, 2, 0, 587786, 305206, 1717, 16384⟩
    (by decide) selected_cut_23224

theorem selected_cut_23225 : selected 8 ⟨587822, by decide⟩
    (prefixPartial 13 305207) = some ⟨13, 2, 0, 587822, 305207, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_305207_587822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305207 ⟨587822, by decide⟩ :=
  accepted_of_selected 13 305207 ⟨587822, by decide⟩ ⟨13, 2, 0, 587822, 305207, 1297, 16384⟩
    (by decide) selected_cut_23225

theorem unmarked_context_12_76301_587823 : frontier 9 ⟨587823, by decide⟩
    (prefixCache 12 76301) (prefixPartial 12 76301) = false := by
  decide +kernel

theorem node_context_12_76301_587823 : EJMOriginalGlobalDAGData.nodes 9 ⟨587823, by decide⟩ =
    .split (coordinate 12) (![⟨587710, by decide⟩,⟨587763, by decide⟩,⟨587786, by decide⟩,⟨587822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76301_587823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76301 ⟨587823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76301
    ⟨587823, by decide⟩ (by decide) (![⟨587710, by decide⟩,⟨587763, by decide⟩,⟨587786, by decide⟩,⟨587822, by decide⟩]) unmarked_context_12_76301_587823 node_context_12_76301_587823
  intro a
  fin_cases a
  · exact context_13_305204_587710
  · exact context_13_305205_587763
  · exact context_13_305206_587786
  · exact context_13_305207_587822

theorem selected_cut_23226 : selected 9 ⟨573823, by decide⟩
    (prefixPartial 12 76302) = some ⟨12, 1, 0, 573823, 76302, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76302_573823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76302 ⟨573823, by decide⟩ :=
  accepted_of_selected 12 76302 ⟨573823, by decide⟩ ⟨12, 1, 0, 573823, 76302, 1, 65536⟩
    (by decide) selected_cut_23226

theorem selected_cut_23227 : selected 9 ⟨518278, by decide⟩
    (prefixPartial 12 76303) = some ⟨12, 1, 0, 518278, 76303, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76303_518278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76303 ⟨518278, by decide⟩ :=
  accepted_of_selected 12 76303 ⟨518278, by decide⟩ ⟨12, 1, 0, 518278, 76303, 1, 65536⟩
    (by decide) selected_cut_23227

theorem unmarked_context_11_19075_587824 : frontier 10 ⟨587824, by decide⟩
    (prefixCache 11 19075) (prefixPartial 11 19075) = false := by
  decide +kernel

theorem node_context_11_19075_587824 : EJMOriginalGlobalDAGData.nodes 10 ⟨587824, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨587823, by decide⟩,⟨573823, by decide⟩,⟨518278, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19075_587824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19075 ⟨587824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19075
    ⟨587824, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨587823, by decide⟩,⟨573823, by decide⟩,⟨518278, by decide⟩]) unmarked_context_11_19075_587824 node_context_11_19075_587824
  intro a
  fin_cases a
  · exact context_12_76300_448748
  · exact context_12_76301_587823
  · exact context_12_76302_573823
  · exact context_12_76303_518278

theorem unmarked_context_10_4768_587825 : frontier 11 ⟨587825, by decide⟩
    (prefixCache 10 4768) (prefixPartial 10 4768) = false := by
  decide +kernel

theorem node_context_10_4768_587825 : EJMOriginalGlobalDAGData.nodes 11 ⟨587825, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨587291, by decide⟩,⟨587616, by decide⟩,⟨587824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4768_587825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4768 ⟨587825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4768
    ⟨587825, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨587291, by decide⟩,⟨587616, by decide⟩,⟨587824, by decide⟩]) unmarked_context_10_4768_587825 node_context_10_4768_587825
  intro a
  fin_cases a
  · exact context_11_19072_434745
  · exact context_11_19073_587291
  · exact context_11_19074_587616
  · exact context_11_19075_587824

theorem selected_cut_23228 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 76304) = some ⟨12, 1, 0, 435160, 76304, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76304_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76304 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 76304 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 76304, 1, 65536⟩
    (by decide) selected_cut_23228

theorem selected_cut_23229 : selected 8 ⟨587897, by decide⟩
    (prefixPartial 13 305220) = some ⟨13, 2, 0, 587897, 305220, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_305220_587897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305220 ⟨587897, by decide⟩ :=
  accepted_of_selected 13 305220 ⟨587897, by decide⟩ ⟨13, 2, 0, 587897, 305220, 2305, 16384⟩
    (by decide) selected_cut_23229

theorem selected_cut_23230 : selected 8 ⟨587934, by decide⟩
    (prefixPartial 13 305221) = some ⟨13, 2, 0, 587934, 305221, 2045, 16384⟩ := by
  decide +kernel

theorem context_13_305221_587934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305221 ⟨587934, by decide⟩ :=
  accepted_of_selected 13 305221 ⟨587934, by decide⟩ ⟨13, 2, 0, 587934, 305221, 2045, 16384⟩
    (by decide) selected_cut_23230

theorem selected_cut_23231 : selected 8 ⟨587957, by decide⟩
    (prefixPartial 13 305222) = some ⟨13, 2, 0, 587957, 305222, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_305222_587957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305222 ⟨587957, by decide⟩ :=
  accepted_of_selected 13 305222 ⟨587957, by decide⟩ ⟨13, 2, 0, 587957, 305222, 1437, 16384⟩
    (by decide) selected_cut_23231

theorem selected_cut_23232 : selected 8 ⟨587979, by decide⟩
    (prefixPartial 13 305223) = some ⟨13, 2, 0, 587979, 305223, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_305223_587979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305223 ⟨587979, by decide⟩ :=
  accepted_of_selected 13 305223 ⟨587979, by decide⟩ ⟨13, 2, 0, 587979, 305223, 1005, 16384⟩
    (by decide) selected_cut_23232

theorem unmarked_context_12_76305_587980 : frontier 9 ⟨587980, by decide⟩
    (prefixCache 12 76305) (prefixPartial 12 76305) = false := by
  decide +kernel

theorem node_context_12_76305_587980 : EJMOriginalGlobalDAGData.nodes 9 ⟨587980, by decide⟩ =
    .split (coordinate 12) (![⟨587897, by decide⟩,⟨587934, by decide⟩,⟨587957, by decide⟩,⟨587979, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76305_587980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76305 ⟨587980, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76305
    ⟨587980, by decide⟩ (by decide) (![⟨587897, by decide⟩,⟨587934, by decide⟩,⟨587957, by decide⟩,⟨587979, by decide⟩]) unmarked_context_12_76305_587980 node_context_12_76305_587980
  intro a
  fin_cases a
  · exact context_13_305220_587897
  · exact context_13_305221_587934
  · exact context_13_305222_587957
  · exact context_13_305223_587979

theorem selected_cut_23233 : selected 8 ⟨588018, by decide⟩
    (prefixPartial 13 305224) = some ⟨13, 2, 0, 588018, 305224, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_305224_588018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305224 ⟨588018, by decide⟩ :=
  accepted_of_selected 13 305224 ⟨588018, by decide⟩ ⟨13, 2, 0, 588018, 305224, 1845, 16384⟩
    (by decide) selected_cut_23233

theorem selected_cut_23234 : selected 8 ⟨588042, by decide⟩
    (prefixPartial 13 305225) = some ⟨13, 2, 0, 588042, 305225, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_305225_588042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305225 ⟨588042, by decide⟩ :=
  accepted_of_selected 13 305225 ⟨588042, by decide⟩ ⟨13, 2, 0, 588042, 305225, 1809, 16384⟩
    (by decide) selected_cut_23234

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
