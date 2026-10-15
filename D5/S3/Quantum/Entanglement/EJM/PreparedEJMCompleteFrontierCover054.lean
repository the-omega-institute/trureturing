/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover053
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_05187 : selected 8 ⟨161118, by decide⟩
    (prefixPartial 13 76905) = some ⟨13, 2, 0, 161118, 76905, 2861, 16384⟩ := by
  decide +kernel

theorem context_13_76905_161118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76905 ⟨161118, by decide⟩ :=
  accepted_of_selected 13 76905 ⟨161118, by decide⟩ ⟨13, 2, 0, 161118, 76905, 2861, 16384⟩
    (by decide) selected_cut_05187

theorem selected_cut_05188 : selected 8 ⟨161139, by decide⟩
    (prefixPartial 13 76906) = some ⟨13, 2, 0, 161139, 76906, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_76906_161139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76906 ⟨161139, by decide⟩ :=
  accepted_of_selected 13 76906 ⟨161139, by decide⟩ ⟨13, 2, 0, 161139, 76906, 1653, 16384⟩
    (by decide) selected_cut_05188

theorem selected_cut_05189 : selected 8 ⟨161145, by decide⟩
    (prefixPartial 13 76907) = some ⟨13, 2, 0, 161145, 76907, 817, 16384⟩ := by
  decide +kernel

theorem context_13_76907_161145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76907 ⟨161145, by decide⟩ :=
  accepted_of_selected 13 76907 ⟨161145, by decide⟩ ⟨13, 2, 0, 161145, 76907, 817, 16384⟩
    (by decide) selected_cut_05189

theorem unmarked_context_12_19226_161146 : frontier 9 ⟨161146, by decide⟩
    (prefixCache 12 19226) (prefixPartial 12 19226) = false := by
  decide +kernel

theorem node_context_12_19226_161146 : EJMOriginalGlobalDAGData.nodes 9 ⟨161146, by decide⟩ =
    .split (coordinate 12) (![⟨161087, by decide⟩,⟨161118, by decide⟩,⟨161139, by decide⟩,⟨161145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19226_161146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19226 ⟨161146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19226
    ⟨161146, by decide⟩ (by decide) (![⟨161087, by decide⟩,⟨161118, by decide⟩,⟨161139, by decide⟩,⟨161145, by decide⟩]) unmarked_context_12_19226_161146 node_context_12_19226_161146
  intro a
  fin_cases a
  · exact context_13_76904_161087
  · exact context_13_76905_161118
  · exact context_13_76906_161139
  · exact context_13_76907_161145

theorem selected_cut_05190 : selected 8 ⟨161168, by decide⟩
    (prefixPartial 13 76908) = some ⟨13, 2, 0, 161168, 76908, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_76908_161168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76908 ⟨161168, by decide⟩ :=
  accepted_of_selected 13 76908 ⟨161168, by decide⟩ ⟨13, 2, 0, 161168, 76908, 1589, 16384⟩
    (by decide) selected_cut_05190

theorem selected_cut_05191 : selected 8 ⟨161206, by decide⟩
    (prefixPartial 13 76909) = some ⟨13, 2, 0, 161206, 76909, 2981, 16384⟩ := by
  decide +kernel

theorem context_13_76909_161206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76909 ⟨161206, by decide⟩ :=
  accepted_of_selected 13 76909 ⟨161206, by decide⟩ ⟨13, 2, 0, 161206, 76909, 2981, 16384⟩
    (by decide) selected_cut_05191

theorem selected_cut_05192 : selected 8 ⟨161233, by decide⟩
    (prefixPartial 13 76910) = some ⟨13, 2, 0, 161233, 76910, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_76910_161233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76910 ⟨161233, by decide⟩ :=
  accepted_of_selected 13 76910 ⟨161233, by decide⟩ ⟨13, 2, 0, 161233, 76910, 1469, 16384⟩
    (by decide) selected_cut_05192

theorem selected_cut_05193 : selected 8 ⟨161241, by decide⟩
    (prefixPartial 13 76911) = some ⟨13, 2, 0, 161241, 76911, 789, 16384⟩ := by
  decide +kernel

theorem context_13_76911_161241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76911 ⟨161241, by decide⟩ :=
  accepted_of_selected 13 76911 ⟨161241, by decide⟩ ⟨13, 2, 0, 161241, 76911, 789, 16384⟩
    (by decide) selected_cut_05193

theorem unmarked_context_12_19227_161242 : frontier 9 ⟨161242, by decide⟩
    (prefixCache 12 19227) (prefixPartial 12 19227) = false := by
  decide +kernel

theorem node_context_12_19227_161242 : EJMOriginalGlobalDAGData.nodes 9 ⟨161242, by decide⟩ =
    .split (coordinate 12) (![⟨161168, by decide⟩,⟨161206, by decide⟩,⟨161233, by decide⟩,⟨161241, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19227_161242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19227 ⟨161242, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19227
    ⟨161242, by decide⟩ (by decide) (![⟨161168, by decide⟩,⟨161206, by decide⟩,⟨161233, by decide⟩,⟨161241, by decide⟩]) unmarked_context_12_19227_161242 node_context_12_19227_161242
  intro a
  fin_cases a
  · exact context_13_76908_161168
  · exact context_13_76909_161206
  · exact context_13_76910_161233
  · exact context_13_76911_161241

theorem unmarked_context_11_4806_161243 : frontier 10 ⟨161243, by decide⟩
    (prefixCache 11 4806) (prefixPartial 11 4806) = false := by
  decide +kernel

theorem node_context_11_4806_161243 : EJMOriginalGlobalDAGData.nodes 10 ⟨161243, by decide⟩ =
    .split (coordinate 11) (![⟨160956, by decide⟩,⟨161064, by decide⟩,⟨161146, by decide⟩,⟨161242, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4806_161243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4806 ⟨161243, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4806
    ⟨161243, by decide⟩ (by decide) (![⟨160956, by decide⟩,⟨161064, by decide⟩,⟨161146, by decide⟩,⟨161242, by decide⟩]) unmarked_context_11_4806_161243 node_context_11_4806_161243
  intro a
  fin_cases a
  · exact context_12_19224_160956
  · exact context_12_19225_161064
  · exact context_12_19226_161146
  · exact context_12_19227_161242

theorem selected_cut_05194 : selected 8 ⟨161261, by decide⟩
    (prefixPartial 13 76912) = some ⟨13, 2, 0, 161261, 76912, 1473, 16384⟩ := by
  decide +kernel

theorem context_13_76912_161261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76912 ⟨161261, by decide⟩ :=
  accepted_of_selected 13 76912 ⟨161261, by decide⟩ ⟨13, 2, 0, 161261, 76912, 1473, 16384⟩
    (by decide) selected_cut_05194

theorem selected_cut_05195 : selected 8 ⟨161297, by decide⟩
    (prefixPartial 13 76913) = some ⟨13, 2, 0, 161297, 76913, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_76913_161297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76913 ⟨161297, by decide⟩ :=
  accepted_of_selected 13 76913 ⟨161297, by decide⟩ ⟨13, 2, 0, 161297, 76913, 2517, 16384⟩
    (by decide) selected_cut_05195

theorem selected_cut_05196 : selected 8 ⟨161314, by decide⟩
    (prefixPartial 13 76914) = some ⟨13, 2, 0, 161314, 76914, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_76914_161314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76914 ⟨161314, by decide⟩ :=
  accepted_of_selected 13 76914 ⟨161314, by decide⟩ ⟨13, 2, 0, 161314, 76914, 1197, 16384⟩
    (by decide) selected_cut_05196

theorem selected_cut_05197 : selected 8 ⟨161320, by decide⟩
    (prefixPartial 13 76915) = some ⟨13, 2, 0, 161320, 76915, 769, 16384⟩ := by
  decide +kernel

theorem context_13_76915_161320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76915 ⟨161320, by decide⟩ :=
  accepted_of_selected 13 76915 ⟨161320, by decide⟩ ⟨13, 2, 0, 161320, 76915, 769, 16384⟩
    (by decide) selected_cut_05197

theorem unmarked_context_12_19228_161321 : frontier 9 ⟨161321, by decide⟩
    (prefixCache 12 19228) (prefixPartial 12 19228) = false := by
  decide +kernel

theorem node_context_12_19228_161321 : EJMOriginalGlobalDAGData.nodes 9 ⟨161321, by decide⟩ =
    .split (coordinate 12) (![⟨161261, by decide⟩,⟨161297, by decide⟩,⟨161314, by decide⟩,⟨161320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19228_161321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19228 ⟨161321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19228
    ⟨161321, by decide⟩ (by decide) (![⟨161261, by decide⟩,⟨161297, by decide⟩,⟨161314, by decide⟩,⟨161320, by decide⟩]) unmarked_context_12_19228_161321 node_context_12_19228_161321
  intro a
  fin_cases a
  · exact context_13_76912_161261
  · exact context_13_76913_161297
  · exact context_13_76914_161314
  · exact context_13_76915_161320

theorem selected_cut_05198 : selected 8 ⟨161344, by decide⟩
    (prefixPartial 13 76916) = some ⟨13, 2, 0, 161344, 76916, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_76916_161344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76916 ⟨161344, by decide⟩ :=
  accepted_of_selected 13 76916 ⟨161344, by decide⟩ ⟨13, 2, 0, 161344, 76916, 1861, 16384⟩
    (by decide) selected_cut_05198

theorem selected_cut_05199 : selected 8 ⟨161377, by decide⟩
    (prefixPartial 13 76917) = some ⟨13, 2, 0, 161377, 76917, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_76917_161377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76917 ⟨161377, by decide⟩ :=
  accepted_of_selected 13 76917 ⟨161377, by decide⟩ ⟨13, 2, 0, 161377, 76917, 2349, 16384⟩
    (by decide) selected_cut_05199

theorem selected_cut_05200 : selected 8 ⟨161394, by decide⟩
    (prefixPartial 13 76918) = some ⟨13, 2, 0, 161394, 76918, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_76918_161394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76918 ⟨161394, by decide⟩ :=
  accepted_of_selected 13 76918 ⟨161394, by decide⟩ ⟨13, 2, 0, 161394, 76918, 1373, 16384⟩
    (by decide) selected_cut_05200

theorem selected_cut_05201 : selected 8 ⟨161399, by decide⟩
    (prefixPartial 13 76919) = some ⟨13, 2, 0, 161399, 76919, 729, 16384⟩ := by
  decide +kernel

theorem context_13_76919_161399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76919 ⟨161399, by decide⟩ :=
  accepted_of_selected 13 76919 ⟨161399, by decide⟩ ⟨13, 2, 0, 161399, 76919, 729, 16384⟩
    (by decide) selected_cut_05201

theorem unmarked_context_12_19229_161400 : frontier 9 ⟨161400, by decide⟩
    (prefixCache 12 19229) (prefixPartial 12 19229) = false := by
  decide +kernel

theorem node_context_12_19229_161400 : EJMOriginalGlobalDAGData.nodes 9 ⟨161400, by decide⟩ =
    .split (coordinate 12) (![⟨161344, by decide⟩,⟨161377, by decide⟩,⟨161394, by decide⟩,⟨161399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19229_161400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19229 ⟨161400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19229
    ⟨161400, by decide⟩ (by decide) (![⟨161344, by decide⟩,⟨161377, by decide⟩,⟨161394, by decide⟩,⟨161399, by decide⟩]) unmarked_context_12_19229_161400 node_context_12_19229_161400
  intro a
  fin_cases a
  · exact context_13_76916_161344
  · exact context_13_76917_161377
  · exact context_13_76918_161394
  · exact context_13_76919_161399

theorem selected_cut_05202 : selected 8 ⟨161426, by decide⟩
    (prefixPartial 13 76920) = some ⟨13, 2, 0, 161426, 76920, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_76920_161426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76920 ⟨161426, by decide⟩ :=
  accepted_of_selected 13 76920 ⟨161426, by decide⟩ ⟨13, 2, 0, 161426, 76920, 1789, 16384⟩
    (by decide) selected_cut_05202

theorem selected_cut_05203 : selected 8 ⟨161469, by decide⟩
    (prefixPartial 13 76921) = some ⟨13, 2, 0, 161469, 76921, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_76921_161469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76921 ⟨161469, by decide⟩ :=
  accepted_of_selected 13 76921 ⟨161469, by decide⟩ ⟨13, 2, 0, 161469, 76921, 2905, 16384⟩
    (by decide) selected_cut_05203

theorem selected_cut_05204 : selected 8 ⟨161489, by decide⟩
    (prefixPartial 13 76922) = some ⟨13, 2, 0, 161489, 76922, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_76922_161489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76922 ⟨161489, by decide⟩ :=
  accepted_of_selected 13 76922 ⟨161489, by decide⟩ ⟨13, 2, 0, 161489, 76922, 1493, 16384⟩
    (by decide) selected_cut_05204

theorem selected_cut_05205 : selected 8 ⟨161499, by decide⟩
    (prefixPartial 13 76923) = some ⟨13, 2, 0, 161499, 76923, 829, 16384⟩ := by
  decide +kernel

theorem context_13_76923_161499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76923 ⟨161499, by decide⟩ :=
  accepted_of_selected 13 76923 ⟨161499, by decide⟩ ⟨13, 2, 0, 161499, 76923, 829, 16384⟩
    (by decide) selected_cut_05205

theorem unmarked_context_12_19230_161500 : frontier 9 ⟨161500, by decide⟩
    (prefixCache 12 19230) (prefixPartial 12 19230) = false := by
  decide +kernel

theorem node_context_12_19230_161500 : EJMOriginalGlobalDAGData.nodes 9 ⟨161500, by decide⟩ =
    .split (coordinate 12) (![⟨161426, by decide⟩,⟨161469, by decide⟩,⟨161489, by decide⟩,⟨161499, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19230_161500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19230 ⟨161500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19230
    ⟨161500, by decide⟩ (by decide) (![⟨161426, by decide⟩,⟨161469, by decide⟩,⟨161489, by decide⟩,⟨161499, by decide⟩]) unmarked_context_12_19230_161500 node_context_12_19230_161500
  intro a
  fin_cases a
  · exact context_13_76920_161426
  · exact context_13_76921_161469
  · exact context_13_76922_161489
  · exact context_13_76923_161499

theorem selected_cut_05206 : selected 8 ⟨161540, by decide⟩
    (prefixPartial 13 76924) = some ⟨13, 2, 0, 161540, 76924, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_76924_161540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76924 ⟨161540, by decide⟩ :=
  accepted_of_selected 13 76924 ⟨161540, by decide⟩ ⟨13, 2, 0, 161540, 76924, 2285, 16384⟩
    (by decide) selected_cut_05206

theorem selected_cut_05207 : selected 8 ⟨161610, by decide⟩
    (prefixPartial 13 76925) = some ⟨13, 2, 0, 161610, 76925, 3981, 16384⟩ := by
  decide +kernel

theorem context_13_76925_161610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76925 ⟨161610, by decide⟩ :=
  accepted_of_selected 13 76925 ⟨161610, by decide⟩ ⟨13, 2, 0, 161610, 76925, 3981, 16384⟩
    (by decide) selected_cut_05207

theorem selected_cut_05208 : selected 8 ⟨161645, by decide⟩
    (prefixPartial 13 76926) = some ⟨13, 2, 0, 161645, 76926, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_76926_161645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76926 ⟨161645, by decide⟩ :=
  accepted_of_selected 13 76926 ⟨161645, by decide⟩ ⟨13, 2, 0, 161645, 76926, 1833, 16384⟩
    (by decide) selected_cut_05208

theorem selected_cut_05209 : selected 8 ⟨161659, by decide⟩
    (prefixPartial 13 76927) = some ⟨13, 2, 0, 161659, 76927, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_76927_161659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76927 ⟨161659, by decide⟩ :=
  accepted_of_selected 13 76927 ⟨161659, by decide⟩ ⟨13, 2, 0, 161659, 76927, 1001, 16384⟩
    (by decide) selected_cut_05209

theorem unmarked_context_12_19231_161660 : frontier 9 ⟨161660, by decide⟩
    (prefixCache 12 19231) (prefixPartial 12 19231) = false := by
  decide +kernel

theorem node_context_12_19231_161660 : EJMOriginalGlobalDAGData.nodes 9 ⟨161660, by decide⟩ =
    .split (coordinate 12) (![⟨161540, by decide⟩,⟨161610, by decide⟩,⟨161645, by decide⟩,⟨161659, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19231_161660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19231 ⟨161660, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19231
    ⟨161660, by decide⟩ (by decide) (![⟨161540, by decide⟩,⟨161610, by decide⟩,⟨161645, by decide⟩,⟨161659, by decide⟩]) unmarked_context_12_19231_161660 node_context_12_19231_161660
  intro a
  fin_cases a
  · exact context_13_76924_161540
  · exact context_13_76925_161610
  · exact context_13_76926_161645
  · exact context_13_76927_161659

theorem unmarked_context_11_4807_161661 : frontier 10 ⟨161661, by decide⟩
    (prefixCache 11 4807) (prefixPartial 11 4807) = false := by
  decide +kernel

theorem node_context_11_4807_161661 : EJMOriginalGlobalDAGData.nodes 10 ⟨161661, by decide⟩ =
    .split (coordinate 11) (![⟨161321, by decide⟩,⟨161400, by decide⟩,⟨161500, by decide⟩,⟨161660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4807_161661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4807 ⟨161661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4807
    ⟨161661, by decide⟩ (by decide) (![⟨161321, by decide⟩,⟨161400, by decide⟩,⟨161500, by decide⟩,⟨161660, by decide⟩]) unmarked_context_11_4807_161661 node_context_11_4807_161661
  intro a
  fin_cases a
  · exact context_12_19228_161321
  · exact context_12_19229_161400
  · exact context_12_19230_161500
  · exact context_12_19231_161660

theorem unmarked_context_10_1201_161662 : frontier 11 ⟨161662, by decide⟩
    (prefixCache 10 1201) (prefixPartial 10 1201) = false := by
  decide +kernel

theorem node_context_10_1201_161662 : EJMOriginalGlobalDAGData.nodes 11 ⟨161662, by decide⟩ =
    .split (coordinate 10) (![⟨160476, by decide⟩,⟨160874, by decide⟩,⟨161243, by decide⟩,⟨161661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1201_161662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1201 ⟨161662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1201
    ⟨161662, by decide⟩ (by decide) (![⟨160476, by decide⟩,⟨160874, by decide⟩,⟨161243, by decide⟩,⟨161661, by decide⟩]) unmarked_context_10_1201_161662 node_context_10_1201_161662
  intro a
  fin_cases a
  · exact context_11_4804_160476
  · exact context_11_4805_160874
  · exact context_11_4806_161243
  · exact context_11_4807_161661

theorem selected_cut_05210 : selected 8 ⟨161701, by decide⟩
    (prefixPartial 13 76928) = some ⟨13, 2, 0, 161701, 76928, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_76928_161701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76928 ⟨161701, by decide⟩ :=
  accepted_of_selected 13 76928 ⟨161701, by decide⟩ ⟨13, 2, 0, 161701, 76928, 1729, 16384⟩
    (by decide) selected_cut_05210

theorem selected_cut_05211 : selected 8 ⟨161765, by decide⟩
    (prefixPartial 13 76929) = some ⟨13, 2, 0, 161765, 76929, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_76929_161765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76929 ⟨161765, by decide⟩ :=
  accepted_of_selected 13 76929 ⟨161765, by decide⟩ ⟨13, 2, 0, 161765, 76929, 2857, 16384⟩
    (by decide) selected_cut_05211

theorem selected_cut_05212 : selected 8 ⟨161780, by decide⟩
    (prefixPartial 13 76930) = some ⟨13, 2, 0, 161780, 76930, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_76930_161780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76930 ⟨161780, by decide⟩ :=
  accepted_of_selected 13 76930 ⟨161780, by decide⟩ ⟨13, 2, 0, 161780, 76930, 1017, 16384⟩
    (by decide) selected_cut_05212

theorem selected_cut_05213 : selected 8 ⟨161784, by decide⟩
    (prefixPartial 13 76931) = some ⟨13, 2, 0, 161784, 76931, 865, 16384⟩ := by
  decide +kernel

theorem context_13_76931_161784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76931 ⟨161784, by decide⟩ :=
  accepted_of_selected 13 76931 ⟨161784, by decide⟩ ⟨13, 2, 0, 161784, 76931, 865, 16384⟩
    (by decide) selected_cut_05213

theorem unmarked_context_12_19232_161785 : frontier 9 ⟨161785, by decide⟩
    (prefixCache 12 19232) (prefixPartial 12 19232) = false := by
  decide +kernel

theorem node_context_12_19232_161785 : EJMOriginalGlobalDAGData.nodes 9 ⟨161785, by decide⟩ =
    .split (coordinate 12) (![⟨161701, by decide⟩,⟨161765, by decide⟩,⟨161780, by decide⟩,⟨161784, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19232_161785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19232 ⟨161785, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19232
    ⟨161785, by decide⟩ (by decide) (![⟨161701, by decide⟩,⟨161765, by decide⟩,⟨161780, by decide⟩,⟨161784, by decide⟩]) unmarked_context_12_19232_161785 node_context_12_19232_161785
  intro a
  fin_cases a
  · exact context_13_76928_161701
  · exact context_13_76929_161765
  · exact context_13_76930_161780
  · exact context_13_76931_161784

theorem selected_cut_05214 : selected 8 ⟨161820, by decide⟩
    (prefixPartial 13 76932) = some ⟨13, 2, 0, 161820, 76932, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_76932_161820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76932 ⟨161820, by decide⟩ :=
  accepted_of_selected 13 76932 ⟨161820, by decide⟩ ⟨13, 2, 0, 161820, 76932, 1653, 16384⟩
    (by decide) selected_cut_05214

theorem selected_cut_05215 : selected 8 ⟨161888, by decide⟩
    (prefixPartial 13 76933) = some ⟨13, 2, 0, 161888, 76933, 2493, 16384⟩ := by
  decide +kernel

theorem context_13_76933_161888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76933 ⟨161888, by decide⟩ :=
  accepted_of_selected 13 76933 ⟨161888, by decide⟩ ⟨13, 2, 0, 161888, 76933, 2493, 16384⟩
    (by decide) selected_cut_05215

theorem selected_cut_05216 : selected 8 ⟨161904, by decide⟩
    (prefixPartial 13 76934) = some ⟨13, 2, 0, 161904, 76934, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_76934_161904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76934 ⟨161904, by decide⟩ :=
  accepted_of_selected 13 76934 ⟨161904, by decide⟩ ⟨13, 2, 0, 161904, 76934, 1069, 16384⟩
    (by decide) selected_cut_05216

theorem selected_cut_05217 : selected 8 ⟨161907, by decide⟩
    (prefixPartial 13 76935) = some ⟨13, 2, 0, 161907, 76935, 613, 16384⟩ := by
  decide +kernel

theorem context_13_76935_161907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76935 ⟨161907, by decide⟩ :=
  accepted_of_selected 13 76935 ⟨161907, by decide⟩ ⟨13, 2, 0, 161907, 76935, 613, 16384⟩
    (by decide) selected_cut_05217

theorem unmarked_context_12_19233_161908 : frontier 9 ⟨161908, by decide⟩
    (prefixCache 12 19233) (prefixPartial 12 19233) = false := by
  decide +kernel

theorem node_context_12_19233_161908 : EJMOriginalGlobalDAGData.nodes 9 ⟨161908, by decide⟩ =
    .split (coordinate 12) (![⟨161820, by decide⟩,⟨161888, by decide⟩,⟨161904, by decide⟩,⟨161907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19233_161908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19233 ⟨161908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19233
    ⟨161908, by decide⟩ (by decide) (![⟨161820, by decide⟩,⟨161888, by decide⟩,⟨161904, by decide⟩,⟨161907, by decide⟩]) unmarked_context_12_19233_161908 node_context_12_19233_161908
  intro a
  fin_cases a
  · exact context_13_76932_161820
  · exact context_13_76933_161888
  · exact context_13_76934_161904
  · exact context_13_76935_161907

theorem selected_cut_05218 : selected 8 ⟨161937, by decide⟩
    (prefixPartial 13 76936) = some ⟨13, 2, 0, 161937, 76936, 1665, 16384⟩ := by
  decide +kernel

theorem context_13_76936_161937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76936 ⟨161937, by decide⟩ :=
  accepted_of_selected 13 76936 ⟨161937, by decide⟩ ⟨13, 2, 0, 161937, 76936, 1665, 16384⟩
    (by decide) selected_cut_05218

theorem selected_cut_05219 : selected 8 ⟨162003, by decide⟩
    (prefixPartial 13 76937) = some ⟨13, 2, 0, 162003, 76937, 2873, 16384⟩ := by
  decide +kernel

theorem context_13_76937_162003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76937 ⟨162003, by decide⟩ :=
  accepted_of_selected 13 76937 ⟨162003, by decide⟩ ⟨13, 2, 0, 162003, 76937, 2873, 16384⟩
    (by decide) selected_cut_05219

theorem selected_cut_05220 : selected 8 ⟨162020, by decide⟩
    (prefixPartial 13 76938) = some ⟨13, 2, 0, 162020, 76938, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_76938_162020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76938 ⟨162020, by decide⟩ :=
  accepted_of_selected 13 76938 ⟨162020, by decide⟩ ⟨13, 2, 0, 162020, 76938, 1193, 16384⟩
    (by decide) selected_cut_05220

theorem selected_cut_05221 : selected 8 ⟨162027, by decide⟩
    (prefixPartial 13 76939) = some ⟨13, 2, 0, 162027, 76939, 657, 16384⟩ := by
  decide +kernel

theorem context_13_76939_162027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76939 ⟨162027, by decide⟩ :=
  accepted_of_selected 13 76939 ⟨162027, by decide⟩ ⟨13, 2, 0, 162027, 76939, 657, 16384⟩
    (by decide) selected_cut_05221

theorem unmarked_context_12_19234_162028 : frontier 9 ⟨162028, by decide⟩
    (prefixCache 12 19234) (prefixPartial 12 19234) = false := by
  decide +kernel

theorem node_context_12_19234_162028 : EJMOriginalGlobalDAGData.nodes 9 ⟨162028, by decide⟩ =
    .split (coordinate 12) (![⟨161937, by decide⟩,⟨162003, by decide⟩,⟨162020, by decide⟩,⟨162027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19234_162028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19234 ⟨162028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19234
    ⟨162028, by decide⟩ (by decide) (![⟨161937, by decide⟩,⟨162003, by decide⟩,⟨162020, by decide⟩,⟨162027, by decide⟩]) unmarked_context_12_19234_162028 node_context_12_19234_162028
  intro a
  fin_cases a
  · exact context_13_76936_161937
  · exact context_13_76937_162003
  · exact context_13_76938_162020
  · exact context_13_76939_162027

theorem selected_cut_05222 : selected 8 ⟨162052, by decide⟩
    (prefixPartial 13 76940) = some ⟨13, 2, 0, 162052, 76940, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_76940_162052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76940 ⟨162052, by decide⟩ :=
  accepted_of_selected 13 76940 ⟨162052, by decide⟩ ⟨13, 2, 0, 162052, 76940, 1305, 16384⟩
    (by decide) selected_cut_05222

theorem selected_cut_05223 : selected 8 ⟨162107, by decide⟩
    (prefixPartial 13 76941) = some ⟨13, 2, 0, 162107, 76941, 2465, 16384⟩ := by
  decide +kernel

theorem context_13_76941_162107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76941 ⟨162107, by decide⟩ :=
  accepted_of_selected 13 76941 ⟨162107, by decide⟩ ⟨13, 2, 0, 162107, 76941, 2465, 16384⟩
    (by decide) selected_cut_05223

theorem selected_cut_05224 : selected 8 ⟨162121, by decide⟩
    (prefixPartial 13 76942) = some ⟨13, 2, 0, 162121, 76942, 1089, 16384⟩ := by
  decide +kernel

theorem context_13_76942_162121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76942 ⟨162121, by decide⟩ :=
  accepted_of_selected 13 76942 ⟨162121, by decide⟩ ⟨13, 2, 0, 162121, 76942, 1089, 16384⟩
    (by decide) selected_cut_05224

theorem selected_cut_05225 : selected 8 ⟨162125, by decide⟩
    (prefixPartial 13 76943) = some ⟨13, 2, 0, 162125, 76943, 601, 16384⟩ := by
  decide +kernel

theorem context_13_76943_162125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76943 ⟨162125, by decide⟩ :=
  accepted_of_selected 13 76943 ⟨162125, by decide⟩ ⟨13, 2, 0, 162125, 76943, 601, 16384⟩
    (by decide) selected_cut_05225

theorem unmarked_context_12_19235_162126 : frontier 9 ⟨162126, by decide⟩
    (prefixCache 12 19235) (prefixPartial 12 19235) = false := by
  decide +kernel

theorem node_context_12_19235_162126 : EJMOriginalGlobalDAGData.nodes 9 ⟨162126, by decide⟩ =
    .split (coordinate 12) (![⟨162052, by decide⟩,⟨162107, by decide⟩,⟨162121, by decide⟩,⟨162125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19235_162126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19235 ⟨162126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19235
    ⟨162126, by decide⟩ (by decide) (![⟨162052, by decide⟩,⟨162107, by decide⟩,⟨162121, by decide⟩,⟨162125, by decide⟩]) unmarked_context_12_19235_162126 node_context_12_19235_162126
  intro a
  fin_cases a
  · exact context_13_76940_162052
  · exact context_13_76941_162107
  · exact context_13_76942_162121
  · exact context_13_76943_162125

theorem unmarked_context_11_4808_162127 : frontier 10 ⟨162127, by decide⟩
    (prefixCache 11 4808) (prefixPartial 11 4808) = false := by
  decide +kernel

theorem node_context_11_4808_162127 : EJMOriginalGlobalDAGData.nodes 10 ⟨162127, by decide⟩ =
    .split (coordinate 11) (![⟨161785, by decide⟩,⟨161908, by decide⟩,⟨162028, by decide⟩,⟨162126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4808_162127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4808 ⟨162127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4808
    ⟨162127, by decide⟩ (by decide) (![⟨161785, by decide⟩,⟨161908, by decide⟩,⟨162028, by decide⟩,⟨162126, by decide⟩]) unmarked_context_11_4808_162127 node_context_11_4808_162127
  intro a
  fin_cases a
  · exact context_12_19232_161785
  · exact context_12_19233_161908
  · exact context_12_19234_162028
  · exact context_12_19235_162126

theorem selected_cut_05226 : selected 8 ⟨162152, by decide⟩
    (prefixPartial 13 76944) = some ⟨13, 2, 0, 162152, 76944, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_76944_162152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76944 ⟨162152, by decide⟩ :=
  accepted_of_selected 13 76944 ⟨162152, by decide⟩ ⟨13, 2, 0, 162152, 76944, 1245, 16384⟩
    (by decide) selected_cut_05226

theorem selected_cut_05227 : selected 8 ⟨162208, by decide⟩
    (prefixPartial 13 76945) = some ⟨13, 2, 0, 162208, 76945, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_76945_162208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76945 ⟨162208, by decide⟩ :=
  accepted_of_selected 13 76945 ⟨162208, by decide⟩ ⟨13, 2, 0, 162208, 76945, 2729, 16384⟩
    (by decide) selected_cut_05227

theorem selected_cut_05228 : selected 8 ⟨162228, by decide⟩
    (prefixPartial 13 76946) = some ⟨13, 2, 0, 162228, 76946, 1209, 16384⟩ := by
  decide +kernel

theorem context_13_76946_162228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76946 ⟨162228, by decide⟩ :=
  accepted_of_selected 13 76946 ⟨162228, by decide⟩ ⟨13, 2, 0, 162228, 76946, 1209, 16384⟩
    (by decide) selected_cut_05228

theorem selected_cut_05229 : selected 8 ⟨162234, by decide⟩
    (prefixPartial 13 76947) = some ⟨13, 2, 0, 162234, 76947, 977, 16384⟩ := by
  decide +kernel

theorem context_13_76947_162234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76947 ⟨162234, by decide⟩ :=
  accepted_of_selected 13 76947 ⟨162234, by decide⟩ ⟨13, 2, 0, 162234, 76947, 977, 16384⟩
    (by decide) selected_cut_05229

theorem unmarked_context_12_19236_162235 : frontier 9 ⟨162235, by decide⟩
    (prefixCache 12 19236) (prefixPartial 12 19236) = false := by
  decide +kernel

theorem node_context_12_19236_162235 : EJMOriginalGlobalDAGData.nodes 9 ⟨162235, by decide⟩ =
    .split (coordinate 12) (![⟨162152, by decide⟩,⟨162208, by decide⟩,⟨162228, by decide⟩,⟨162234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19236_162235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19236 ⟨162235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19236
    ⟨162235, by decide⟩ (by decide) (![⟨162152, by decide⟩,⟨162208, by decide⟩,⟨162228, by decide⟩,⟨162234, by decide⟩]) unmarked_context_12_19236_162235 node_context_12_19236_162235
  intro a
  fin_cases a
  · exact context_13_76944_162152
  · exact context_13_76945_162208
  · exact context_13_76946_162228
  · exact context_13_76947_162234

theorem selected_cut_05230 : selected 8 ⟨162265, by decide⟩
    (prefixPartial 13 76948) = some ⟨13, 2, 0, 162265, 76948, 1257, 16384⟩ := by
  decide +kernel

theorem context_13_76948_162265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76948 ⟨162265, by decide⟩ :=
  accepted_of_selected 13 76948 ⟨162265, by decide⟩ ⟨13, 2, 0, 162265, 76948, 1257, 16384⟩
    (by decide) selected_cut_05230

theorem selected_cut_05231 : selected 8 ⟨162310, by decide⟩
    (prefixPartial 13 76949) = some ⟨13, 2, 0, 162310, 76949, 2345, 16384⟩ := by
  decide +kernel

theorem context_13_76949_162310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76949 ⟨162310, by decide⟩ :=
  accepted_of_selected 13 76949 ⟨162310, by decide⟩ ⟨13, 2, 0, 162310, 76949, 2345, 16384⟩
    (by decide) selected_cut_05231

theorem selected_cut_05232 : selected 8 ⟨162327, by decide⟩
    (prefixPartial 13 76950) = some ⟨13, 2, 0, 162327, 76950, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_76950_162327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76950 ⟨162327, by decide⟩ :=
  accepted_of_selected 13 76950 ⟨162327, by decide⟩ ⟨13, 2, 0, 162327, 76950, 1293, 16384⟩
    (by decide) selected_cut_05232

theorem selected_cut_05233 : selected 8 ⟨162336, by decide⟩
    (prefixPartial 13 76951) = some ⟨13, 2, 0, 162336, 76951, 765, 16384⟩ := by
  decide +kernel

theorem context_13_76951_162336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76951 ⟨162336, by decide⟩ :=
  accepted_of_selected 13 76951 ⟨162336, by decide⟩ ⟨13, 2, 0, 162336, 76951, 765, 16384⟩
    (by decide) selected_cut_05233

theorem unmarked_context_12_19237_162337 : frontier 9 ⟨162337, by decide⟩
    (prefixCache 12 19237) (prefixPartial 12 19237) = false := by
  decide +kernel

theorem node_context_12_19237_162337 : EJMOriginalGlobalDAGData.nodes 9 ⟨162337, by decide⟩ =
    .split (coordinate 12) (![⟨162265, by decide⟩,⟨162310, by decide⟩,⟨162327, by decide⟩,⟨162336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19237_162337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19237 ⟨162337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19237
    ⟨162337, by decide⟩ (by decide) (![⟨162265, by decide⟩,⟨162310, by decide⟩,⟨162327, by decide⟩,⟨162336, by decide⟩]) unmarked_context_12_19237_162337 node_context_12_19237_162337
  intro a
  fin_cases a
  · exact context_13_76948_162265
  · exact context_13_76949_162310
  · exact context_13_76950_162327
  · exact context_13_76951_162336

theorem selected_cut_05234 : selected 8 ⟨162361, by decide⟩
    (prefixPartial 13 76952) = some ⟨13, 2, 0, 162361, 76952, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_76952_162361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76952 ⟨162361, by decide⟩ :=
  accepted_of_selected 13 76952 ⟨162361, by decide⟩ ⟨13, 2, 0, 162361, 76952, 1401, 16384⟩
    (by decide) selected_cut_05234

theorem selected_cut_05235 : selected 8 ⟨162406, by decide⟩
    (prefixPartial 13 76953) = some ⟨13, 2, 0, 162406, 76953, 2721, 16384⟩ := by
  decide +kernel

theorem context_13_76953_162406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76953 ⟨162406, by decide⟩ :=
  accepted_of_selected 13 76953 ⟨162406, by decide⟩ ⟨13, 2, 0, 162406, 76953, 2721, 16384⟩
    (by decide) selected_cut_05235

theorem selected_cut_05236 : selected 8 ⟨162425, by decide⟩
    (prefixPartial 13 76954) = some ⟨13, 2, 0, 162425, 76954, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_76954_162425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76954 ⟨162425, by decide⟩ :=
  accepted_of_selected 13 76954 ⟨162425, by decide⟩ ⟨13, 2, 0, 162425, 76954, 1493, 16384⟩
    (by decide) selected_cut_05236

theorem selected_cut_05237 : selected 8 ⟨162434, by decide⟩
    (prefixPartial 13 76955) = some ⟨13, 2, 0, 162434, 76955, 957, 16384⟩ := by
  decide +kernel

theorem context_13_76955_162434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76955 ⟨162434, by decide⟩ :=
  accepted_of_selected 13 76955 ⟨162434, by decide⟩ ⟨13, 2, 0, 162434, 76955, 957, 16384⟩
    (by decide) selected_cut_05237

theorem unmarked_context_12_19238_162435 : frontier 9 ⟨162435, by decide⟩
    (prefixCache 12 19238) (prefixPartial 12 19238) = false := by
  decide +kernel

theorem node_context_12_19238_162435 : EJMOriginalGlobalDAGData.nodes 9 ⟨162435, by decide⟩ =
    .split (coordinate 12) (![⟨162361, by decide⟩,⟨162406, by decide⟩,⟨162425, by decide⟩,⟨162434, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19238_162435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19238 ⟨162435, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19238
    ⟨162435, by decide⟩ (by decide) (![⟨162361, by decide⟩,⟨162406, by decide⟩,⟨162425, by decide⟩,⟨162434, by decide⟩]) unmarked_context_12_19238_162435 node_context_12_19238_162435
  intro a
  fin_cases a
  · exact context_13_76952_162361
  · exact context_13_76953_162406
  · exact context_13_76954_162425
  · exact context_13_76955_162434

theorem selected_cut_05238 : selected 8 ⟨162453, by decide⟩
    (prefixPartial 13 76956) = some ⟨13, 2, 0, 162453, 76956, 1121, 16384⟩ := by
  decide +kernel

theorem context_13_76956_162453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76956 ⟨162453, by decide⟩ :=
  accepted_of_selected 13 76956 ⟨162453, by decide⟩ ⟨13, 2, 0, 162453, 76956, 1121, 16384⟩
    (by decide) selected_cut_05238

theorem selected_cut_05239 : selected 8 ⟨162501, by decide⟩
    (prefixPartial 13 76957) = some ⟨13, 2, 0, 162501, 76957, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_76957_162501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76957 ⟨162501, by decide⟩ :=
  accepted_of_selected 13 76957 ⟨162501, by decide⟩ ⟨13, 2, 0, 162501, 76957, 2409, 16384⟩
    (by decide) selected_cut_05239

theorem selected_cut_05240 : selected 8 ⟨162517, by decide⟩
    (prefixPartial 13 76958) = some ⟨13, 2, 0, 162517, 76958, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_76958_162517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76958 ⟨162517, by decide⟩ :=
  accepted_of_selected 13 76958 ⟨162517, by decide⟩ ⟨13, 2, 0, 162517, 76958, 1373, 16384⟩
    (by decide) selected_cut_05240

theorem selected_cut_05241 : selected 8 ⟨162528, by decide⟩
    (prefixPartial 13 76959) = some ⟨13, 2, 0, 162528, 76959, 805, 16384⟩ := by
  decide +kernel

theorem context_13_76959_162528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76959 ⟨162528, by decide⟩ :=
  accepted_of_selected 13 76959 ⟨162528, by decide⟩ ⟨13, 2, 0, 162528, 76959, 805, 16384⟩
    (by decide) selected_cut_05241

theorem unmarked_context_12_19239_162529 : frontier 9 ⟨162529, by decide⟩
    (prefixCache 12 19239) (prefixPartial 12 19239) = false := by
  decide +kernel

theorem node_context_12_19239_162529 : EJMOriginalGlobalDAGData.nodes 9 ⟨162529, by decide⟩ =
    .split (coordinate 12) (![⟨162453, by decide⟩,⟨162501, by decide⟩,⟨162517, by decide⟩,⟨162528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19239_162529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19239 ⟨162529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19239
    ⟨162529, by decide⟩ (by decide) (![⟨162453, by decide⟩,⟨162501, by decide⟩,⟨162517, by decide⟩,⟨162528, by decide⟩]) unmarked_context_12_19239_162529 node_context_12_19239_162529
  intro a
  fin_cases a
  · exact context_13_76956_162453
  · exact context_13_76957_162501
  · exact context_13_76958_162517
  · exact context_13_76959_162528

theorem unmarked_context_11_4809_162530 : frontier 10 ⟨162530, by decide⟩
    (prefixCache 11 4809) (prefixPartial 11 4809) = false := by
  decide +kernel

theorem node_context_11_4809_162530 : EJMOriginalGlobalDAGData.nodes 10 ⟨162530, by decide⟩ =
    .split (coordinate 11) (![⟨162235, by decide⟩,⟨162337, by decide⟩,⟨162435, by decide⟩,⟨162529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4809_162530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4809 ⟨162530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4809
    ⟨162530, by decide⟩ (by decide) (![⟨162235, by decide⟩,⟨162337, by decide⟩,⟨162435, by decide⟩,⟨162529, by decide⟩]) unmarked_context_11_4809_162530 node_context_11_4809_162530
  intro a
  fin_cases a
  · exact context_12_19236_162235
  · exact context_12_19237_162337
  · exact context_12_19238_162435
  · exact context_12_19239_162529

theorem selected_cut_05242 : selected 8 ⟨162550, by decide⟩
    (prefixPartial 13 76960) = some ⟨13, 2, 0, 162550, 76960, 1317, 16384⟩ := by
  decide +kernel

theorem context_13_76960_162550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76960 ⟨162550, by decide⟩ :=
  accepted_of_selected 13 76960 ⟨162550, by decide⟩ ⟨13, 2, 0, 162550, 76960, 1317, 16384⟩
    (by decide) selected_cut_05242

theorem selected_cut_05243 : selected 8 ⟨162626, by decide⟩
    (prefixPartial 13 76961) = some ⟨13, 2, 0, 162626, 76961, 3185, 16384⟩ := by
  decide +kernel

theorem context_13_76961_162626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76961 ⟨162626, by decide⟩ :=
  accepted_of_selected 13 76961 ⟨162626, by decide⟩ ⟨13, 2, 0, 162626, 76961, 3185, 16384⟩
    (by decide) selected_cut_05243

theorem selected_cut_05244 : selected 8 ⟨162649, by decide⟩
    (prefixPartial 13 76962) = some ⟨13, 2, 0, 162649, 76962, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_76962_162649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76962 ⟨162649, by decide⟩ :=
  accepted_of_selected 13 76962 ⟨162649, by decide⟩ ⟨13, 2, 0, 162649, 76962, 1465, 16384⟩
    (by decide) selected_cut_05244

theorem selected_cut_05245 : selected 8 ⟨162661, by decide⟩
    (prefixPartial 13 76963) = some ⟨13, 2, 0, 162661, 76963, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_76963_162661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76963 ⟨162661, by decide⟩ :=
  accepted_of_selected 13 76963 ⟨162661, by decide⟩ ⟨13, 2, 0, 162661, 76963, 1113, 16384⟩
    (by decide) selected_cut_05245

theorem unmarked_context_12_19240_162662 : frontier 9 ⟨162662, by decide⟩
    (prefixCache 12 19240) (prefixPartial 12 19240) = false := by
  decide +kernel

theorem node_context_12_19240_162662 : EJMOriginalGlobalDAGData.nodes 9 ⟨162662, by decide⟩ =
    .split (coordinate 12) (![⟨162550, by decide⟩,⟨162626, by decide⟩,⟨162649, by decide⟩,⟨162661, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19240_162662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19240 ⟨162662, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19240
    ⟨162662, by decide⟩ (by decide) (![⟨162550, by decide⟩,⟨162626, by decide⟩,⟨162649, by decide⟩,⟨162661, by decide⟩]) unmarked_context_12_19240_162662 node_context_12_19240_162662
  intro a
  fin_cases a
  · exact context_13_76960_162550
  · exact context_13_76961_162626
  · exact context_13_76962_162649
  · exact context_13_76963_162661

theorem selected_cut_05246 : selected 8 ⟨162690, by decide⟩
    (prefixPartial 13 76964) = some ⟨13, 2, 0, 162690, 76964, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_76964_162690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76964 ⟨162690, by decide⟩ :=
  accepted_of_selected 13 76964 ⟨162690, by decide⟩ ⟨13, 2, 0, 162690, 76964, 1633, 16384⟩
    (by decide) selected_cut_05246

theorem selected_cut_05247 : selected 8 ⟨162763, by decide⟩
    (prefixPartial 13 76965) = some ⟨13, 2, 0, 162763, 76965, 3489, 16384⟩ := by
  decide +kernel

theorem context_13_76965_162763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76965 ⟨162763, by decide⟩ :=
  accepted_of_selected 13 76965 ⟨162763, by decide⟩ ⟨13, 2, 0, 162763, 76965, 3489, 16384⟩
    (by decide) selected_cut_05247

theorem selected_cut_05248 : selected 8 ⟨162785, by decide⟩
    (prefixPartial 13 76966) = some ⟨13, 2, 0, 162785, 76966, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_76966_162785 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76966 ⟨162785, by decide⟩ :=
  accepted_of_selected 13 76966 ⟨162785, by decide⟩ ⟨13, 2, 0, 162785, 76966, 1669, 16384⟩
    (by decide) selected_cut_05248

theorem selected_cut_05249 : selected 8 ⟨162797, by decide⟩
    (prefixPartial 13 76967) = some ⟨13, 2, 0, 162797, 76967, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_76967_162797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76967 ⟨162797, by decide⟩ :=
  accepted_of_selected 13 76967 ⟨162797, by decide⟩ ⟨13, 2, 0, 162797, 76967, 1073, 16384⟩
    (by decide) selected_cut_05249

theorem unmarked_context_12_19241_162798 : frontier 9 ⟨162798, by decide⟩
    (prefixCache 12 19241) (prefixPartial 12 19241) = false := by
  decide +kernel

theorem node_context_12_19241_162798 : EJMOriginalGlobalDAGData.nodes 9 ⟨162798, by decide⟩ =
    .split (coordinate 12) (![⟨162690, by decide⟩,⟨162763, by decide⟩,⟨162785, by decide⟩,⟨162797, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19241_162798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19241 ⟨162798, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19241
    ⟨162798, by decide⟩ (by decide) (![⟨162690, by decide⟩,⟨162763, by decide⟩,⟨162785, by decide⟩,⟨162797, by decide⟩]) unmarked_context_12_19241_162798 node_context_12_19241_162798
  intro a
  fin_cases a
  · exact context_13_76964_162690
  · exact context_13_76965_162763
  · exact context_13_76966_162785
  · exact context_13_76967_162797

theorem selected_cut_05250 : selected 8 ⟨162819, by decide⟩
    (prefixPartial 13 76968) = some ⟨13, 2, 0, 162819, 76968, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_76968_162819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76968 ⟨162819, by decide⟩ :=
  accepted_of_selected 13 76968 ⟨162819, by decide⟩ ⟨13, 2, 0, 162819, 76968, 1441, 16384⟩
    (by decide) selected_cut_05250

theorem selected_cut_05251 : selected 8 ⟨162891, by decide⟩
    (prefixPartial 13 76969) = some ⟨13, 2, 0, 162891, 76969, 3133, 16384⟩ := by
  decide +kernel

theorem context_13_76969_162891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76969 ⟨162891, by decide⟩ :=
  accepted_of_selected 13 76969 ⟨162891, by decide⟩ ⟨13, 2, 0, 162891, 76969, 3133, 16384⟩
    (by decide) selected_cut_05251

theorem selected_cut_05252 : selected 8 ⟨162908, by decide⟩
    (prefixPartial 13 76970) = some ⟨13, 2, 0, 162908, 76970, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_76970_162908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76970 ⟨162908, by decide⟩ :=
  accepted_of_selected 13 76970 ⟨162908, by decide⟩ ⟨13, 2, 0, 162908, 76970, 1601, 16384⟩
    (by decide) selected_cut_05252

theorem selected_cut_05253 : selected 8 ⟨162915, by decide⟩
    (prefixPartial 13 76971) = some ⟨13, 2, 0, 162915, 76971, 989, 16384⟩ := by
  decide +kernel

theorem context_13_76971_162915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76971 ⟨162915, by decide⟩ :=
  accepted_of_selected 13 76971 ⟨162915, by decide⟩ ⟨13, 2, 0, 162915, 76971, 989, 16384⟩
    (by decide) selected_cut_05253

theorem unmarked_context_12_19242_162916 : frontier 9 ⟨162916, by decide⟩
    (prefixCache 12 19242) (prefixPartial 12 19242) = false := by
  decide +kernel

theorem node_context_12_19242_162916 : EJMOriginalGlobalDAGData.nodes 9 ⟨162916, by decide⟩ =
    .split (coordinate 12) (![⟨162819, by decide⟩,⟨162891, by decide⟩,⟨162908, by decide⟩,⟨162915, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19242_162916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19242 ⟨162916, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19242
    ⟨162916, by decide⟩ (by decide) (![⟨162819, by decide⟩,⟨162891, by decide⟩,⟨162908, by decide⟩,⟨162915, by decide⟩]) unmarked_context_12_19242_162916 node_context_12_19242_162916
  intro a
  fin_cases a
  · exact context_13_76968_162819
  · exact context_13_76969_162891
  · exact context_13_76970_162908
  · exact context_13_76971_162915

theorem selected_cut_05254 : selected 8 ⟨162935, by decide⟩
    (prefixPartial 13 76972) = some ⟨13, 2, 0, 162935, 76972, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_76972_162935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76972 ⟨162935, by decide⟩ :=
  accepted_of_selected 13 76972 ⟨162935, by decide⟩ ⟨13, 2, 0, 162935, 76972, 1241, 16384⟩
    (by decide) selected_cut_05254

theorem selected_cut_05255 : selected 8 ⟨163003, by decide⟩
    (prefixPartial 13 76973) = some ⟨13, 2, 0, 163003, 76973, 3117, 16384⟩ := by
  decide +kernel

theorem context_13_76973_163003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76973 ⟨163003, by decide⟩ :=
  accepted_of_selected 13 76973 ⟨163003, by decide⟩ ⟨13, 2, 0, 163003, 76973, 3117, 16384⟩
    (by decide) selected_cut_05255

theorem selected_cut_05256 : selected 8 ⟨163018, by decide⟩
    (prefixPartial 13 76974) = some ⟨13, 2, 0, 163018, 76974, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_76974_163018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76974 ⟨163018, by decide⟩ :=
  accepted_of_selected 13 76974 ⟨163018, by decide⟩ ⟨13, 2, 0, 163018, 76974, 1537, 16384⟩
    (by decide) selected_cut_05256

theorem selected_cut_05257 : selected 8 ⟨163033, by decide⟩
    (prefixPartial 13 76975) = some ⟨13, 2, 0, 163033, 76975, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_76975_163033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76975 ⟨163033, by decide⟩ :=
  accepted_of_selected 13 76975 ⟨163033, by decide⟩ ⟨13, 2, 0, 163033, 76975, 1025, 16384⟩
    (by decide) selected_cut_05257

theorem unmarked_context_12_19243_163034 : frontier 9 ⟨163034, by decide⟩
    (prefixCache 12 19243) (prefixPartial 12 19243) = false := by
  decide +kernel

theorem node_context_12_19243_163034 : EJMOriginalGlobalDAGData.nodes 9 ⟨163034, by decide⟩ =
    .split (coordinate 12) (![⟨162935, by decide⟩,⟨163003, by decide⟩,⟨163018, by decide⟩,⟨163033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19243_163034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19243 ⟨163034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19243
    ⟨163034, by decide⟩ (by decide) (![⟨162935, by decide⟩,⟨163003, by decide⟩,⟨163018, by decide⟩,⟨163033, by decide⟩]) unmarked_context_12_19243_163034 node_context_12_19243_163034
  intro a
  fin_cases a
  · exact context_13_76972_162935
  · exact context_13_76973_163003
  · exact context_13_76974_163018
  · exact context_13_76975_163033

theorem unmarked_context_11_4810_163035 : frontier 10 ⟨163035, by decide⟩
    (prefixCache 11 4810) (prefixPartial 11 4810) = false := by
  decide +kernel

theorem node_context_11_4810_163035 : EJMOriginalGlobalDAGData.nodes 10 ⟨163035, by decide⟩ =
    .split (coordinate 11) (![⟨162662, by decide⟩,⟨162798, by decide⟩,⟨162916, by decide⟩,⟨163034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4810_163035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4810 ⟨163035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4810
    ⟨163035, by decide⟩ (by decide) (![⟨162662, by decide⟩,⟨162798, by decide⟩,⟨162916, by decide⟩,⟨163034, by decide⟩]) unmarked_context_11_4810_163035 node_context_11_4810_163035
  intro a
  fin_cases a
  · exact context_12_19240_162662
  · exact context_12_19241_162798
  · exact context_12_19242_162916
  · exact context_12_19243_163034

theorem selected_cut_05258 : selected 8 ⟨163047, by decide⟩
    (prefixPartial 13 76976) = some ⟨13, 2, 0, 163047, 76976, 801, 16384⟩ := by
  decide +kernel

theorem context_13_76976_163047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76976 ⟨163047, by decide⟩ :=
  accepted_of_selected 13 76976 ⟨163047, by decide⟩ ⟨13, 2, 0, 163047, 76976, 801, 16384⟩
    (by decide) selected_cut_05258

theorem selected_cut_05259 : selected 8 ⟨163082, by decide⟩
    (prefixPartial 13 76977) = some ⟨13, 2, 0, 163082, 76977, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_76977_163082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76977 ⟨163082, by decide⟩ :=
  accepted_of_selected 13 76977 ⟨163082, by decide⟩ ⟨13, 2, 0, 163082, 76977, 2169, 16384⟩
    (by decide) selected_cut_05259

theorem selected_cut_05260 : selected 8 ⟨163095, by decide⟩
    (prefixPartial 13 76978) = some ⟨13, 2, 0, 163095, 76978, 1157, 16384⟩ := by
  decide +kernel

theorem context_13_76978_163095 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76978 ⟨163095, by decide⟩ :=
  accepted_of_selected 13 76978 ⟨163095, by decide⟩ ⟨13, 2, 0, 163095, 76978, 1157, 16384⟩
    (by decide) selected_cut_05260

theorem selected_cut_05261 : selected 8 ⟨163102, by decide⟩
    (prefixPartial 13 76979) = some ⟨13, 2, 0, 163102, 76979, 853, 16384⟩ := by
  decide +kernel

theorem context_13_76979_163102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76979 ⟨163102, by decide⟩ :=
  accepted_of_selected 13 76979 ⟨163102, by decide⟩ ⟨13, 2, 0, 163102, 76979, 853, 16384⟩
    (by decide) selected_cut_05261

theorem unmarked_context_12_19244_163103 : frontier 9 ⟨163103, by decide⟩
    (prefixCache 12 19244) (prefixPartial 12 19244) = false := by
  decide +kernel

theorem node_context_12_19244_163103 : EJMOriginalGlobalDAGData.nodes 9 ⟨163103, by decide⟩ =
    .split (coordinate 12) (![⟨163047, by decide⟩,⟨163082, by decide⟩,⟨163095, by decide⟩,⟨163102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19244_163103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19244 ⟨163103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19244
    ⟨163103, by decide⟩ (by decide) (![⟨163047, by decide⟩,⟨163082, by decide⟩,⟨163095, by decide⟩,⟨163102, by decide⟩]) unmarked_context_12_19244_163103 node_context_12_19244_163103
  intro a
  fin_cases a
  · exact context_13_76976_163047
  · exact context_13_76977_163082
  · exact context_13_76978_163095
  · exact context_13_76979_163102

theorem selected_cut_05262 : selected 8 ⟨163123, by decide⟩
    (prefixPartial 13 76980) = some ⟨13, 2, 0, 163123, 76980, 921, 16384⟩ := by
  decide +kernel

theorem context_13_76980_163123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76980 ⟨163123, by decide⟩ :=
  accepted_of_selected 13 76980 ⟨163123, by decide⟩ ⟨13, 2, 0, 163123, 76980, 921, 16384⟩
    (by decide) selected_cut_05262

theorem selected_cut_05263 : selected 8 ⟨163167, by decide⟩
    (prefixPartial 13 76981) = some ⟨13, 2, 0, 163167, 76981, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_76981_163167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76981 ⟨163167, by decide⟩ :=
  accepted_of_selected 13 76981 ⟨163167, by decide⟩ ⟨13, 2, 0, 163167, 76981, 2161, 16384⟩
    (by decide) selected_cut_05263

theorem selected_cut_05264 : selected 8 ⟨163183, by decide⟩
    (prefixPartial 13 76982) = some ⟨13, 2, 0, 163183, 76982, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_76982_163183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76982 ⟨163183, by decide⟩ :=
  accepted_of_selected 13 76982 ⟨163183, by decide⟩ ⟨13, 2, 0, 163183, 76982, 1329, 16384⟩
    (by decide) selected_cut_05264

theorem selected_cut_05265 : selected 8 ⟨163195, by decide⟩
    (prefixPartial 13 76983) = some ⟨13, 2, 0, 163195, 76983, 757, 16384⟩ := by
  decide +kernel

theorem context_13_76983_163195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76983 ⟨163195, by decide⟩ :=
  accepted_of_selected 13 76983 ⟨163195, by decide⟩ ⟨13, 2, 0, 163195, 76983, 757, 16384⟩
    (by decide) selected_cut_05265

theorem unmarked_context_12_19245_163196 : frontier 9 ⟨163196, by decide⟩
    (prefixCache 12 19245) (prefixPartial 12 19245) = false := by
  decide +kernel

theorem node_context_12_19245_163196 : EJMOriginalGlobalDAGData.nodes 9 ⟨163196, by decide⟩ =
    .split (coordinate 12) (![⟨163123, by decide⟩,⟨163167, by decide⟩,⟨163183, by decide⟩,⟨163195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19245_163196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19245 ⟨163196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19245
    ⟨163196, by decide⟩ (by decide) (![⟨163123, by decide⟩,⟨163167, by decide⟩,⟨163183, by decide⟩,⟨163195, by decide⟩]) unmarked_context_12_19245_163196 node_context_12_19245_163196
  intro a
  fin_cases a
  · exact context_13_76980_163123
  · exact context_13_76981_163167
  · exact context_13_76982_163183
  · exact context_13_76983_163195

theorem selected_cut_05266 : selected 8 ⟨163212, by decide⟩
    (prefixPartial 13 76984) = some ⟨13, 2, 0, 163212, 76984, 885, 16384⟩ := by
  decide +kernel

theorem context_13_76984_163212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76984 ⟨163212, by decide⟩ :=
  accepted_of_selected 13 76984 ⟨163212, by decide⟩ ⟨13, 2, 0, 163212, 76984, 885, 16384⟩
    (by decide) selected_cut_05266

theorem selected_cut_05267 : selected 8 ⟨163257, by decide⟩
    (prefixPartial 13 76985) = some ⟨13, 2, 0, 163257, 76985, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_76985_163257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76985 ⟨163257, by decide⟩ :=
  accepted_of_selected 13 76985 ⟨163257, by decide⟩ ⟨13, 2, 0, 163257, 76985, 2337, 16384⟩
    (by decide) selected_cut_05267

theorem selected_cut_05268 : selected 8 ⟨163273, by decide⟩
    (prefixPartial 13 76986) = some ⟨13, 2, 0, 163273, 76986, 1309, 16384⟩ := by
  decide +kernel

theorem context_13_76986_163273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76986 ⟨163273, by decide⟩ :=
  accepted_of_selected 13 76986 ⟨163273, by decide⟩ ⟨13, 2, 0, 163273, 76986, 1309, 16384⟩
    (by decide) selected_cut_05268

theorem selected_cut_05269 : selected 8 ⟨163285, by decide⟩
    (prefixPartial 13 76987) = some ⟨13, 2, 0, 163285, 76987, 837, 16384⟩ := by
  decide +kernel

theorem context_13_76987_163285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76987 ⟨163285, by decide⟩ :=
  accepted_of_selected 13 76987 ⟨163285, by decide⟩ ⟨13, 2, 0, 163285, 76987, 837, 16384⟩
    (by decide) selected_cut_05269

theorem unmarked_context_12_19246_163286 : frontier 9 ⟨163286, by decide⟩
    (prefixCache 12 19246) (prefixPartial 12 19246) = false := by
  decide +kernel

theorem node_context_12_19246_163286 : EJMOriginalGlobalDAGData.nodes 9 ⟨163286, by decide⟩ =
    .split (coordinate 12) (![⟨163212, by decide⟩,⟨163257, by decide⟩,⟨163273, by decide⟩,⟨163285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19246_163286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19246 ⟨163286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19246
    ⟨163286, by decide⟩ (by decide) (![⟨163212, by decide⟩,⟨163257, by decide⟩,⟨163273, by decide⟩,⟨163285, by decide⟩]) unmarked_context_12_19246_163286 node_context_12_19246_163286
  intro a
  fin_cases a
  · exact context_13_76984_163212
  · exact context_13_76985_163257
  · exact context_13_76986_163273
  · exact context_13_76987_163285

theorem selected_cut_05270 : selected 8 ⟨163301, by decide⟩
    (prefixPartial 13 76988) = some ⟨13, 2, 0, 163301, 76988, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_76988_163301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76988 ⟨163301, by decide⟩ :=
  accepted_of_selected 13 76988 ⟨163301, by decide⟩ ⟨13, 2, 0, 163301, 76988, 1037, 16384⟩
    (by decide) selected_cut_05270

theorem selected_cut_05271 : selected 8 ⟨163368, by decide⟩
    (prefixPartial 13 76989) = some ⟨13, 2, 0, 163368, 76989, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_76989_163368 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76989 ⟨163368, by decide⟩ :=
  accepted_of_selected 13 76989 ⟨163368, by decide⟩ ⟨13, 2, 0, 163368, 76989, 2969, 16384⟩
    (by decide) selected_cut_05271

theorem selected_cut_05272 : selected 8 ⟨163387, by decide⟩
    (prefixPartial 13 76990) = some ⟨13, 2, 0, 163387, 76990, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_76990_163387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76990 ⟨163387, by decide⟩ :=
  accepted_of_selected 13 76990 ⟨163387, by decide⟩ ⟨13, 2, 0, 163387, 76990, 1781, 16384⟩
    (by decide) selected_cut_05272

theorem selected_cut_05273 : selected 8 ⟨163399, by decide⟩
    (prefixPartial 13 76991) = some ⟨13, 2, 0, 163399, 76991, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_76991_163399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76991 ⟨163399, by decide⟩ :=
  accepted_of_selected 13 76991 ⟨163399, by decide⟩ ⟨13, 2, 0, 163399, 76991, 1049, 16384⟩
    (by decide) selected_cut_05273

theorem unmarked_context_12_19247_163400 : frontier 9 ⟨163400, by decide⟩
    (prefixCache 12 19247) (prefixPartial 12 19247) = false := by
  decide +kernel

theorem node_context_12_19247_163400 : EJMOriginalGlobalDAGData.nodes 9 ⟨163400, by decide⟩ =
    .split (coordinate 12) (![⟨163301, by decide⟩,⟨163368, by decide⟩,⟨163387, by decide⟩,⟨163399, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19247_163400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19247 ⟨163400, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19247
    ⟨163400, by decide⟩ (by decide) (![⟨163301, by decide⟩,⟨163368, by decide⟩,⟨163387, by decide⟩,⟨163399, by decide⟩]) unmarked_context_12_19247_163400 node_context_12_19247_163400
  intro a
  fin_cases a
  · exact context_13_76988_163301
  · exact context_13_76989_163368
  · exact context_13_76990_163387
  · exact context_13_76991_163399

theorem unmarked_context_11_4811_163401 : frontier 10 ⟨163401, by decide⟩
    (prefixCache 11 4811) (prefixPartial 11 4811) = false := by
  decide +kernel

theorem node_context_11_4811_163401 : EJMOriginalGlobalDAGData.nodes 10 ⟨163401, by decide⟩ =
    .split (coordinate 11) (![⟨163103, by decide⟩,⟨163196, by decide⟩,⟨163286, by decide⟩,⟨163400, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4811_163401 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4811 ⟨163401, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4811
    ⟨163401, by decide⟩ (by decide) (![⟨163103, by decide⟩,⟨163196, by decide⟩,⟨163286, by decide⟩,⟨163400, by decide⟩]) unmarked_context_11_4811_163401 node_context_11_4811_163401
  intro a
  fin_cases a
  · exact context_12_19244_163103
  · exact context_12_19245_163196
  · exact context_12_19246_163286
  · exact context_12_19247_163400

theorem unmarked_context_10_1202_163402 : frontier 11 ⟨163402, by decide⟩
    (prefixCache 10 1202) (prefixPartial 10 1202) = false := by
  decide +kernel

theorem node_context_10_1202_163402 : EJMOriginalGlobalDAGData.nodes 11 ⟨163402, by decide⟩ =
    .split (coordinate 10) (![⟨162127, by decide⟩,⟨162530, by decide⟩,⟨163035, by decide⟩,⟨163401, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1202_163402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1202 ⟨163402, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1202
    ⟨163402, by decide⟩ (by decide) (![⟨162127, by decide⟩,⟨162530, by decide⟩,⟨163035, by decide⟩,⟨163401, by decide⟩]) unmarked_context_10_1202_163402 node_context_10_1202_163402
  intro a
  fin_cases a
  · exact context_11_4808_162127
  · exact context_11_4809_162530
  · exact context_11_4810_163035
  · exact context_11_4811_163401

theorem selected_cut_05274 : selected 8 ⟨163415, by decide⟩
    (prefixPartial 13 76992) = some ⟨13, 2, 0, 163415, 76992, 665, 16384⟩ := by
  decide +kernel

theorem context_13_76992_163415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76992 ⟨163415, by decide⟩ :=
  accepted_of_selected 13 76992 ⟨163415, by decide⟩ ⟨13, 2, 0, 163415, 76992, 665, 16384⟩
    (by decide) selected_cut_05274

theorem selected_cut_05275 : selected 8 ⟨163454, by decide⟩
    (prefixPartial 13 76993) = some ⟨13, 2, 0, 163454, 76993, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_76993_163454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76993 ⟨163454, by decide⟩ :=
  accepted_of_selected 13 76993 ⟨163454, by decide⟩ ⟨13, 2, 0, 163454, 76993, 1865, 16384⟩
    (by decide) selected_cut_05275

theorem selected_cut_05276 : selected 8 ⟨163472, by decide⟩
    (prefixPartial 13 76994) = some ⟨13, 2, 0, 163472, 76994, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_76994_163472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76994 ⟨163472, by decide⟩ :=
  accepted_of_selected 13 76994 ⟨163472, by decide⟩ ⟨13, 2, 0, 163472, 76994, 1077, 16384⟩
    (by decide) selected_cut_05276

theorem selected_cut_05277 : selected 8 ⟨163477, by decide⟩
    (prefixPartial 13 76995) = some ⟨13, 2, 0, 163477, 76995, 801, 16384⟩ := by
  decide +kernel

theorem context_13_76995_163477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76995 ⟨163477, by decide⟩ :=
  accepted_of_selected 13 76995 ⟨163477, by decide⟩ ⟨13, 2, 0, 163477, 76995, 801, 16384⟩
    (by decide) selected_cut_05277

theorem unmarked_context_12_19248_163478 : frontier 9 ⟨163478, by decide⟩
    (prefixCache 12 19248) (prefixPartial 12 19248) = false := by
  decide +kernel

theorem node_context_12_19248_163478 : EJMOriginalGlobalDAGData.nodes 9 ⟨163478, by decide⟩ =
    .split (coordinate 12) (![⟨163415, by decide⟩,⟨163454, by decide⟩,⟨163472, by decide⟩,⟨163477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19248_163478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19248 ⟨163478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19248
    ⟨163478, by decide⟩ (by decide) (![⟨163415, by decide⟩,⟨163454, by decide⟩,⟨163472, by decide⟩,⟨163477, by decide⟩]) unmarked_context_12_19248_163478 node_context_12_19248_163478
  intro a
  fin_cases a
  · exact context_13_76992_163415
  · exact context_13_76993_163454
  · exact context_13_76994_163472
  · exact context_13_76995_163477

theorem selected_cut_05278 : selected 8 ⟨163490, by decide⟩
    (prefixPartial 13 76996) = some ⟨13, 2, 0, 163490, 76996, 617, 16384⟩ := by
  decide +kernel

theorem context_13_76996_163490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76996 ⟨163490, by decide⟩ :=
  accepted_of_selected 13 76996 ⟨163490, by decide⟩ ⟨13, 2, 0, 163490, 76996, 617, 16384⟩
    (by decide) selected_cut_05278

theorem selected_cut_05279 : selected 8 ⟨163535, by decide⟩
    (prefixPartial 13 76997) = some ⟨13, 2, 0, 163535, 76997, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_76997_163535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76997 ⟨163535, by decide⟩ :=
  accepted_of_selected 13 76997 ⟨163535, by decide⟩ ⟨13, 2, 0, 163535, 76997, 2001, 16384⟩
    (by decide) selected_cut_05279

theorem selected_cut_05280 : selected 8 ⟨163555, by decide⟩
    (prefixPartial 13 76998) = some ⟨13, 2, 0, 163555, 76998, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_76998_163555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76998 ⟨163555, by decide⟩ :=
  accepted_of_selected 13 76998 ⟨163555, by decide⟩ ⟨13, 2, 0, 163555, 76998, 1205, 16384⟩
    (by decide) selected_cut_05280

theorem selected_cut_05281 : selected 8 ⟨163560, by decide⟩
    (prefixPartial 13 76999) = some ⟨13, 2, 0, 163560, 76999, 601, 16384⟩ := by
  decide +kernel

theorem context_13_76999_163560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 76999 ⟨163560, by decide⟩ :=
  accepted_of_selected 13 76999 ⟨163560, by decide⟩ ⟨13, 2, 0, 163560, 76999, 601, 16384⟩
    (by decide) selected_cut_05281

theorem unmarked_context_12_19249_163561 : frontier 9 ⟨163561, by decide⟩
    (prefixCache 12 19249) (prefixPartial 12 19249) = false := by
  decide +kernel

theorem node_context_12_19249_163561 : EJMOriginalGlobalDAGData.nodes 9 ⟨163561, by decide⟩ =
    .split (coordinate 12) (![⟨163490, by decide⟩,⟨163535, by decide⟩,⟨163555, by decide⟩,⟨163560, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_19249_163561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 19249 ⟨163561, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 19249
    ⟨163561, by decide⟩ (by decide) (![⟨163490, by decide⟩,⟨163535, by decide⟩,⟨163555, by decide⟩,⟨163560, by decide⟩]) unmarked_context_12_19249_163561 node_context_12_19249_163561
  intro a
  fin_cases a
  · exact context_13_76996_163490
  · exact context_13_76997_163535
  · exact context_13_76998_163555
  · exact context_13_76999_163560

theorem selected_cut_05282 : selected 8 ⟨163567, by decide⟩
    (prefixPartial 13 77000) = some ⟨13, 2, 0, 163567, 77000, 569, 16384⟩ := by
  decide +kernel

theorem context_13_77000_163567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 77000 ⟨163567, by decide⟩ :=
  accepted_of_selected 13 77000 ⟨163567, by decide⟩ ⟨13, 2, 0, 163567, 77000, 569, 16384⟩
    (by decide) selected_cut_05282

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
