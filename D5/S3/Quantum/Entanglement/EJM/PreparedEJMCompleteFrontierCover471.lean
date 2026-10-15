/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover470
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_45220 : selected 9 ⟨402280, by decide⟩
    (prefixPartial 12 356149) = some ⟨12, 1, 0, 402280, 356149, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356149_402280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356149 ⟨402280, by decide⟩ :=
  accepted_of_selected 12 356149 ⟨402280, by decide⟩ ⟨12, 1, 0, 402280, 356149, 1, 65536⟩
    (by decide) selected_cut_45220

theorem selected_cut_45221 : selected 9 ⟨1250466, by decide⟩
    (prefixPartial 12 356150) = some ⟨12, 2, 0, 1250466, 356150, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_356150_1250466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356150 ⟨1250466, by decide⟩ :=
  accepted_of_selected 12 356150 ⟨1250466, by decide⟩ ⟨12, 2, 0, 1250466, 356150, 2261, 65536⟩
    (by decide) selected_cut_45221

theorem selected_cut_45222 : selected 9 ⟨1250514, by decide⟩
    (prefixPartial 12 356151) = some ⟨12, 2, 0, 1250514, 356151, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_356151_1250514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356151 ⟨1250514, by decide⟩ :=
  accepted_of_selected 12 356151 ⟨1250514, by decide⟩ ⟨12, 2, 0, 1250514, 356151, 2145, 65536⟩
    (by decide) selected_cut_45222

theorem unmarked_context_11_89037_1250515 : frontier 10 ⟨1250515, by decide⟩
    (prefixCache 11 89037) (prefixPartial 11 89037) = false := by
  decide +kernel

theorem node_context_11_89037_1250515 : EJMOriginalGlobalDAGData.nodes 10 ⟨1250515, by decide⟩ =
    .split (coordinate 11) (![⟨1250420, by decide⟩,⟨402280, by decide⟩,⟨1250466, by decide⟩,⟨1250514, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89037_1250515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89037 ⟨1250515, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89037
    ⟨1250515, by decide⟩ (by decide) (![⟨1250420, by decide⟩,⟨402280, by decide⟩,⟨1250466, by decide⟩,⟨1250514, by decide⟩]) unmarked_context_11_89037_1250515 node_context_11_89037_1250515
  intro a
  fin_cases a
  · exact context_12_356148_1250420
  · exact context_12_356149_402280
  · exact context_12_356150_1250466
  · exact context_12_356151_1250514

theorem selected_cut_45223 : selected 9 ⟨1250577, by decide⟩
    (prefixPartial 12 356152) = some ⟨12, 2, 0, 1250577, 356152, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_356152_1250577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356152 ⟨1250577, by decide⟩ :=
  accepted_of_selected 12 356152 ⟨1250577, by decide⟩ ⟨12, 2, 0, 1250577, 356152, 2449, 65536⟩
    (by decide) selected_cut_45223

theorem selected_cut_45224 : selected 9 ⟨1250626, by decide⟩
    (prefixPartial 12 356153) = some ⟨12, 2, 0, 1250626, 356153, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_356153_1250626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356153 ⟨1250626, by decide⟩ :=
  accepted_of_selected 12 356153 ⟨1250626, by decide⟩ ⟨12, 2, 0, 1250626, 356153, 2205, 65536⟩
    (by decide) selected_cut_45224

theorem selected_cut_45225 : selected 9 ⟨1250744, by decide⟩
    (prefixPartial 12 356154) = some ⟨12, 2, 0, 1250744, 356154, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_356154_1250744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356154 ⟨1250744, by decide⟩ :=
  accepted_of_selected 12 356154 ⟨1250744, by decide⟩ ⟨12, 2, 0, 1250744, 356154, 1293, 65536⟩
    (by decide) selected_cut_45225

theorem selected_cut_45226 : selected 9 ⟨1250789, by decide⟩
    (prefixPartial 12 356155) = some ⟨12, 2, 0, 1250789, 356155, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_356155_1250789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356155 ⟨1250789, by decide⟩ :=
  accepted_of_selected 12 356155 ⟨1250789, by decide⟩ ⟨12, 2, 0, 1250789, 356155, 2213, 65536⟩
    (by decide) selected_cut_45226

theorem unmarked_context_11_89038_1250790 : frontier 10 ⟨1250790, by decide⟩
    (prefixCache 11 89038) (prefixPartial 11 89038) = false := by
  decide +kernel

theorem node_context_11_89038_1250790 : EJMOriginalGlobalDAGData.nodes 10 ⟨1250790, by decide⟩ =
    .split (coordinate 11) (![⟨1250577, by decide⟩,⟨1250626, by decide⟩,⟨1250744, by decide⟩,⟨1250789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89038_1250790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89038 ⟨1250790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89038
    ⟨1250790, by decide⟩ (by decide) (![⟨1250577, by decide⟩,⟨1250626, by decide⟩,⟨1250744, by decide⟩,⟨1250789, by decide⟩]) unmarked_context_11_89038_1250790 node_context_11_89038_1250790
  intro a
  fin_cases a
  · exact context_12_356152_1250577
  · exact context_12_356153_1250626
  · exact context_12_356154_1250744
  · exact context_12_356155_1250789

theorem selected_cut_45227 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 89039) = some ⟨11, 1, 0, 977886, 89039, 1, 262144⟩ := by
  decide +kernel

theorem context_11_89039_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89039 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 89039 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 89039, 1, 262144⟩
    (by decide) selected_cut_45227

theorem unmarked_context_10_22259_1250791 : frontier 11 ⟨1250791, by decide⟩
    (prefixCache 10 22259) (prefixPartial 10 22259) = false := by
  decide +kernel

theorem node_context_10_22259_1250791 : EJMOriginalGlobalDAGData.nodes 11 ⟨1250791, by decide⟩ =
    .split (coordinate 10) (![⟨1250357, by decide⟩,⟨1250515, by decide⟩,⟨1250790, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22259_1250791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22259 ⟨1250791, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22259
    ⟨1250791, by decide⟩ (by decide) (![⟨1250357, by decide⟩,⟨1250515, by decide⟩,⟨1250790, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22259_1250791 node_context_10_22259_1250791
  intro a
  fin_cases a
  · exact context_11_89036_1250357
  · exact context_11_89037_1250515
  · exact context_11_89038_1250790
  · exact context_11_89039_977886

theorem unmarked_context_9_5564_1250792 : frontier 12 ⟨1250792, by decide⟩
    (prefixCache 9 5564) (prefixPartial 9 5564) = false := by
  decide +kernel

theorem node_context_9_5564_1250792 : EJMOriginalGlobalDAGData.nodes 12 ⟨1250792, by decide⟩ =
    .split (coordinate 9) (![⟨1248662, by decide⟩,⟨1249367, by decide⟩,⟨1250193, by decide⟩,⟨1250791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5564_1250792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5564 ⟨1250792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5564
    ⟨1250792, by decide⟩ (by decide) (![⟨1248662, by decide⟩,⟨1249367, by decide⟩,⟨1250193, by decide⟩,⟨1250791, by decide⟩]) unmarked_context_9_5564_1250792 node_context_9_5564_1250792
  intro a
  fin_cases a
  · exact context_10_22256_1248662
  · exact context_10_22257_1249367
  · exact context_10_22258_1250193
  · exact context_10_22259_1250791

theorem selected_cut_45228 : selected 10 ⟨1250831, by decide⟩
    (prefixPartial 11 89040) = some ⟨11, 2, 0, 1250831, 89040, 1849, 262144⟩ := by
  decide +kernel

theorem context_11_89040_1250831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89040 ⟨1250831, by decide⟩ :=
  accepted_of_selected 11 89040 ⟨1250831, by decide⟩ ⟨11, 2, 0, 1250831, 89040, 1849, 262144⟩
    (by decide) selected_cut_45228

theorem selected_cut_45229 : selected 9 ⟨1250866, by decide⟩
    (prefixPartial 12 356164) = some ⟨12, 2, 0, 1250866, 356164, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_356164_1250866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356164 ⟨1250866, by decide⟩ :=
  accepted_of_selected 12 356164 ⟨1250866, by decide⟩ ⟨12, 2, 0, 1250866, 356164, 1581, 65536⟩
    (by decide) selected_cut_45229

theorem selected_cut_45230 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 356165) = some ⟨12, 1, 0, 896706, 356165, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356165_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356165 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 356165 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 356165, 1, 65536⟩
    (by decide) selected_cut_45230

theorem selected_cut_45231 : selected 9 ⟨1250898, by decide⟩
    (prefixPartial 12 356166) = some ⟨12, 2, 0, 1250898, 356166, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_356166_1250898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356166 ⟨1250898, by decide⟩ :=
  accepted_of_selected 12 356166 ⟨1250898, by decide⟩ ⟨12, 2, 0, 1250898, 356166, 1405, 65536⟩
    (by decide) selected_cut_45231

theorem selected_cut_45232 : selected 9 ⟨1250929, by decide⟩
    (prefixPartial 12 356167) = some ⟨12, 2, 0, 1250929, 356167, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_356167_1250929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356167 ⟨1250929, by decide⟩ :=
  accepted_of_selected 12 356167 ⟨1250929, by decide⟩ ⟨12, 2, 0, 1250929, 356167, 1557, 65536⟩
    (by decide) selected_cut_45232

theorem unmarked_context_11_89041_1250930 : frontier 10 ⟨1250930, by decide⟩
    (prefixCache 11 89041) (prefixPartial 11 89041) = false := by
  decide +kernel

theorem node_context_11_89041_1250930 : EJMOriginalGlobalDAGData.nodes 10 ⟨1250930, by decide⟩ =
    .split (coordinate 11) (![⟨1250866, by decide⟩,⟨896706, by decide⟩,⟨1250898, by decide⟩,⟨1250929, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89041_1250930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89041 ⟨1250930, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89041
    ⟨1250930, by decide⟩ (by decide) (![⟨1250866, by decide⟩,⟨896706, by decide⟩,⟨1250898, by decide⟩,⟨1250929, by decide⟩]) unmarked_context_11_89041_1250930 node_context_11_89041_1250930
  intro a
  fin_cases a
  · exact context_12_356164_1250866
  · exact context_12_356165_896706
  · exact context_12_356166_1250898
  · exact context_12_356167_1250929

theorem selected_cut_45233 : selected 9 ⟨1250964, by decide⟩
    (prefixPartial 12 356168) = some ⟨12, 2, 0, 1250964, 356168, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_356168_1250964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356168 ⟨1250964, by decide⟩ :=
  accepted_of_selected 12 356168 ⟨1250964, by decide⟩ ⟨12, 2, 0, 1250964, 356168, 1693, 65536⟩
    (by decide) selected_cut_45233

theorem selected_cut_45234 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 356169) = some ⟨12, 1, 0, 896706, 356169, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356169_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356169 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 356169 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 356169, 1, 65536⟩
    (by decide) selected_cut_45234

theorem selected_cut_45235 : selected 9 ⟨1250995, by decide⟩
    (prefixPartial 12 356170) = some ⟨12, 2, 0, 1250995, 356170, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_356170_1250995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356170 ⟨1250995, by decide⟩ :=
  accepted_of_selected 12 356170 ⟨1250995, by decide⟩ ⟨12, 2, 0, 1250995, 356170, 1601, 65536⟩
    (by decide) selected_cut_45235

theorem selected_cut_45236 : selected 9 ⟨1251022, by decide⟩
    (prefixPartial 12 356171) = some ⟨12, 2, 0, 1251022, 356171, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_356171_1251022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356171 ⟨1251022, by decide⟩ :=
  accepted_of_selected 12 356171 ⟨1251022, by decide⟩ ⟨12, 2, 0, 1251022, 356171, 1601, 65536⟩
    (by decide) selected_cut_45236

theorem unmarked_context_11_89042_1251023 : frontier 10 ⟨1251023, by decide⟩
    (prefixCache 11 89042) (prefixPartial 11 89042) = false := by
  decide +kernel

theorem node_context_11_89042_1251023 : EJMOriginalGlobalDAGData.nodes 10 ⟨1251023, by decide⟩ =
    .split (coordinate 11) (![⟨1250964, by decide⟩,⟨896706, by decide⟩,⟨1250995, by decide⟩,⟨1251022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89042_1251023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89042 ⟨1251023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89042
    ⟨1251023, by decide⟩ (by decide) (![⟨1250964, by decide⟩,⟨896706, by decide⟩,⟨1250995, by decide⟩,⟨1251022, by decide⟩]) unmarked_context_11_89042_1251023 node_context_11_89042_1251023
  intro a
  fin_cases a
  · exact context_12_356168_1250964
  · exact context_12_356169_896706
  · exact context_12_356170_1250995
  · exact context_12_356171_1251022

theorem selected_cut_45237 : selected 10 ⟨1251080, by decide⟩
    (prefixPartial 11 89043) = some ⟨11, 2, 0, 1251080, 89043, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_89043_1251080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89043 ⟨1251080, by decide⟩ :=
  accepted_of_selected 11 89043 ⟨1251080, by decide⟩ ⟨11, 2, 0, 1251080, 89043, 2725, 262144⟩
    (by decide) selected_cut_45237

theorem unmarked_context_10_22260_1251081 : frontier 11 ⟨1251081, by decide⟩
    (prefixCache 10 22260) (prefixPartial 10 22260) = false := by
  decide +kernel

theorem node_context_10_22260_1251081 : EJMOriginalGlobalDAGData.nodes 11 ⟨1251081, by decide⟩ =
    .split (coordinate 10) (![⟨1250831, by decide⟩,⟨1250930, by decide⟩,⟨1251023, by decide⟩,⟨1251080, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22260_1251081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22260 ⟨1251081, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22260
    ⟨1251081, by decide⟩ (by decide) (![⟨1250831, by decide⟩,⟨1250930, by decide⟩,⟨1251023, by decide⟩,⟨1251080, by decide⟩]) unmarked_context_10_22260_1251081 node_context_10_22260_1251081
  intro a
  fin_cases a
  · exact context_11_89040_1250831
  · exact context_11_89041_1250930
  · exact context_11_89042_1251023
  · exact context_11_89043_1251080

theorem selected_cut_45238 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 22261) = some ⟨10, 1, 0, 893098, 22261, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_22261_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22261 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 22261 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 22261, 1, 1048576⟩
    (by decide) selected_cut_45238

theorem selected_cut_45239 : selected 9 ⟨1251108, by decide⟩
    (prefixPartial 12 356192) = some ⟨12, 2, 0, 1251108, 356192, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_356192_1251108 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356192 ⟨1251108, by decide⟩ :=
  accepted_of_selected 12 356192 ⟨1251108, by decide⟩ ⟨12, 2, 0, 1251108, 356192, 1433, 65536⟩
    (by decide) selected_cut_45239

theorem selected_cut_45240 : selected 9 ⟨896706, by decide⟩
    (prefixPartial 12 356193) = some ⟨12, 1, 0, 896706, 356193, 1, 65536⟩ := by
  decide +kernel

theorem context_12_356193_896706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356193 ⟨896706, by decide⟩ :=
  accepted_of_selected 12 356193 ⟨896706, by decide⟩ ⟨12, 1, 0, 896706, 356193, 1, 65536⟩
    (by decide) selected_cut_45240

theorem selected_cut_45241 : selected 9 ⟨1251138, by decide⟩
    (prefixPartial 12 356194) = some ⟨12, 2, 0, 1251138, 356194, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_356194_1251138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356194 ⟨1251138, by decide⟩ :=
  accepted_of_selected 12 356194 ⟨1251138, by decide⟩ ⟨12, 2, 0, 1251138, 356194, 1497, 65536⟩
    (by decide) selected_cut_45241

theorem selected_cut_45242 : selected 9 ⟨1251163, by decide⟩
    (prefixPartial 12 356195) = some ⟨12, 2, 0, 1251163, 356195, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_356195_1251163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356195 ⟨1251163, by decide⟩ :=
  accepted_of_selected 12 356195 ⟨1251163, by decide⟩ ⟨12, 2, 0, 1251163, 356195, 1493, 65536⟩
    (by decide) selected_cut_45242

theorem unmarked_context_11_89048_1251164 : frontier 10 ⟨1251164, by decide⟩
    (prefixCache 11 89048) (prefixPartial 11 89048) = false := by
  decide +kernel

theorem node_context_11_89048_1251164 : EJMOriginalGlobalDAGData.nodes 10 ⟨1251164, by decide⟩ =
    .split (coordinate 11) (![⟨1251108, by decide⟩,⟨896706, by decide⟩,⟨1251138, by decide⟩,⟨1251163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89048_1251164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89048 ⟨1251164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89048
    ⟨1251164, by decide⟩ (by decide) (![⟨1251108, by decide⟩,⟨896706, by decide⟩,⟨1251138, by decide⟩,⟨1251163, by decide⟩]) unmarked_context_11_89048_1251164 node_context_11_89048_1251164
  intro a
  fin_cases a
  · exact context_12_356192_1251108
  · exact context_12_356193_896706
  · exact context_12_356194_1251138
  · exact context_12_356195_1251163

theorem selected_cut_45243 : selected 10 ⟨1251232, by decide⟩
    (prefixPartial 11 89049) = some ⟨11, 2, 0, 1251232, 89049, 3605, 262144⟩ := by
  decide +kernel

theorem context_11_89049_1251232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89049 ⟨1251232, by decide⟩ :=
  accepted_of_selected 11 89049 ⟨1251232, by decide⟩ ⟨11, 2, 0, 1251232, 89049, 3605, 262144⟩
    (by decide) selected_cut_45243

theorem selected_cut_45244 : selected 10 ⟨1251257, by decide⟩
    (prefixPartial 11 89050) = some ⟨11, 2, 0, 1251257, 89050, 1253, 262144⟩ := by
  decide +kernel

theorem context_11_89050_1251257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89050 ⟨1251257, by decide⟩ :=
  accepted_of_selected 11 89050 ⟨1251257, by decide⟩ ⟨11, 2, 0, 1251257, 89050, 1253, 262144⟩
    (by decide) selected_cut_45244

theorem selected_cut_45245 : selected 10 ⟨1251306, by decide⟩
    (prefixPartial 11 89051) = some ⟨11, 2, 0, 1251306, 89051, 2305, 262144⟩ := by
  decide +kernel

theorem context_11_89051_1251306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89051 ⟨1251306, by decide⟩ :=
  accepted_of_selected 11 89051 ⟨1251306, by decide⟩ ⟨11, 2, 0, 1251306, 89051, 2305, 262144⟩
    (by decide) selected_cut_45245

theorem unmarked_context_10_22262_1251307 : frontier 11 ⟨1251307, by decide⟩
    (prefixCache 10 22262) (prefixPartial 10 22262) = false := by
  decide +kernel

theorem node_context_10_22262_1251307 : EJMOriginalGlobalDAGData.nodes 11 ⟨1251307, by decide⟩ =
    .split (coordinate 10) (![⟨1251164, by decide⟩,⟨1251232, by decide⟩,⟨1251257, by decide⟩,⟨1251306, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22262_1251307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22262 ⟨1251307, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22262
    ⟨1251307, by decide⟩ (by decide) (![⟨1251164, by decide⟩,⟨1251232, by decide⟩,⟨1251257, by decide⟩,⟨1251306, by decide⟩]) unmarked_context_10_22262_1251307 node_context_10_22262_1251307
  intro a
  fin_cases a
  · exact context_11_89048_1251164
  · exact context_11_89049_1251232
  · exact context_11_89050_1251257
  · exact context_11_89051_1251306

theorem selected_cut_45246 : selected 10 ⟨1251362, by decide⟩
    (prefixPartial 11 89052) = some ⟨11, 2, 0, 1251362, 89052, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_89052_1251362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89052 ⟨1251362, by decide⟩ :=
  accepted_of_selected 11 89052 ⟨1251362, by decide⟩ ⟨11, 2, 0, 1251362, 89052, 2725, 262144⟩
    (by decide) selected_cut_45246

theorem selected_cut_45247 : selected 10 ⟨1251429, by decide⟩
    (prefixPartial 11 89053) = some ⟨11, 2, 0, 1251429, 89053, 3321, 262144⟩ := by
  decide +kernel

theorem context_11_89053_1251429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89053 ⟨1251429, by decide⟩ :=
  accepted_of_selected 11 89053 ⟨1251429, by decide⟩ ⟨11, 2, 0, 1251429, 89053, 3321, 262144⟩
    (by decide) selected_cut_45247

theorem selected_cut_45248 : selected 10 ⟨1251475, by decide⟩
    (prefixPartial 11 89054) = some ⟨11, 2, 0, 1251475, 89054, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_89054_1251475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89054 ⟨1251475, by decide⟩ :=
  accepted_of_selected 11 89054 ⟨1251475, by decide⟩ ⟨11, 2, 0, 1251475, 89054, 2193, 262144⟩
    (by decide) selected_cut_45248

theorem selected_cut_45249 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 89055) = some ⟨11, 1, 0, 977886, 89055, 1, 262144⟩ := by
  decide +kernel

theorem context_11_89055_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89055 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 89055 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 89055, 1, 262144⟩
    (by decide) selected_cut_45249

theorem unmarked_context_10_22263_1251476 : frontier 11 ⟨1251476, by decide⟩
    (prefixCache 10 22263) (prefixPartial 10 22263) = false := by
  decide +kernel

theorem node_context_10_22263_1251476 : EJMOriginalGlobalDAGData.nodes 11 ⟨1251476, by decide⟩ =
    .split (coordinate 10) (![⟨1251362, by decide⟩,⟨1251429, by decide⟩,⟨1251475, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22263_1251476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22263 ⟨1251476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22263
    ⟨1251476, by decide⟩ (by decide) (![⟨1251362, by decide⟩,⟨1251429, by decide⟩,⟨1251475, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22263_1251476 node_context_10_22263_1251476
  intro a
  fin_cases a
  · exact context_11_89052_1251362
  · exact context_11_89053_1251429
  · exact context_11_89054_1251475
  · exact context_11_89055_977886

theorem unmarked_context_9_5565_1251477 : frontier 12 ⟨1251477, by decide⟩
    (prefixCache 9 5565) (prefixPartial 9 5565) = false := by
  decide +kernel

theorem node_context_9_5565_1251477 : EJMOriginalGlobalDAGData.nodes 12 ⟨1251477, by decide⟩ =
    .split (coordinate 9) (![⟨1251081, by decide⟩,⟨893098, by decide⟩,⟨1251307, by decide⟩,⟨1251476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5565_1251477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5565 ⟨1251477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5565
    ⟨1251477, by decide⟩ (by decide) (![⟨1251081, by decide⟩,⟨893098, by decide⟩,⟨1251307, by decide⟩,⟨1251476, by decide⟩]) unmarked_context_9_5565_1251477 node_context_9_5565_1251477
  intro a
  fin_cases a
  · exact context_10_22260_1251081
  · exact context_10_22261_893098
  · exact context_10_22262_1251307
  · exact context_10_22263_1251476

theorem selected_cut_45250 : selected 10 ⟨1251567, by decide⟩
    (prefixPartial 11 89056) = some ⟨11, 2, 0, 1251567, 89056, 2709, 262144⟩ := by
  decide +kernel

theorem context_11_89056_1251567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89056 ⟨1251567, by decide⟩ :=
  accepted_of_selected 11 89056 ⟨1251567, by decide⟩ ⟨11, 2, 0, 1251567, 89056, 2709, 262144⟩
    (by decide) selected_cut_45250

theorem selected_cut_45251 : selected 9 ⟨1251591, by decide⟩
    (prefixPartial 12 356228) = some ⟨12, 2, 0, 1251591, 356228, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_356228_1251591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356228 ⟨1251591, by decide⟩ :=
  accepted_of_selected 12 356228 ⟨1251591, by decide⟩ ⟨12, 2, 0, 1251591, 356228, 1193, 65536⟩
    (by decide) selected_cut_45251

theorem selected_cut_45252 : selected 9 ⟨1251610, by decide⟩
    (prefixPartial 12 356229) = some ⟨12, 2, 0, 1251610, 356229, 997, 65536⟩ := by
  decide +kernel

theorem context_12_356229_1251610 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356229 ⟨1251610, by decide⟩ :=
  accepted_of_selected 12 356229 ⟨1251610, by decide⟩ ⟨12, 2, 0, 1251610, 356229, 997, 65536⟩
    (by decide) selected_cut_45252

theorem selected_cut_45253 : selected 9 ⟨1251632, by decide⟩
    (prefixPartial 12 356230) = some ⟨12, 2, 0, 1251632, 356230, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_356230_1251632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356230 ⟨1251632, by decide⟩ :=
  accepted_of_selected 12 356230 ⟨1251632, by decide⟩ ⟨12, 2, 0, 1251632, 356230, 1077, 65536⟩
    (by decide) selected_cut_45253

theorem selected_cut_45254 : selected 9 ⟨1251655, by decide⟩
    (prefixPartial 12 356231) = some ⟨12, 2, 0, 1251655, 356231, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_356231_1251655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 356231 ⟨1251655, by decide⟩ :=
  accepted_of_selected 12 356231 ⟨1251655, by decide⟩ ⟨12, 2, 0, 1251655, 356231, 1193, 65536⟩
    (by decide) selected_cut_45254

theorem unmarked_context_11_89057_1251656 : frontier 10 ⟨1251656, by decide⟩
    (prefixCache 11 89057) (prefixPartial 11 89057) = false := by
  decide +kernel

theorem node_context_11_89057_1251656 : EJMOriginalGlobalDAGData.nodes 10 ⟨1251656, by decide⟩ =
    .split (coordinate 11) (![⟨1251591, by decide⟩,⟨1251610, by decide⟩,⟨1251632, by decide⟩,⟨1251655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_89057_1251656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89057 ⟨1251656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 89057
    ⟨1251656, by decide⟩ (by decide) (![⟨1251591, by decide⟩,⟨1251610, by decide⟩,⟨1251632, by decide⟩,⟨1251655, by decide⟩]) unmarked_context_11_89057_1251656 node_context_11_89057_1251656
  intro a
  fin_cases a
  · exact context_12_356228_1251591
  · exact context_12_356229_1251610
  · exact context_12_356230_1251632
  · exact context_12_356231_1251655

theorem selected_cut_45255 : selected 10 ⟨1251739, by decide⟩
    (prefixPartial 11 89058) = some ⟨11, 2, 0, 1251739, 89058, 3509, 262144⟩ := by
  decide +kernel

theorem context_11_89058_1251739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89058 ⟨1251739, by decide⟩ :=
  accepted_of_selected 11 89058 ⟨1251739, by decide⟩ ⟨11, 2, 0, 1251739, 89058, 3509, 262144⟩
    (by decide) selected_cut_45255

theorem selected_cut_45256 : selected 10 ⟨1251794, by decide⟩
    (prefixPartial 11 89059) = some ⟨11, 2, 0, 1251794, 89059, 2765, 262144⟩ := by
  decide +kernel

theorem context_11_89059_1251794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89059 ⟨1251794, by decide⟩ :=
  accepted_of_selected 11 89059 ⟨1251794, by decide⟩ ⟨11, 2, 0, 1251794, 89059, 2765, 262144⟩
    (by decide) selected_cut_45256

theorem unmarked_context_10_22264_1251795 : frontier 11 ⟨1251795, by decide⟩
    (prefixCache 10 22264) (prefixPartial 10 22264) = false := by
  decide +kernel

theorem node_context_10_22264_1251795 : EJMOriginalGlobalDAGData.nodes 11 ⟨1251795, by decide⟩ =
    .split (coordinate 10) (![⟨1251567, by decide⟩,⟨1251656, by decide⟩,⟨1251739, by decide⟩,⟨1251794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22264_1251795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22264 ⟨1251795, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22264
    ⟨1251795, by decide⟩ (by decide) (![⟨1251567, by decide⟩,⟨1251656, by decide⟩,⟨1251739, by decide⟩,⟨1251794, by decide⟩]) unmarked_context_10_22264_1251795 node_context_10_22264_1251795
  intro a
  fin_cases a
  · exact context_11_89056_1251567
  · exact context_11_89057_1251656
  · exact context_11_89058_1251739
  · exact context_11_89059_1251794

theorem selected_cut_45257 : selected 10 ⟨1251862, by decide⟩
    (prefixPartial 11 89060) = some ⟨11, 2, 0, 1251862, 89060, 3129, 262144⟩ := by
  decide +kernel

theorem context_11_89060_1251862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89060 ⟨1251862, by decide⟩ :=
  accepted_of_selected 11 89060 ⟨1251862, by decide⟩ ⟨11, 2, 0, 1251862, 89060, 3129, 262144⟩
    (by decide) selected_cut_45257

theorem selected_cut_45258 : selected 10 ⟨1251886, by decide⟩
    (prefixPartial 11 89061) = some ⟨11, 2, 0, 1251886, 89061, 953, 262144⟩ := by
  decide +kernel

theorem context_11_89061_1251886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89061 ⟨1251886, by decide⟩ :=
  accepted_of_selected 11 89061 ⟨1251886, by decide⟩ ⟨11, 2, 0, 1251886, 89061, 953, 262144⟩
    (by decide) selected_cut_45258

theorem selected_cut_45259 : selected 10 ⟨1251939, by decide⟩
    (prefixPartial 11 89062) = some ⟨11, 2, 0, 1251939, 89062, 2649, 262144⟩ := by
  decide +kernel

theorem context_11_89062_1251939 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89062 ⟨1251939, by decide⟩ :=
  accepted_of_selected 11 89062 ⟨1251939, by decide⟩ ⟨11, 2, 0, 1251939, 89062, 2649, 262144⟩
    (by decide) selected_cut_45259

theorem selected_cut_45260 : selected 10 ⟨1251971, by decide⟩
    (prefixPartial 11 89063) = some ⟨11, 2, 0, 1251971, 89063, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_89063_1251971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89063 ⟨1251971, by decide⟩ :=
  accepted_of_selected 11 89063 ⟨1251971, by decide⟩ ⟨11, 2, 0, 1251971, 89063, 1517, 262144⟩
    (by decide) selected_cut_45260

theorem unmarked_context_10_22265_1251972 : frontier 11 ⟨1251972, by decide⟩
    (prefixCache 10 22265) (prefixPartial 10 22265) = false := by
  decide +kernel

theorem node_context_10_22265_1251972 : EJMOriginalGlobalDAGData.nodes 11 ⟨1251972, by decide⟩ =
    .split (coordinate 10) (![⟨1251862, by decide⟩,⟨1251886, by decide⟩,⟨1251939, by decide⟩,⟨1251971, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22265_1251972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22265 ⟨1251972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22265
    ⟨1251972, by decide⟩ (by decide) (![⟨1251862, by decide⟩,⟨1251886, by decide⟩,⟨1251939, by decide⟩,⟨1251971, by decide⟩]) unmarked_context_10_22265_1251972 node_context_10_22265_1251972
  intro a
  fin_cases a
  · exact context_11_89060_1251862
  · exact context_11_89061_1251886
  · exact context_11_89062_1251939
  · exact context_11_89063_1251971

theorem selected_cut_45261 : selected 11 ⟨1252040, by decide⟩
    (prefixPartial 10 22266) = some ⟨10, 2, 0, 1252040, 22266, 3249, 1048576⟩ := by
  decide +kernel

theorem context_10_22266_1252040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22266 ⟨1252040, by decide⟩ :=
  accepted_of_selected 10 22266 ⟨1252040, by decide⟩ ⟨10, 2, 0, 1252040, 22266, 3249, 1048576⟩
    (by decide) selected_cut_45261

theorem selected_cut_45262 : selected 10 ⟨1252092, by decide⟩
    (prefixPartial 11 89068) = some ⟨11, 2, 0, 1252092, 89068, 1993, 262144⟩ := by
  decide +kernel

theorem context_11_89068_1252092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89068 ⟨1252092, by decide⟩ :=
  accepted_of_selected 11 89068 ⟨1252092, by decide⟩ ⟨11, 2, 0, 1252092, 89068, 1993, 262144⟩
    (by decide) selected_cut_45262

theorem selected_cut_45263 : selected 10 ⟨1252120, by decide⟩
    (prefixPartial 11 89069) = some ⟨11, 2, 0, 1252120, 89069, 1449, 262144⟩ := by
  decide +kernel

theorem context_11_89069_1252120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89069 ⟨1252120, by decide⟩ :=
  accepted_of_selected 11 89069 ⟨1252120, by decide⟩ ⟨11, 2, 0, 1252120, 89069, 1449, 262144⟩
    (by decide) selected_cut_45263

theorem selected_cut_45264 : selected 10 ⟨1252152, by decide⟩
    (prefixPartial 11 89070) = some ⟨11, 2, 0, 1252152, 89070, 1465, 262144⟩ := by
  decide +kernel

theorem context_11_89070_1252152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89070 ⟨1252152, by decide⟩ :=
  accepted_of_selected 11 89070 ⟨1252152, by decide⟩ ⟨11, 2, 0, 1252152, 89070, 1465, 262144⟩
    (by decide) selected_cut_45264

theorem selected_cut_45265 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 89071) = some ⟨11, 1, 0, 977886, 89071, 1, 262144⟩ := by
  decide +kernel

theorem context_11_89071_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 89071 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 89071 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 89071, 1, 262144⟩
    (by decide) selected_cut_45265

theorem unmarked_context_10_22267_1252153 : frontier 11 ⟨1252153, by decide⟩
    (prefixCache 10 22267) (prefixPartial 10 22267) = false := by
  decide +kernel

theorem node_context_10_22267_1252153 : EJMOriginalGlobalDAGData.nodes 11 ⟨1252153, by decide⟩ =
    .split (coordinate 10) (![⟨1252092, by decide⟩,⟨1252120, by decide⟩,⟨1252152, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22267_1252153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22267 ⟨1252153, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22267
    ⟨1252153, by decide⟩ (by decide) (![⟨1252092, by decide⟩,⟨1252120, by decide⟩,⟨1252152, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_22267_1252153 node_context_10_22267_1252153
  intro a
  fin_cases a
  · exact context_11_89068_1252092
  · exact context_11_89069_1252120
  · exact context_11_89070_1252152
  · exact context_11_89071_977886

theorem unmarked_context_9_5566_1252154 : frontier 12 ⟨1252154, by decide⟩
    (prefixCache 9 5566) (prefixPartial 9 5566) = false := by
  decide +kernel

theorem node_context_9_5566_1252154 : EJMOriginalGlobalDAGData.nodes 12 ⟨1252154, by decide⟩ =
    .split (coordinate 9) (![⟨1251795, by decide⟩,⟨1251972, by decide⟩,⟨1252040, by decide⟩,⟨1252153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5566_1252154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5566 ⟨1252154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5566
    ⟨1252154, by decide⟩ (by decide) (![⟨1251795, by decide⟩,⟨1251972, by decide⟩,⟨1252040, by decide⟩,⟨1252153, by decide⟩]) unmarked_context_9_5566_1252154 node_context_9_5566_1252154
  intro a
  fin_cases a
  · exact context_10_22264_1251795
  · exact context_10_22265_1251972
  · exact context_10_22266_1252040
  · exact context_10_22267_1252153

theorem selected_cut_45266 : selected 11 ⟨1252210, by decide⟩
    (prefixPartial 10 22268) = some ⟨10, 2, 0, 1252210, 22268, 3309, 1048576⟩ := by
  decide +kernel

theorem context_10_22268_1252210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22268 ⟨1252210, by decide⟩ :=
  accepted_of_selected 10 22268 ⟨1252210, by decide⟩ ⟨10, 2, 0, 1252210, 22268, 3309, 1048576⟩
    (by decide) selected_cut_45266

theorem selected_cut_45267 : selected 11 ⟨1252250, by decide⟩
    (prefixPartial 10 22269) = some ⟨10, 2, 0, 1252250, 22269, 1793, 1048576⟩ := by
  decide +kernel

theorem context_10_22269_1252250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22269 ⟨1252250, by decide⟩ :=
  accepted_of_selected 10 22269 ⟨1252250, by decide⟩ ⟨10, 2, 0, 1252250, 22269, 1793, 1048576⟩
    (by decide) selected_cut_45267

theorem selected_cut_45268 : selected 11 ⟨1252288, by decide⟩
    (prefixPartial 10 22270) = some ⟨10, 2, 0, 1252288, 22270, 1185, 1048576⟩ := by
  decide +kernel

theorem context_10_22270_1252288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22270 ⟨1252288, by decide⟩ :=
  accepted_of_selected 10 22270 ⟨1252288, by decide⟩ ⟨10, 2, 0, 1252288, 22270, 1185, 1048576⟩
    (by decide) selected_cut_45268

theorem selected_cut_45269 : selected 11 ⟨1252297, by decide⟩
    (prefixPartial 10 22271) = some ⟨10, 2, 0, 1252297, 22271, 85, 1048576⟩ := by
  decide +kernel

theorem context_10_22271_1252297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22271 ⟨1252297, by decide⟩ :=
  accepted_of_selected 10 22271 ⟨1252297, by decide⟩ ⟨10, 2, 0, 1252297, 22271, 85, 1048576⟩
    (by decide) selected_cut_45269

theorem unmarked_context_9_5567_1252298 : frontier 12 ⟨1252298, by decide⟩
    (prefixCache 9 5567) (prefixPartial 9 5567) = false := by
  decide +kernel

theorem node_context_9_5567_1252298 : EJMOriginalGlobalDAGData.nodes 12 ⟨1252298, by decide⟩ =
    .split (coordinate 9) (![⟨1252210, by decide⟩,⟨1252250, by decide⟩,⟨1252288, by decide⟩,⟨1252297, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5567_1252298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5567 ⟨1252298, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5567
    ⟨1252298, by decide⟩ (by decide) (![⟨1252210, by decide⟩,⟨1252250, by decide⟩,⟨1252288, by decide⟩,⟨1252297, by decide⟩]) unmarked_context_9_5567_1252298 node_context_9_5567_1252298
  intro a
  fin_cases a
  · exact context_10_22268_1252210
  · exact context_10_22269_1252250
  · exact context_10_22270_1252288
  · exact context_10_22271_1252297

theorem unmarked_context_8_1391_1252299 : frontier 13 ⟨1252299, by decide⟩
    (prefixCache 8 1391) (prefixPartial 8 1391) = false := by
  decide +kernel

theorem node_context_8_1391_1252299 : EJMOriginalGlobalDAGData.nodes 13 ⟨1252299, by decide⟩ =
    .split (coordinate 8) (![⟨1250792, by decide⟩,⟨1251477, by decide⟩,⟨1252154, by decide⟩,⟨1252298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1391_1252299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1391 ⟨1252299, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1391
    ⟨1252299, by decide⟩ (by decide) (![⟨1250792, by decide⟩,⟨1251477, by decide⟩,⟨1252154, by decide⟩,⟨1252298, by decide⟩]) unmarked_context_8_1391_1252299 node_context_8_1391_1252299
  intro a
  fin_cases a
  · exact context_9_5564_1250792
  · exact context_9_5565_1251477
  · exact context_9_5566_1252154
  · exact context_9_5567_1252298

theorem unmarked_context_7_347_1252300 : frontier 14 ⟨1252300, by decide⟩
    (prefixCache 7 347) (prefixPartial 7 347) = false := by
  decide +kernel

theorem node_context_7_347_1252300 : EJMOriginalGlobalDAGData.nodes 14 ⟨1252300, by decide⟩ =
    .split (coordinate 7) (![⟨1241359, by decide⟩,⟨1244604, by decide⟩,⟨1248184, by decide⟩,⟨1252299, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_347_1252300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 347 ⟨1252300, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 347
    ⟨1252300, by decide⟩ (by decide) (![⟨1241359, by decide⟩,⟨1244604, by decide⟩,⟨1248184, by decide⟩,⟨1252299, by decide⟩]) unmarked_context_7_347_1252300 node_context_7_347_1252300
  intro a
  fin_cases a
  · exact context_8_1388_1241359
  · exact context_8_1389_1244604
  · exact context_8_1390_1248184
  · exact context_8_1391_1252299

theorem unmarked_context_6_86_1252301 : frontier 15 ⟨1252301, by decide⟩
    (prefixCache 6 86) (prefixPartial 6 86) = false := by
  decide +kernel

theorem node_context_6_86_1252301 : EJMOriginalGlobalDAGData.nodes 15 ⟨1252301, by decide⟩ =
    .split (coordinate 6) (![⟨1210391, by decide⟩,⟨1223893, by decide⟩,⟨1236922, by decide⟩,⟨1252300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_86_1252301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 86 ⟨1252301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 86
    ⟨1252301, by decide⟩ (by decide) (![⟨1210391, by decide⟩,⟨1223893, by decide⟩,⟨1236922, by decide⟩,⟨1252300, by decide⟩]) unmarked_context_6_86_1252301 node_context_6_86_1252301
  intro a
  fin_cases a
  · exact context_7_344_1210391
  · exact context_7_345_1223893
  · exact context_7_346_1236922
  · exact context_7_347_1252300

theorem selected_cut_45270 : selected 15 ⟨116314, by decide⟩
    (prefixPartial 6 87) = some ⟨6, 1, 0, 116314, 87, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_87_116314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 87 ⟨116314, by decide⟩ :=
  accepted_of_selected 6 87 ⟨116314, by decide⟩ ⟨6, 1, 0, 116314, 87, 1, 268435456⟩
    (by decide) selected_cut_45270

theorem unmarked_context_5_21_1252302 : frontier 16 ⟨1252302, by decide⟩
    (prefixCache 5 21) (prefixPartial 5 21) = false := by
  decide +kernel

theorem node_context_5_21_1252302 : EJMOriginalGlobalDAGData.nodes 16 ⟨1252302, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨1196754, by decide⟩,⟨1252301, by decide⟩,⟨116314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_21_1252302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 21 ⟨1252302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 21
    ⟨1252302, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨1196754, by decide⟩,⟨1252301, by decide⟩,⟨116314, by decide⟩]) unmarked_context_5_21_1252302 node_context_5_21_1252302
  intro a
  fin_cases a
  · exact context_6_84_434744
  · exact context_6_85_1196754
  · exact context_6_86_1252301
  · exact context_6_87_116314

theorem selected_cut_45271 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 88) = some ⟨6, 1, 0, 434744, 88, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_88_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 88 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 88 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 88, 1, 268435456⟩
    (by decide) selected_cut_45271

theorem selected_cut_45272 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 356) = some ⟨7, 1, 0, 116316, 356, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_356_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 356 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 356 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 356, 1, 67108864⟩
    (by decide) selected_cut_45272

theorem selected_cut_45273 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 357) = some ⟨7, 1, 0, 116316, 357, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_357_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 357 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 357 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 357, 1, 67108864⟩
    (by decide) selected_cut_45273

theorem selected_cut_45274 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 91648) = some ⟨11, 1, 0, 434745, 91648, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91648_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91648 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 91648 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 91648, 1, 262144⟩
    (by decide) selected_cut_45274

theorem selected_cut_45275 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 366596) = some ⟨12, 1, 0, 895, 366596, 1, 65536⟩ := by
  decide +kernel

theorem context_12_366596_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366596 ⟨895, by decide⟩ :=
  accepted_of_selected 12 366596 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 366596, 1, 65536⟩
    (by decide) selected_cut_45275

theorem selected_cut_45276 : selected 9 ⟨1252403, by decide⟩
    (prefixPartial 12 366597) = some ⟨12, 2, 0, 1252403, 366597, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_366597_1252403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366597 ⟨1252403, by decide⟩ :=
  accepted_of_selected 12 366597 ⟨1252403, by decide⟩ ⟨12, 2, 0, 1252403, 366597, 1785, 65536⟩
    (by decide) selected_cut_45276

theorem selected_cut_45277 : selected 9 ⟨1252492, by decide⟩
    (prefixPartial 12 366598) = some ⟨12, 2, 0, 1252492, 366598, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_366598_1252492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366598 ⟨1252492, by decide⟩ :=
  accepted_of_selected 12 366598 ⟨1252492, by decide⟩ ⟨12, 2, 0, 1252492, 366598, 3585, 65536⟩
    (by decide) selected_cut_45277

theorem selected_cut_45278 : selected 9 ⟨1252580, by decide⟩
    (prefixPartial 12 366599) = some ⟨12, 2, 0, 1252580, 366599, 3733, 65536⟩ := by
  decide +kernel

theorem context_12_366599_1252580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366599 ⟨1252580, by decide⟩ :=
  accepted_of_selected 12 366599 ⟨1252580, by decide⟩ ⟨12, 2, 0, 1252580, 366599, 3733, 65536⟩
    (by decide) selected_cut_45278

theorem unmarked_context_11_91649_1252581 : frontier 10 ⟨1252581, by decide⟩
    (prefixCache 11 91649) (prefixPartial 11 91649) = false := by
  decide +kernel

theorem node_context_11_91649_1252581 : EJMOriginalGlobalDAGData.nodes 10 ⟨1252581, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨1252403, by decide⟩,⟨1252492, by decide⟩,⟨1252580, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91649_1252581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91649 ⟨1252581, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91649
    ⟨1252581, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨1252403, by decide⟩,⟨1252492, by decide⟩,⟨1252580, by decide⟩]) unmarked_context_11_91649_1252581 node_context_11_91649_1252581
  intro a
  fin_cases a
  · exact context_12_366596_895
  · exact context_12_366597_1252403
  · exact context_12_366598_1252492
  · exact context_12_366599_1252580

theorem selected_cut_45279 : selected 10 ⟨1252660, by decide⟩
    (prefixPartial 11 91650) = some ⟨11, 2, 0, 1252660, 91650, 3613, 262144⟩ := by
  decide +kernel

theorem context_11_91650_1252660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91650 ⟨1252660, by decide⟩ :=
  accepted_of_selected 11 91650 ⟨1252660, by decide⟩ ⟨11, 2, 0, 1252660, 91650, 3613, 262144⟩
    (by decide) selected_cut_45279

theorem selected_cut_45280 : selected 10 ⟨1252724, by decide⟩
    (prefixPartial 11 91651) = some ⟨11, 2, 0, 1252724, 91651, 1889, 262144⟩ := by
  decide +kernel

theorem context_11_91651_1252724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91651 ⟨1252724, by decide⟩ :=
  accepted_of_selected 11 91651 ⟨1252724, by decide⟩ ⟨11, 2, 0, 1252724, 91651, 1889, 262144⟩
    (by decide) selected_cut_45280

theorem unmarked_context_10_22912_1252725 : frontier 11 ⟨1252725, by decide⟩
    (prefixCache 10 22912) (prefixPartial 10 22912) = false := by
  decide +kernel

theorem node_context_10_22912_1252725 : EJMOriginalGlobalDAGData.nodes 11 ⟨1252725, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1252581, by decide⟩,⟨1252660, by decide⟩,⟨1252724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22912_1252725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22912 ⟨1252725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22912
    ⟨1252725, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1252581, by decide⟩,⟨1252660, by decide⟩,⟨1252724, by decide⟩]) unmarked_context_10_22912_1252725 node_context_10_22912_1252725
  intro a
  fin_cases a
  · exact context_11_91648_434745
  · exact context_11_91649_1252581
  · exact context_11_91650_1252660
  · exact context_11_91651_1252724

theorem selected_cut_45281 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 366608) = some ⟨12, 1, 0, 985390, 366608, 1, 65536⟩ := by
  decide +kernel

theorem context_12_366608_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366608 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 366608 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 366608, 1, 65536⟩
    (by decide) selected_cut_45281

theorem selected_cut_45282 : selected 9 ⟨1252784, by decide⟩
    (prefixPartial 12 366609) = some ⟨12, 2, 0, 1252784, 366609, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_366609_1252784 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366609 ⟨1252784, by decide⟩ :=
  accepted_of_selected 12 366609 ⟨1252784, by decide⟩ ⟨12, 2, 0, 1252784, 366609, 1933, 65536⟩
    (by decide) selected_cut_45282

theorem selected_cut_45283 : selected 9 ⟨1252845, by decide⟩
    (prefixPartial 12 366610) = some ⟨12, 2, 0, 1252845, 366610, 2565, 65536⟩ := by
  decide +kernel

theorem context_12_366610_1252845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366610 ⟨1252845, by decide⟩ :=
  accepted_of_selected 12 366610 ⟨1252845, by decide⟩ ⟨12, 2, 0, 1252845, 366610, 2565, 65536⟩
    (by decide) selected_cut_45283

theorem selected_cut_45284 : selected 9 ⟨1252903, by decide⟩
    (prefixPartial 12 366611) = some ⟨12, 2, 0, 1252903, 366611, 2757, 65536⟩ := by
  decide +kernel

theorem context_12_366611_1252903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366611 ⟨1252903, by decide⟩ :=
  accepted_of_selected 12 366611 ⟨1252903, by decide⟩ ⟨12, 2, 0, 1252903, 366611, 2757, 65536⟩
    (by decide) selected_cut_45284

theorem unmarked_context_11_91652_1252904 : frontier 10 ⟨1252904, by decide⟩
    (prefixCache 11 91652) (prefixPartial 11 91652) = false := by
  decide +kernel

theorem node_context_11_91652_1252904 : EJMOriginalGlobalDAGData.nodes 10 ⟨1252904, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1252784, by decide⟩,⟨1252845, by decide⟩,⟨1252903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91652_1252904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91652 ⟨1252904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91652
    ⟨1252904, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1252784, by decide⟩,⟨1252845, by decide⟩,⟨1252903, by decide⟩]) unmarked_context_11_91652_1252904 node_context_11_91652_1252904
  intro a
  fin_cases a
  · exact context_12_366608_985390
  · exact context_12_366609_1252784
  · exact context_12_366610_1252845
  · exact context_12_366611_1252903

theorem selected_cut_45285 : selected 9 ⟨1252985, by decide⟩
    (prefixPartial 12 366612) = some ⟨12, 2, 0, 1252985, 366612, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_366612_1252985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366612 ⟨1252985, by decide⟩ :=
  accepted_of_selected 12 366612 ⟨1252985, by decide⟩ ⟨12, 2, 0, 1252985, 366612, 1573, 65536⟩
    (by decide) selected_cut_45285

theorem selected_cut_45286 : selected 9 ⟨772506, by decide⟩
    (prefixPartial 12 366613) = some ⟨12, 1, 0, 772506, 366613, 1, 65536⟩ := by
  decide +kernel

theorem context_12_366613_772506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366613 ⟨772506, by decide⟩ :=
  accepted_of_selected 12 366613 ⟨772506, by decide⟩ ⟨12, 1, 0, 772506, 366613, 1, 65536⟩
    (by decide) selected_cut_45286

theorem selected_cut_45287 : selected 9 ⟨1253049, by decide⟩
    (prefixPartial 12 366614) = some ⟨12, 2, 0, 1253049, 366614, 2513, 65536⟩ := by
  decide +kernel

theorem context_12_366614_1253049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366614 ⟨1253049, by decide⟩ :=
  accepted_of_selected 12 366614 ⟨1253049, by decide⟩ ⟨12, 2, 0, 1253049, 366614, 2513, 65536⟩
    (by decide) selected_cut_45287

theorem selected_cut_45288 : selected 9 ⟨1253115, by decide⟩
    (prefixPartial 12 366615) = some ⟨12, 2, 0, 1253115, 366615, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_366615_1253115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366615 ⟨1253115, by decide⟩ :=
  accepted_of_selected 12 366615 ⟨1253115, by decide⟩ ⟨12, 2, 0, 1253115, 366615, 2769, 65536⟩
    (by decide) selected_cut_45288

theorem unmarked_context_11_91653_1253116 : frontier 10 ⟨1253116, by decide⟩
    (prefixCache 11 91653) (prefixPartial 11 91653) = false := by
  decide +kernel

theorem node_context_11_91653_1253116 : EJMOriginalGlobalDAGData.nodes 10 ⟨1253116, by decide⟩ =
    .split (coordinate 11) (![⟨1252985, by decide⟩,⟨772506, by decide⟩,⟨1253049, by decide⟩,⟨1253115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91653_1253116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91653 ⟨1253116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91653
    ⟨1253116, by decide⟩ (by decide) (![⟨1252985, by decide⟩,⟨772506, by decide⟩,⟨1253049, by decide⟩,⟨1253115, by decide⟩]) unmarked_context_11_91653_1253116 node_context_11_91653_1253116
  intro a
  fin_cases a
  · exact context_12_366612_1252985
  · exact context_12_366613_772506
  · exact context_12_366614_1253049
  · exact context_12_366615_1253115

theorem selected_cut_45289 : selected 9 ⟨994572, by decide⟩
    (prefixPartial 12 366616) = some ⟨12, 1, 0, 994572, 366616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_366616_994572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366616 ⟨994572, by decide⟩ :=
  accepted_of_selected 12 366616 ⟨994572, by decide⟩ ⟨12, 1, 0, 994572, 366616, 1, 65536⟩
    (by decide) selected_cut_45289

theorem selected_cut_45290 : selected 9 ⟨1253173, by decide⟩
    (prefixPartial 12 366617) = some ⟨12, 2, 0, 1253173, 366617, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_366617_1253173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366617 ⟨1253173, by decide⟩ :=
  accepted_of_selected 12 366617 ⟨1253173, by decide⟩ ⟨12, 2, 0, 1253173, 366617, 2545, 65536⟩
    (by decide) selected_cut_45290

theorem selected_cut_45291 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 366618) = some ⟨12, 1, 0, 806997, 366618, 1, 65536⟩ := by
  decide +kernel

theorem context_12_366618_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366618 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 366618 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 366618, 1, 65536⟩
    (by decide) selected_cut_45291

theorem selected_cut_45292 : selected 9 ⟨1253232, by decide⟩
    (prefixPartial 12 366619) = some ⟨12, 2, 0, 1253232, 366619, 2705, 65536⟩ := by
  decide +kernel

theorem context_12_366619_1253232 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366619 ⟨1253232, by decide⟩ :=
  accepted_of_selected 12 366619 ⟨1253232, by decide⟩ ⟨12, 2, 0, 1253232, 366619, 2705, 65536⟩
    (by decide) selected_cut_45292

theorem unmarked_context_11_91654_1253233 : frontier 10 ⟨1253233, by decide⟩
    (prefixCache 11 91654) (prefixPartial 11 91654) = false := by
  decide +kernel

theorem node_context_11_91654_1253233 : EJMOriginalGlobalDAGData.nodes 10 ⟨1253233, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1253173, by decide⟩,⟨806997, by decide⟩,⟨1253232, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91654_1253233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91654 ⟨1253233, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91654
    ⟨1253233, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1253173, by decide⟩,⟨806997, by decide⟩,⟨1253232, by decide⟩]) unmarked_context_11_91654_1253233 node_context_11_91654_1253233
  intro a
  fin_cases a
  · exact context_12_366616_994572
  · exact context_12_366617_1253173
  · exact context_12_366618_806997
  · exact context_12_366619_1253232

theorem selected_cut_45293 : selected 9 ⟨1253281, by decide⟩
    (prefixPartial 12 366620) = some ⟨12, 2, 0, 1253281, 366620, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_366620_1253281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366620 ⟨1253281, by decide⟩ :=
  accepted_of_selected 12 366620 ⟨1253281, by decide⟩ ⟨12, 2, 0, 1253281, 366620, 2025, 65536⟩
    (by decide) selected_cut_45293

theorem selected_cut_45294 : selected 9 ⟨1253333, by decide⟩
    (prefixPartial 12 366621) = some ⟨12, 2, 0, 1253333, 366621, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_366621_1253333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366621 ⟨1253333, by decide⟩ :=
  accepted_of_selected 12 366621 ⟨1253333, by decide⟩ ⟨12, 2, 0, 1253333, 366621, 2449, 65536⟩
    (by decide) selected_cut_45294

theorem selected_cut_45295 : selected 9 ⟨1253393, by decide⟩
    (prefixPartial 12 366622) = some ⟨12, 2, 0, 1253393, 366622, 2333, 65536⟩ := by
  decide +kernel

theorem context_12_366622_1253393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366622 ⟨1253393, by decide⟩ :=
  accepted_of_selected 12 366622 ⟨1253393, by decide⟩ ⟨12, 2, 0, 1253393, 366622, 2333, 65536⟩
    (by decide) selected_cut_45295

theorem selected_cut_45296 : selected 9 ⟨1253436, by decide⟩
    (prefixPartial 12 366623) = some ⟨12, 2, 0, 1253436, 366623, 2045, 65536⟩ := by
  decide +kernel

theorem context_12_366623_1253436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366623 ⟨1253436, by decide⟩ :=
  accepted_of_selected 12 366623 ⟨1253436, by decide⟩ ⟨12, 2, 0, 1253436, 366623, 2045, 65536⟩
    (by decide) selected_cut_45296

theorem unmarked_context_11_91655_1253437 : frontier 10 ⟨1253437, by decide⟩
    (prefixCache 11 91655) (prefixPartial 11 91655) = false := by
  decide +kernel

theorem node_context_11_91655_1253437 : EJMOriginalGlobalDAGData.nodes 10 ⟨1253437, by decide⟩ =
    .split (coordinate 11) (![⟨1253281, by decide⟩,⟨1253333, by decide⟩,⟨1253393, by decide⟩,⟨1253436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91655_1253437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91655 ⟨1253437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91655
    ⟨1253437, by decide⟩ (by decide) (![⟨1253281, by decide⟩,⟨1253333, by decide⟩,⟨1253393, by decide⟩,⟨1253436, by decide⟩]) unmarked_context_11_91655_1253437 node_context_11_91655_1253437
  intro a
  fin_cases a
  · exact context_12_366620_1253281
  · exact context_12_366621_1253333
  · exact context_12_366622_1253393
  · exact context_12_366623_1253436

theorem unmarked_context_10_22913_1253438 : frontier 11 ⟨1253438, by decide⟩
    (prefixCache 10 22913) (prefixPartial 10 22913) = false := by
  decide +kernel

theorem node_context_10_22913_1253438 : EJMOriginalGlobalDAGData.nodes 11 ⟨1253438, by decide⟩ =
    .split (coordinate 10) (![⟨1252904, by decide⟩,⟨1253116, by decide⟩,⟨1253233, by decide⟩,⟨1253437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22913_1253438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22913 ⟨1253438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22913
    ⟨1253438, by decide⟩ (by decide) (![⟨1252904, by decide⟩,⟨1253116, by decide⟩,⟨1253233, by decide⟩,⟨1253437, by decide⟩]) unmarked_context_10_22913_1253438 node_context_10_22913_1253438
  intro a
  fin_cases a
  · exact context_11_91652_1252904
  · exact context_11_91653_1253116
  · exact context_11_91654_1253233
  · exact context_11_91655_1253437

theorem selected_cut_45297 : selected 10 ⟨1253536, by decide⟩
    (prefixPartial 11 91656) = some ⟨11, 2, 0, 1253536, 91656, 3313, 262144⟩ := by
  decide +kernel

theorem context_11_91656_1253536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91656 ⟨1253536, by decide⟩ :=
  accepted_of_selected 11 91656 ⟨1253536, by decide⟩ ⟨11, 2, 0, 1253536, 91656, 3313, 262144⟩
    (by decide) selected_cut_45297

theorem selected_cut_45298 : selected 10 ⟨1253655, by decide⟩
    (prefixPartial 11 91657) = some ⟨11, 2, 0, 1253655, 91657, 3093, 262144⟩ := by
  decide +kernel

theorem context_11_91657_1253655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91657 ⟨1253655, by decide⟩ :=
  accepted_of_selected 11 91657 ⟨1253655, by decide⟩ ⟨11, 2, 0, 1253655, 91657, 3093, 262144⟩
    (by decide) selected_cut_45298

theorem selected_cut_45299 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 91658) = some ⟨11, 1, 0, 900587, 91658, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91658_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91658 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 91658 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 91658, 1, 262144⟩
    (by decide) selected_cut_45299

theorem selected_cut_45300 : selected 9 ⟨1253699, by decide⟩
    (prefixPartial 12 366636) = some ⟨12, 2, 0, 1253699, 366636, 1569, 65536⟩ := by
  decide +kernel

theorem context_12_366636_1253699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366636 ⟨1253699, by decide⟩ :=
  accepted_of_selected 12 366636 ⟨1253699, by decide⟩ ⟨12, 2, 0, 1253699, 366636, 1569, 65536⟩
    (by decide) selected_cut_45300

theorem selected_cut_45301 : selected 9 ⟨1253753, by decide⟩
    (prefixPartial 12 366637) = some ⟨12, 2, 0, 1253753, 366637, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_366637_1253753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366637 ⟨1253753, by decide⟩ :=
  accepted_of_selected 12 366637 ⟨1253753, by decide⟩ ⟨12, 2, 0, 1253753, 366637, 1701, 65536⟩
    (by decide) selected_cut_45301

theorem selected_cut_45302 : selected 9 ⟨1253800, by decide⟩
    (prefixPartial 12 366638) = some ⟨12, 2, 0, 1253800, 366638, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_366638_1253800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366638 ⟨1253800, by decide⟩ :=
  accepted_of_selected 12 366638 ⟨1253800, by decide⟩ ⟨12, 2, 0, 1253800, 366638, 1573, 65536⟩
    (by decide) selected_cut_45302

theorem selected_cut_45303 : selected 9 ⟨1253829, by decide⟩
    (prefixPartial 12 366639) = some ⟨12, 2, 0, 1253829, 366639, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_366639_1253829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 366639 ⟨1253829, by decide⟩ :=
  accepted_of_selected 12 366639 ⟨1253829, by decide⟩ ⟨12, 2, 0, 1253829, 366639, 1337, 65536⟩
    (by decide) selected_cut_45303

theorem unmarked_context_11_91659_1253830 : frontier 10 ⟨1253830, by decide⟩
    (prefixCache 11 91659) (prefixPartial 11 91659) = false := by
  decide +kernel

theorem node_context_11_91659_1253830 : EJMOriginalGlobalDAGData.nodes 10 ⟨1253830, by decide⟩ =
    .split (coordinate 11) (![⟨1253699, by decide⟩,⟨1253753, by decide⟩,⟨1253800, by decide⟩,⟨1253829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_91659_1253830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91659 ⟨1253830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 91659
    ⟨1253830, by decide⟩ (by decide) (![⟨1253699, by decide⟩,⟨1253753, by decide⟩,⟨1253800, by decide⟩,⟨1253829, by decide⟩]) unmarked_context_11_91659_1253830 node_context_11_91659_1253830
  intro a
  fin_cases a
  · exact context_12_366636_1253699
  · exact context_12_366637_1253753
  · exact context_12_366638_1253800
  · exact context_12_366639_1253829

theorem unmarked_context_10_22914_1253831 : frontier 11 ⟨1253831, by decide⟩
    (prefixCache 10 22914) (prefixPartial 10 22914) = false := by
  decide +kernel

theorem node_context_10_22914_1253831 : EJMOriginalGlobalDAGData.nodes 11 ⟨1253831, by decide⟩ =
    .split (coordinate 10) (![⟨1253536, by decide⟩,⟨1253655, by decide⟩,⟨900587, by decide⟩,⟨1253830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22914_1253831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22914 ⟨1253831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22914
    ⟨1253831, by decide⟩ (by decide) (![⟨1253536, by decide⟩,⟨1253655, by decide⟩,⟨900587, by decide⟩,⟨1253830, by decide⟩]) unmarked_context_10_22914_1253831 node_context_10_22914_1253831
  intro a
  fin_cases a
  · exact context_11_91656_1253536
  · exact context_11_91657_1253655
  · exact context_11_91658_900587
  · exact context_11_91659_1253830

theorem selected_cut_45304 : selected 10 ⟨1253950, by decide⟩
    (prefixPartial 11 91660) = some ⟨11, 2, 0, 1253950, 91660, 2729, 262144⟩ := by
  decide +kernel

theorem context_11_91660_1253950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91660 ⟨1253950, by decide⟩ :=
  accepted_of_selected 11 91660 ⟨1253950, by decide⟩ ⟨11, 2, 0, 1253950, 91660, 2729, 262144⟩
    (by decide) selected_cut_45304

theorem selected_cut_45305 : selected 10 ⟨1254018, by decide⟩
    (prefixPartial 11 91661) = some ⟨11, 2, 0, 1254018, 91661, 913, 262144⟩ := by
  decide +kernel

theorem context_11_91661_1254018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91661 ⟨1254018, by decide⟩ :=
  accepted_of_selected 11 91661 ⟨1254018, by decide⟩ ⟨11, 2, 0, 1254018, 91661, 913, 262144⟩
    (by decide) selected_cut_45305

theorem selected_cut_45306 : selected 10 ⟨1254067, by decide⟩
    (prefixPartial 11 91662) = some ⟨11, 2, 0, 1254067, 91662, 1289, 262144⟩ := by
  decide +kernel

theorem context_11_91662_1254067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91662 ⟨1254067, by decide⟩ :=
  accepted_of_selected 11 91662 ⟨1254067, by decide⟩ ⟨11, 2, 0, 1254067, 91662, 1289, 262144⟩
    (by decide) selected_cut_45306

theorem selected_cut_45307 : selected 10 ⟨1254161, by decide⟩
    (prefixPartial 11 91663) = some ⟨11, 2, 0, 1254161, 91663, 2593, 262144⟩ := by
  decide +kernel

theorem context_11_91663_1254161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91663 ⟨1254161, by decide⟩ :=
  accepted_of_selected 11 91663 ⟨1254161, by decide⟩ ⟨11, 2, 0, 1254161, 91663, 2593, 262144⟩
    (by decide) selected_cut_45307

theorem unmarked_context_10_22915_1254162 : frontier 11 ⟨1254162, by decide⟩
    (prefixCache 10 22915) (prefixPartial 10 22915) = false := by
  decide +kernel

theorem node_context_10_22915_1254162 : EJMOriginalGlobalDAGData.nodes 11 ⟨1254162, by decide⟩ =
    .split (coordinate 10) (![⟨1253950, by decide⟩,⟨1254018, by decide⟩,⟨1254067, by decide⟩,⟨1254161, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_22915_1254162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 22915 ⟨1254162, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 22915
    ⟨1254162, by decide⟩ (by decide) (![⟨1253950, by decide⟩,⟨1254018, by decide⟩,⟨1254067, by decide⟩,⟨1254161, by decide⟩]) unmarked_context_10_22915_1254162 node_context_10_22915_1254162
  intro a
  fin_cases a
  · exact context_11_91660_1253950
  · exact context_11_91661_1254018
  · exact context_11_91662_1254067
  · exact context_11_91663_1254161

theorem unmarked_context_9_5728_1254163 : frontier 12 ⟨1254163, by decide⟩
    (prefixCache 9 5728) (prefixPartial 9 5728) = false := by
  decide +kernel

theorem node_context_9_5728_1254163 : EJMOriginalGlobalDAGData.nodes 12 ⟨1254163, by decide⟩ =
    .split (coordinate 9) (![⟨1252725, by decide⟩,⟨1253438, by decide⟩,⟨1253831, by decide⟩,⟨1254162, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5728_1254163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5728 ⟨1254163, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5728
    ⟨1254163, by decide⟩ (by decide) (![⟨1252725, by decide⟩,⟨1253438, by decide⟩,⟨1253831, by decide⟩,⟨1254162, by decide⟩]) unmarked_context_9_5728_1254163 node_context_9_5728_1254163
  intro a
  fin_cases a
  · exact context_10_22912_1252725
  · exact context_10_22913_1253438
  · exact context_10_22914_1253831
  · exact context_10_22915_1254162

theorem selected_cut_45308 : selected 12 ⟨1254422, by decide⟩
    (prefixPartial 9 5729) = some ⟨9, 2, 0, 1254422, 5729, 3629, 4194304⟩ := by
  decide +kernel

theorem context_9_5729_1254422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5729 ⟨1254422, by decide⟩ :=
  accepted_of_selected 9 5729 ⟨1254422, by decide⟩ ⟨9, 2, 0, 1254422, 5729, 3629, 4194304⟩
    (by decide) selected_cut_45308

theorem selected_cut_45309 : selected 12 ⟨1254451, by decide⟩
    (prefixPartial 9 5730) = some ⟨9, 2, 0, 1254451, 5730, 173, 4194304⟩ := by
  decide +kernel

theorem context_9_5730_1254451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5730 ⟨1254451, by decide⟩ :=
  accepted_of_selected 9 5730 ⟨1254451, by decide⟩ ⟨9, 2, 0, 1254451, 5730, 173, 4194304⟩
    (by decide) selected_cut_45309

theorem selected_cut_45310 : selected 12 ⟨1254453, by decide⟩
    (prefixPartial 9 5731) = some ⟨9, 2, 0, 1254453, 5731, 9, 4194304⟩ := by
  decide +kernel

theorem context_9_5731_1254453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5731 ⟨1254453, by decide⟩ :=
  accepted_of_selected 9 5731 ⟨1254453, by decide⟩ ⟨9, 2, 0, 1254453, 5731, 9, 4194304⟩
    (by decide) selected_cut_45310

theorem unmarked_context_8_1432_1254454 : frontier 13 ⟨1254454, by decide⟩
    (prefixCache 8 1432) (prefixPartial 8 1432) = false := by
  decide +kernel

theorem node_context_8_1432_1254454 : EJMOriginalGlobalDAGData.nodes 13 ⟨1254454, by decide⟩ =
    .split (coordinate 8) (![⟨1254163, by decide⟩,⟨1254422, by decide⟩,⟨1254451, by decide⟩,⟨1254453, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1432_1254454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1432 ⟨1254454, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1432
    ⟨1254454, by decide⟩ (by decide) (![⟨1254163, by decide⟩,⟨1254422, by decide⟩,⟨1254451, by decide⟩,⟨1254453, by decide⟩]) unmarked_context_8_1432_1254454 node_context_8_1432_1254454
  intro a
  fin_cases a
  · exact context_9_5728_1254163
  · exact context_9_5729_1254422
  · exact context_9_5730_1254451
  · exact context_9_5731_1254453

theorem selected_cut_45311 : selected 13 ⟨1109534, by decide⟩
    (prefixPartial 8 1433) = some ⟨8, 1, 0, 1109534, 1433, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1433_1109534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1433 ⟨1109534, by decide⟩ :=
  accepted_of_selected 8 1433 ⟨1109534, by decide⟩ ⟨8, 1, 0, 1109534, 1433, 1, 16777216⟩
    (by decide) selected_cut_45311

theorem selected_cut_45312 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 91776) = some ⟨11, 1, 0, 434745, 91776, 1, 262144⟩ := by
  decide +kernel

theorem context_11_91776_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 91776 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 91776 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 91776, 1, 262144⟩
    (by decide) selected_cut_45312

theorem selected_cut_45313 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 367108) = some ⟨12, 1, 0, 895, 367108, 1, 65536⟩ := by
  decide +kernel

theorem context_12_367108_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367108 ⟨895, by decide⟩ :=
  accepted_of_selected 12 367108 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 367108, 1, 65536⟩
    (by decide) selected_cut_45313

theorem selected_cut_45314 : selected 9 ⟨1254593, by decide⟩
    (prefixPartial 12 367109) = some ⟨12, 2, 0, 1254593, 367109, 3121, 65536⟩ := by
  decide +kernel

theorem context_12_367109_1254593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 367109 ⟨1254593, by decide⟩ :=
  accepted_of_selected 12 367109 ⟨1254593, by decide⟩ ⟨12, 2, 0, 1254593, 367109, 3121, 65536⟩
    (by decide) selected_cut_45314

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
