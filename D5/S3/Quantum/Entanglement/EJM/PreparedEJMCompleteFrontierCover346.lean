/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover345
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33220 : selected 8 ⟨855898, by decide⟩
    (prefixPartial 13 440461) = some ⟨13, 2, 0, 855898, 440461, 2813, 16384⟩ := by
  decide +kernel

theorem context_13_440461_855898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440461 ⟨855898, by decide⟩ :=
  accepted_of_selected 13 440461 ⟨855898, by decide⟩ ⟨13, 2, 0, 855898, 440461, 2813, 16384⟩
    (by decide) selected_cut_33220

theorem selected_cut_33221 : selected 8 ⟨855929, by decide⟩
    (prefixPartial 13 440462) = some ⟨13, 2, 0, 855929, 440462, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_440462_855929 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440462 ⟨855929, by decide⟩ :=
  accepted_of_selected 13 440462 ⟨855929, by decide⟩ ⟨13, 2, 0, 855929, 440462, 1521, 16384⟩
    (by decide) selected_cut_33221

theorem selected_cut_33222 : selected 8 ⟨855935, by decide⟩
    (prefixPartial 13 440463) = some ⟨13, 2, 0, 855935, 440463, 637, 16384⟩ := by
  decide +kernel

theorem context_13_440463_855935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440463 ⟨855935, by decide⟩ :=
  accepted_of_selected 13 440463 ⟨855935, by decide⟩ ⟨13, 2, 0, 855935, 440463, 637, 16384⟩
    (by decide) selected_cut_33222

theorem unmarked_context_12_110115_855936 : frontier 9 ⟨855936, by decide⟩
    (prefixCache 12 110115) (prefixPartial 12 110115) = false := by
  decide +kernel

theorem node_context_12_110115_855936 : EJMOriginalGlobalDAGData.nodes 9 ⟨855936, by decide⟩ =
    .split (coordinate 12) (![⟨855856, by decide⟩,⟨855898, by decide⟩,⟨855929, by decide⟩,⟨855935, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110115_855936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110115 ⟨855936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110115
    ⟨855936, by decide⟩ (by decide) (![⟨855856, by decide⟩,⟨855898, by decide⟩,⟨855929, by decide⟩,⟨855935, by decide⟩]) unmarked_context_12_110115_855936 node_context_12_110115_855936
  intro a
  fin_cases a
  · exact context_13_440460_855856
  · exact context_13_440461_855898
  · exact context_13_440462_855929
  · exact context_13_440463_855935

theorem unmarked_context_11_27528_855937 : frontier 10 ⟨855937, by decide⟩
    (prefixCache 11 27528) (prefixPartial 11 27528) = false := by
  decide +kernel

theorem node_context_11_27528_855937 : EJMOriginalGlobalDAGData.nodes 10 ⟨855937, by decide⟩ =
    .split (coordinate 11) (![⟨855670, by decide⟩,⟨855778, by decide⟩,⟨855840, by decide⟩,⟨855936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27528_855937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27528 ⟨855937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27528
    ⟨855937, by decide⟩ (by decide) (![⟨855670, by decide⟩,⟨855778, by decide⟩,⟨855840, by decide⟩,⟨855936, by decide⟩]) unmarked_context_11_27528_855937 node_context_11_27528_855937
  intro a
  fin_cases a
  · exact context_12_110112_855670
  · exact context_12_110113_855778
  · exact context_12_110114_855840
  · exact context_12_110115_855936

theorem selected_cut_33223 : selected 8 ⟨855953, by decide⟩
    (prefixPartial 13 440464) = some ⟨13, 2, 0, 855953, 440464, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_440464_855953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440464 ⟨855953, by decide⟩ :=
  accepted_of_selected 13 440464 ⟨855953, by decide⟩ ⟨13, 2, 0, 855953, 440464, 1133, 16384⟩
    (by decide) selected_cut_33223

theorem selected_cut_33224 : selected 8 ⟨855977, by decide⟩
    (prefixPartial 13 440465) = some ⟨13, 2, 0, 855977, 440465, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_440465_855977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440465 ⟨855977, by decide⟩ :=
  accepted_of_selected 13 440465 ⟨855977, by decide⟩ ⟨13, 2, 0, 855977, 440465, 2325, 16384⟩
    (by decide) selected_cut_33224

theorem selected_cut_33225 : selected 8 ⟨856005, by decide⟩
    (prefixPartial 13 440466) = some ⟨13, 2, 0, 856005, 440466, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_440466_856005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440466 ⟨856005, by decide⟩ :=
  accepted_of_selected 13 440466 ⟨856005, by decide⟩ ⟨13, 2, 0, 856005, 440466, 1405, 16384⟩
    (by decide) selected_cut_33225

theorem selected_cut_33226 : selected 8 ⟨856012, by decide⟩
    (prefixPartial 13 440467) = some ⟨13, 2, 0, 856012, 440467, 729, 16384⟩ := by
  decide +kernel

theorem context_13_440467_856012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440467 ⟨856012, by decide⟩ :=
  accepted_of_selected 13 440467 ⟨856012, by decide⟩ ⟨13, 2, 0, 856012, 440467, 729, 16384⟩
    (by decide) selected_cut_33226

theorem unmarked_context_12_110116_856013 : frontier 9 ⟨856013, by decide⟩
    (prefixCache 12 110116) (prefixPartial 12 110116) = false := by
  decide +kernel

theorem node_context_12_110116_856013 : EJMOriginalGlobalDAGData.nodes 9 ⟨856013, by decide⟩ =
    .split (coordinate 12) (![⟨855953, by decide⟩,⟨855977, by decide⟩,⟨856005, by decide⟩,⟨856012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110116_856013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110116 ⟨856013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110116
    ⟨856013, by decide⟩ (by decide) (![⟨855953, by decide⟩,⟨855977, by decide⟩,⟨856005, by decide⟩,⟨856012, by decide⟩]) unmarked_context_12_110116_856013 node_context_12_110116_856013
  intro a
  fin_cases a
  · exact context_13_440464_855953
  · exact context_13_440465_855977
  · exact context_13_440466_856005
  · exact context_13_440467_856012

theorem selected_cut_33227 : selected 8 ⟨856035, by decide⟩
    (prefixPartial 13 440468) = some ⟨13, 2, 0, 856035, 440468, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_440468_856035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440468 ⟨856035, by decide⟩ :=
  accepted_of_selected 13 440468 ⟨856035, by decide⟩ ⟨13, 2, 0, 856035, 440468, 1261, 16384⟩
    (by decide) selected_cut_33227

theorem selected_cut_33228 : selected 8 ⟨856064, by decide⟩
    (prefixPartial 13 440469) = some ⟨13, 2, 0, 856064, 440469, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_440469_856064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440469 ⟨856064, by decide⟩ :=
  accepted_of_selected 13 440469 ⟨856064, by decide⟩ ⟨13, 2, 0, 856064, 440469, 2437, 16384⟩
    (by decide) selected_cut_33228

theorem selected_cut_33229 : selected 8 ⟨856090, by decide⟩
    (prefixPartial 13 440470) = some ⟨13, 2, 0, 856090, 440470, 1577, 16384⟩ := by
  decide +kernel

theorem context_13_440470_856090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440470 ⟨856090, by decide⟩ :=
  accepted_of_selected 13 440470 ⟨856090, by decide⟩ ⟨13, 2, 0, 856090, 440470, 1577, 16384⟩
    (by decide) selected_cut_33229

theorem selected_cut_33230 : selected 8 ⟨856099, by decide⟩
    (prefixPartial 13 440471) = some ⟨13, 2, 0, 856099, 440471, 705, 16384⟩ := by
  decide +kernel

theorem context_13_440471_856099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440471 ⟨856099, by decide⟩ :=
  accepted_of_selected 13 440471 ⟨856099, by decide⟩ ⟨13, 2, 0, 856099, 440471, 705, 16384⟩
    (by decide) selected_cut_33230

theorem unmarked_context_12_110117_856100 : frontier 9 ⟨856100, by decide⟩
    (prefixCache 12 110117) (prefixPartial 12 110117) = false := by
  decide +kernel

theorem node_context_12_110117_856100 : EJMOriginalGlobalDAGData.nodes 9 ⟨856100, by decide⟩ =
    .split (coordinate 12) (![⟨856035, by decide⟩,⟨856064, by decide⟩,⟨856090, by decide⟩,⟨856099, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110117_856100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110117 ⟨856100, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110117
    ⟨856100, by decide⟩ (by decide) (![⟨856035, by decide⟩,⟨856064, by decide⟩,⟨856090, by decide⟩,⟨856099, by decide⟩]) unmarked_context_12_110117_856100 node_context_12_110117_856100
  intro a
  fin_cases a
  · exact context_13_440468_856035
  · exact context_13_440469_856064
  · exact context_13_440470_856090
  · exact context_13_440471_856099

theorem selected_cut_33231 : selected 8 ⟨856112, by decide⟩
    (prefixPartial 13 440472) = some ⟨13, 2, 0, 856112, 440472, 785, 16384⟩ := by
  decide +kernel

theorem context_13_440472_856112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440472 ⟨856112, by decide⟩ :=
  accepted_of_selected 13 440472 ⟨856112, by decide⟩ ⟨13, 2, 0, 856112, 440472, 785, 16384⟩
    (by decide) selected_cut_33231

theorem selected_cut_33232 : selected 8 ⟨856134, by decide⟩
    (prefixPartial 13 440473) = some ⟨13, 2, 0, 856134, 440473, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_440473_856134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440473 ⟨856134, by decide⟩ :=
  accepted_of_selected 13 440473 ⟨856134, by decide⟩ ⟨13, 2, 0, 856134, 440473, 1949, 16384⟩
    (by decide) selected_cut_33232

theorem selected_cut_33233 : selected 8 ⟨856151, by decide⟩
    (prefixPartial 13 440474) = some ⟨13, 2, 0, 856151, 440474, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_440474_856151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440474 ⟨856151, by decide⟩ :=
  accepted_of_selected 13 440474 ⟨856151, by decide⟩ ⟨13, 2, 0, 856151, 440474, 1109, 16384⟩
    (by decide) selected_cut_33233

theorem selected_cut_33234 : selected 8 ⟨856160, by decide⟩
    (prefixPartial 13 440475) = some ⟨13, 2, 0, 856160, 440475, 681, 16384⟩ := by
  decide +kernel

theorem context_13_440475_856160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440475 ⟨856160, by decide⟩ :=
  accepted_of_selected 13 440475 ⟨856160, by decide⟩ ⟨13, 2, 0, 856160, 440475, 681, 16384⟩
    (by decide) selected_cut_33234

theorem unmarked_context_12_110118_856161 : frontier 9 ⟨856161, by decide⟩
    (prefixCache 12 110118) (prefixPartial 12 110118) = false := by
  decide +kernel

theorem node_context_12_110118_856161 : EJMOriginalGlobalDAGData.nodes 9 ⟨856161, by decide⟩ =
    .split (coordinate 12) (![⟨856112, by decide⟩,⟨856134, by decide⟩,⟨856151, by decide⟩,⟨856160, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110118_856161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110118 ⟨856161, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110118
    ⟨856161, by decide⟩ (by decide) (![⟨856112, by decide⟩,⟨856134, by decide⟩,⟨856151, by decide⟩,⟨856160, by decide⟩]) unmarked_context_12_110118_856161 node_context_12_110118_856161
  intro a
  fin_cases a
  · exact context_13_440472_856112
  · exact context_13_440473_856134
  · exact context_13_440474_856151
  · exact context_13_440475_856160

theorem selected_cut_33235 : selected 8 ⟨856183, by decide⟩
    (prefixPartial 13 440476) = some ⟨13, 2, 0, 856183, 440476, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_440476_856183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440476 ⟨856183, by decide⟩ :=
  accepted_of_selected 13 440476 ⟨856183, by decide⟩ ⟨13, 2, 0, 856183, 440476, 1193, 16384⟩
    (by decide) selected_cut_33235

theorem selected_cut_33236 : selected 8 ⟨856229, by decide⟩
    (prefixPartial 13 440477) = some ⟨13, 2, 0, 856229, 440477, 2853, 16384⟩ := by
  decide +kernel

theorem context_13_440477_856229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440477 ⟨856229, by decide⟩ :=
  accepted_of_selected 13 440477 ⟨856229, by decide⟩ ⟨13, 2, 0, 856229, 440477, 2853, 16384⟩
    (by decide) selected_cut_33236

theorem selected_cut_33237 : selected 8 ⟨856257, by decide⟩
    (prefixPartial 13 440478) = some ⟨13, 2, 0, 856257, 440478, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_440478_856257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440478 ⟨856257, by decide⟩ :=
  accepted_of_selected 13 440478 ⟨856257, by decide⟩ ⟨13, 2, 0, 856257, 440478, 1745, 16384⟩
    (by decide) selected_cut_33237

theorem selected_cut_33238 : selected 8 ⟨856264, by decide⟩
    (prefixPartial 13 440479) = some ⟨13, 2, 0, 856264, 440479, 761, 16384⟩ := by
  decide +kernel

theorem context_13_440479_856264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440479 ⟨856264, by decide⟩ :=
  accepted_of_selected 13 440479 ⟨856264, by decide⟩ ⟨13, 2, 0, 856264, 440479, 761, 16384⟩
    (by decide) selected_cut_33238

theorem unmarked_context_12_110119_856265 : frontier 9 ⟨856265, by decide⟩
    (prefixCache 12 110119) (prefixPartial 12 110119) = false := by
  decide +kernel

theorem node_context_12_110119_856265 : EJMOriginalGlobalDAGData.nodes 9 ⟨856265, by decide⟩ =
    .split (coordinate 12) (![⟨856183, by decide⟩,⟨856229, by decide⟩,⟨856257, by decide⟩,⟨856264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110119_856265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110119 ⟨856265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110119
    ⟨856265, by decide⟩ (by decide) (![⟨856183, by decide⟩,⟨856229, by decide⟩,⟨856257, by decide⟩,⟨856264, by decide⟩]) unmarked_context_12_110119_856265 node_context_12_110119_856265
  intro a
  fin_cases a
  · exact context_13_440476_856183
  · exact context_13_440477_856229
  · exact context_13_440478_856257
  · exact context_13_440479_856264

theorem unmarked_context_11_27529_856266 : frontier 10 ⟨856266, by decide⟩
    (prefixCache 11 27529) (prefixPartial 11 27529) = false := by
  decide +kernel

theorem node_context_11_27529_856266 : EJMOriginalGlobalDAGData.nodes 10 ⟨856266, by decide⟩ =
    .split (coordinate 11) (![⟨856013, by decide⟩,⟨856100, by decide⟩,⟨856161, by decide⟩,⟨856265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27529_856266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27529 ⟨856266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27529
    ⟨856266, by decide⟩ (by decide) (![⟨856013, by decide⟩,⟨856100, by decide⟩,⟨856161, by decide⟩,⟨856265, by decide⟩]) unmarked_context_11_27529_856266 node_context_11_27529_856266
  intro a
  fin_cases a
  · exact context_12_110116_856013
  · exact context_12_110117_856100
  · exact context_12_110118_856161
  · exact context_12_110119_856265

theorem selected_cut_33239 : selected 8 ⟨856278, by decide⟩
    (prefixPartial 13 440480) = some ⟨13, 2, 0, 856278, 440480, 737, 16384⟩ := by
  decide +kernel

theorem context_13_440480_856278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440480 ⟨856278, by decide⟩ :=
  accepted_of_selected 13 440480 ⟨856278, by decide⟩ ⟨13, 2, 0, 856278, 440480, 737, 16384⟩
    (by decide) selected_cut_33239

theorem selected_cut_33240 : selected 8 ⟨856299, by decide⟩
    (prefixPartial 13 440481) = some ⟨13, 2, 0, 856299, 440481, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_440481_856299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440481 ⟨856299, by decide⟩ :=
  accepted_of_selected 13 440481 ⟨856299, by decide⟩ ⟨13, 2, 0, 856299, 440481, 1877, 16384⟩
    (by decide) selected_cut_33240

theorem selected_cut_33241 : selected 8 ⟨856321, by decide⟩
    (prefixPartial 13 440482) = some ⟨13, 2, 0, 856321, 440482, 1377, 16384⟩ := by
  decide +kernel

theorem context_13_440482_856321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440482 ⟨856321, by decide⟩ :=
  accepted_of_selected 13 440482 ⟨856321, by decide⟩ ⟨13, 2, 0, 856321, 440482, 1377, 16384⟩
    (by decide) selected_cut_33241

theorem selected_cut_33242 : selected 8 ⟨856325, by decide⟩
    (prefixPartial 13 440483) = some ⟨13, 2, 0, 856325, 440483, 529, 16384⟩ := by
  decide +kernel

theorem context_13_440483_856325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440483 ⟨856325, by decide⟩ :=
  accepted_of_selected 13 440483 ⟨856325, by decide⟩ ⟨13, 2, 0, 856325, 440483, 529, 16384⟩
    (by decide) selected_cut_33242

theorem unmarked_context_12_110120_856326 : frontier 9 ⟨856326, by decide⟩
    (prefixCache 12 110120) (prefixPartial 12 110120) = false := by
  decide +kernel

theorem node_context_12_110120_856326 : EJMOriginalGlobalDAGData.nodes 9 ⟨856326, by decide⟩ =
    .split (coordinate 12) (![⟨856278, by decide⟩,⟨856299, by decide⟩,⟨856321, by decide⟩,⟨856325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110120_856326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110120 ⟨856326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110120
    ⟨856326, by decide⟩ (by decide) (![⟨856278, by decide⟩,⟨856299, by decide⟩,⟨856321, by decide⟩,⟨856325, by decide⟩]) unmarked_context_12_110120_856326 node_context_12_110120_856326
  intro a
  fin_cases a
  · exact context_13_440480_856278
  · exact context_13_440481_856299
  · exact context_13_440482_856321
  · exact context_13_440483_856325

theorem selected_cut_33243 : selected 8 ⟨856339, by decide⟩
    (prefixPartial 13 440484) = some ⟨13, 2, 0, 856339, 440484, 941, 16384⟩ := by
  decide +kernel

theorem context_13_440484_856339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440484 ⟨856339, by decide⟩ :=
  accepted_of_selected 13 440484 ⟨856339, by decide⟩ ⟨13, 2, 0, 856339, 440484, 941, 16384⟩
    (by decide) selected_cut_33243

theorem selected_cut_33244 : selected 8 ⟨856369, by decide⟩
    (prefixPartial 13 440485) = some ⟨13, 2, 0, 856369, 440485, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_440485_856369 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440485 ⟨856369, by decide⟩ :=
  accepted_of_selected 13 440485 ⟨856369, by decide⟩ ⟨13, 2, 0, 856369, 440485, 2161, 16384⟩
    (by decide) selected_cut_33244

theorem selected_cut_33245 : selected 8 ⟨856388, by decide⟩
    (prefixPartial 13 440486) = some ⟨13, 2, 0, 856388, 440486, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_440486_856388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440486 ⟨856388, by decide⟩ :=
  accepted_of_selected 13 440486 ⟨856388, by decide⟩ ⟨13, 2, 0, 856388, 440486, 1557, 16384⟩
    (by decide) selected_cut_33245

theorem selected_cut_33246 : selected 8 ⟨856392, by decide⟩
    (prefixPartial 13 440487) = some ⟨13, 2, 0, 856392, 440487, 549, 16384⟩ := by
  decide +kernel

theorem context_13_440487_856392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440487 ⟨856392, by decide⟩ :=
  accepted_of_selected 13 440487 ⟨856392, by decide⟩ ⟨13, 2, 0, 856392, 440487, 549, 16384⟩
    (by decide) selected_cut_33246

theorem unmarked_context_12_110121_856393 : frontier 9 ⟨856393, by decide⟩
    (prefixCache 12 110121) (prefixPartial 12 110121) = false := by
  decide +kernel

theorem node_context_12_110121_856393 : EJMOriginalGlobalDAGData.nodes 9 ⟨856393, by decide⟩ =
    .split (coordinate 12) (![⟨856339, by decide⟩,⟨856369, by decide⟩,⟨856388, by decide⟩,⟨856392, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110121_856393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110121 ⟨856393, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110121
    ⟨856393, by decide⟩ (by decide) (![⟨856339, by decide⟩,⟨856369, by decide⟩,⟨856388, by decide⟩,⟨856392, by decide⟩]) unmarked_context_12_110121_856393 node_context_12_110121_856393
  intro a
  fin_cases a
  · exact context_13_440484_856339
  · exact context_13_440485_856369
  · exact context_13_440486_856388
  · exact context_13_440487_856392

theorem selected_cut_33247 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 110122) = some ⟨12, 1, 0, 445248, 110122, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110122_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110122 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 110122 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 110122, 1, 65536⟩
    (by decide) selected_cut_33247

theorem selected_cut_33248 : selected 8 ⟨856405, by decide⟩
    (prefixPartial 13 440492) = some ⟨13, 2, 0, 856405, 440492, 765, 16384⟩ := by
  decide +kernel

theorem context_13_440492_856405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440492 ⟨856405, by decide⟩ :=
  accepted_of_selected 13 440492 ⟨856405, by decide⟩ ⟨13, 2, 0, 856405, 440492, 765, 16384⟩
    (by decide) selected_cut_33248

theorem selected_cut_33249 : selected 8 ⟨856437, by decide⟩
    (prefixPartial 13 440493) = some ⟨13, 2, 0, 856437, 440493, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_440493_856437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440493 ⟨856437, by decide⟩ :=
  accepted_of_selected 13 440493 ⟨856437, by decide⟩ ⟨13, 2, 0, 856437, 440493, 2469, 16384⟩
    (by decide) selected_cut_33249

theorem selected_cut_33250 : selected 8 ⟨856454, by decide⟩
    (prefixPartial 13 440494) = some ⟨13, 2, 0, 856454, 440494, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_440494_856454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440494 ⟨856454, by decide⟩ :=
  accepted_of_selected 13 440494 ⟨856454, by decide⟩ ⟨13, 2, 0, 856454, 440494, 1461, 16384⟩
    (by decide) selected_cut_33250

theorem selected_cut_33251 : selected 8 ⟨856458, by decide⟩
    (prefixPartial 13 440495) = some ⟨13, 2, 0, 856458, 440495, 549, 16384⟩ := by
  decide +kernel

theorem context_13_440495_856458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440495 ⟨856458, by decide⟩ :=
  accepted_of_selected 13 440495 ⟨856458, by decide⟩ ⟨13, 2, 0, 856458, 440495, 549, 16384⟩
    (by decide) selected_cut_33251

theorem unmarked_context_12_110123_856459 : frontier 9 ⟨856459, by decide⟩
    (prefixCache 12 110123) (prefixPartial 12 110123) = false := by
  decide +kernel

theorem node_context_12_110123_856459 : EJMOriginalGlobalDAGData.nodes 9 ⟨856459, by decide⟩ =
    .split (coordinate 12) (![⟨856405, by decide⟩,⟨856437, by decide⟩,⟨856454, by decide⟩,⟨856458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110123_856459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110123 ⟨856459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110123
    ⟨856459, by decide⟩ (by decide) (![⟨856405, by decide⟩,⟨856437, by decide⟩,⟨856454, by decide⟩,⟨856458, by decide⟩]) unmarked_context_12_110123_856459 node_context_12_110123_856459
  intro a
  fin_cases a
  · exact context_13_440492_856405
  · exact context_13_440493_856437
  · exact context_13_440494_856454
  · exact context_13_440495_856458

theorem unmarked_context_11_27530_856460 : frontier 10 ⟨856460, by decide⟩
    (prefixCache 11 27530) (prefixPartial 11 27530) = false := by
  decide +kernel

theorem node_context_11_27530_856460 : EJMOriginalGlobalDAGData.nodes 10 ⟨856460, by decide⟩ =
    .split (coordinate 11) (![⟨856326, by decide⟩,⟨856393, by decide⟩,⟨445248, by decide⟩,⟨856459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27530_856460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27530 ⟨856460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27530
    ⟨856460, by decide⟩ (by decide) (![⟨856326, by decide⟩,⟨856393, by decide⟩,⟨445248, by decide⟩,⟨856459, by decide⟩]) unmarked_context_11_27530_856460 node_context_11_27530_856460
  intro a
  fin_cases a
  · exact context_12_110120_856326
  · exact context_12_110121_856393
  · exact context_12_110122_445248
  · exact context_12_110123_856459

theorem selected_cut_33252 : selected 8 ⟨856469, by decide⟩
    (prefixPartial 13 440496) = some ⟨13, 2, 0, 856469, 440496, 625, 16384⟩ := by
  decide +kernel

theorem context_13_440496_856469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440496 ⟨856469, by decide⟩ :=
  accepted_of_selected 13 440496 ⟨856469, by decide⟩ ⟨13, 2, 0, 856469, 440496, 625, 16384⟩
    (by decide) selected_cut_33252

theorem selected_cut_33253 : selected 8 ⟨856492, by decide⟩
    (prefixPartial 13 440497) = some ⟨13, 2, 0, 856492, 440497, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_440497_856492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440497 ⟨856492, by decide⟩ :=
  accepted_of_selected 13 440497 ⟨856492, by decide⟩ ⟨13, 2, 0, 856492, 440497, 2157, 16384⟩
    (by decide) selected_cut_33253

theorem selected_cut_33254 : selected 8 ⟨856509, by decide⟩
    (prefixPartial 13 440498) = some ⟨13, 2, 0, 856509, 440498, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_440498_856509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440498 ⟨856509, by decide⟩ :=
  accepted_of_selected 13 440498 ⟨856509, by decide⟩ ⟨13, 2, 0, 856509, 440498, 1453, 16384⟩
    (by decide) selected_cut_33254

theorem selected_cut_33255 : selected 8 ⟨856517, by decide⟩
    (prefixPartial 13 440499) = some ⟨13, 2, 0, 856517, 440499, 849, 16384⟩ := by
  decide +kernel

theorem context_13_440499_856517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440499 ⟨856517, by decide⟩ :=
  accepted_of_selected 13 440499 ⟨856517, by decide⟩ ⟨13, 2, 0, 856517, 440499, 849, 16384⟩
    (by decide) selected_cut_33255

theorem unmarked_context_12_110124_856518 : frontier 9 ⟨856518, by decide⟩
    (prefixCache 12 110124) (prefixPartial 12 110124) = false := by
  decide +kernel

theorem node_context_12_110124_856518 : EJMOriginalGlobalDAGData.nodes 9 ⟨856518, by decide⟩ =
    .split (coordinate 12) (![⟨856469, by decide⟩,⟨856492, by decide⟩,⟨856509, by decide⟩,⟨856517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110124_856518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110124 ⟨856518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110124
    ⟨856518, by decide⟩ (by decide) (![⟨856469, by decide⟩,⟨856492, by decide⟩,⟨856509, by decide⟩,⟨856517, by decide⟩]) unmarked_context_12_110124_856518 node_context_12_110124_856518
  intro a
  fin_cases a
  · exact context_13_440496_856469
  · exact context_13_440497_856492
  · exact context_13_440498_856509
  · exact context_13_440499_856517

theorem selected_cut_33256 : selected 8 ⟨856532, by decide⟩
    (prefixPartial 13 440500) = some ⟨13, 2, 0, 856532, 440500, 721, 16384⟩ := by
  decide +kernel

theorem context_13_440500_856532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440500 ⟨856532, by decide⟩ :=
  accepted_of_selected 13 440500 ⟨856532, by decide⟩ ⟨13, 2, 0, 856532, 440500, 721, 16384⟩
    (by decide) selected_cut_33256

theorem selected_cut_33257 : selected 8 ⟨856567, by decide⟩
    (prefixPartial 13 440501) = some ⟨13, 2, 0, 856567, 440501, 2649, 16384⟩ := by
  decide +kernel

theorem context_13_440501_856567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440501 ⟨856567, by decide⟩ :=
  accepted_of_selected 13 440501 ⟨856567, by decide⟩ ⟨13, 2, 0, 856567, 440501, 2649, 16384⟩
    (by decide) selected_cut_33257

theorem selected_cut_33258 : selected 8 ⟨856592, by decide⟩
    (prefixPartial 13 440502) = some ⟨13, 2, 0, 856592, 440502, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_440502_856592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440502 ⟨856592, by decide⟩ :=
  accepted_of_selected 13 440502 ⟨856592, by decide⟩ ⟨13, 2, 0, 856592, 440502, 1649, 16384⟩
    (by decide) selected_cut_33258

theorem selected_cut_33259 : selected 8 ⟨856604, by decide⟩
    (prefixPartial 13 440503) = some ⟨13, 2, 0, 856604, 440503, 781, 16384⟩ := by
  decide +kernel

theorem context_13_440503_856604 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440503 ⟨856604, by decide⟩ :=
  accepted_of_selected 13 440503 ⟨856604, by decide⟩ ⟨13, 2, 0, 856604, 440503, 781, 16384⟩
    (by decide) selected_cut_33259

theorem unmarked_context_12_110125_856605 : frontier 9 ⟨856605, by decide⟩
    (prefixCache 12 110125) (prefixPartial 12 110125) = false := by
  decide +kernel

theorem node_context_12_110125_856605 : EJMOriginalGlobalDAGData.nodes 9 ⟨856605, by decide⟩ =
    .split (coordinate 12) (![⟨856532, by decide⟩,⟨856567, by decide⟩,⟨856592, by decide⟩,⟨856604, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110125_856605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110125 ⟨856605, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110125
    ⟨856605, by decide⟩ (by decide) (![⟨856532, by decide⟩,⟨856567, by decide⟩,⟨856592, by decide⟩,⟨856604, by decide⟩]) unmarked_context_12_110125_856605 node_context_12_110125_856605
  intro a
  fin_cases a
  · exact context_13_440500_856532
  · exact context_13_440501_856567
  · exact context_13_440502_856592
  · exact context_13_440503_856604

theorem selected_cut_33260 : selected 8 ⟨856611, by decide⟩
    (prefixPartial 13 440504) = some ⟨13, 2, 0, 856611, 440504, 433, 16384⟩ := by
  decide +kernel

theorem context_13_440504_856611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440504 ⟨856611, by decide⟩ :=
  accepted_of_selected 13 440504 ⟨856611, by decide⟩ ⟨13, 2, 0, 856611, 440504, 433, 16384⟩
    (by decide) selected_cut_33260

theorem selected_cut_33261 : selected 8 ⟨856632, by decide⟩
    (prefixPartial 13 440505) = some ⟨13, 2, 0, 856632, 440505, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_440505_856632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440505 ⟨856632, by decide⟩ :=
  accepted_of_selected 13 440505 ⟨856632, by decide⟩ ⟨13, 2, 0, 856632, 440505, 1957, 16384⟩
    (by decide) selected_cut_33261

theorem selected_cut_33262 : selected 8 ⟨856650, by decide⟩
    (prefixPartial 13 440506) = some ⟨13, 2, 0, 856650, 440506, 1133, 16384⟩ := by
  decide +kernel

theorem context_13_440506_856650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440506 ⟨856650, by decide⟩ :=
  accepted_of_selected 13 440506 ⟨856650, by decide⟩ ⟨13, 2, 0, 856650, 440506, 1133, 16384⟩
    (by decide) selected_cut_33262

theorem selected_cut_33263 : selected 8 ⟨856658, by decide⟩
    (prefixPartial 13 440507) = some ⟨13, 2, 0, 856658, 440507, 757, 16384⟩ := by
  decide +kernel

theorem context_13_440507_856658 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440507 ⟨856658, by decide⟩ :=
  accepted_of_selected 13 440507 ⟨856658, by decide⟩ ⟨13, 2, 0, 856658, 440507, 757, 16384⟩
    (by decide) selected_cut_33263

theorem unmarked_context_12_110126_856659 : frontier 9 ⟨856659, by decide⟩
    (prefixCache 12 110126) (prefixPartial 12 110126) = false := by
  decide +kernel

theorem node_context_12_110126_856659 : EJMOriginalGlobalDAGData.nodes 9 ⟨856659, by decide⟩ =
    .split (coordinate 12) (![⟨856611, by decide⟩,⟨856632, by decide⟩,⟨856650, by decide⟩,⟨856658, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110126_856659 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110126 ⟨856659, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110126
    ⟨856659, by decide⟩ (by decide) (![⟨856611, by decide⟩,⟨856632, by decide⟩,⟨856650, by decide⟩,⟨856658, by decide⟩]) unmarked_context_12_110126_856659 node_context_12_110126_856659
  intro a
  fin_cases a
  · exact context_13_440504_856611
  · exact context_13_440505_856632
  · exact context_13_440506_856650
  · exact context_13_440507_856658

theorem selected_cut_33264 : selected 8 ⟨856670, by decide⟩
    (prefixPartial 13 440508) = some ⟨13, 2, 0, 856670, 440508, 593, 16384⟩ := by
  decide +kernel

theorem context_13_440508_856670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440508 ⟨856670, by decide⟩ :=
  accepted_of_selected 13 440508 ⟨856670, by decide⟩ ⟨13, 2, 0, 856670, 440508, 593, 16384⟩
    (by decide) selected_cut_33264

theorem selected_cut_33265 : selected 8 ⟨856712, by decide⟩
    (prefixPartial 13 440509) = some ⟨13, 2, 0, 856712, 440509, 2789, 16384⟩ := by
  decide +kernel

theorem context_13_440509_856712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440509 ⟨856712, by decide⟩ :=
  accepted_of_selected 13 440509 ⟨856712, by decide⟩ ⟨13, 2, 0, 856712, 440509, 2789, 16384⟩
    (by decide) selected_cut_33265

theorem selected_cut_33266 : selected 8 ⟨856731, by decide⟩
    (prefixPartial 13 440510) = some ⟨13, 2, 0, 856731, 440510, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_440510_856731 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440510 ⟨856731, by decide⟩ :=
  accepted_of_selected 13 440510 ⟨856731, by decide⟩ ⟨13, 2, 0, 856731, 440510, 1617, 16384⟩
    (by decide) selected_cut_33266

theorem selected_cut_33267 : selected 8 ⟨856745, by decide⟩
    (prefixPartial 13 440511) = some ⟨13, 2, 0, 856745, 440511, 893, 16384⟩ := by
  decide +kernel

theorem context_13_440511_856745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440511 ⟨856745, by decide⟩ :=
  accepted_of_selected 13 440511 ⟨856745, by decide⟩ ⟨13, 2, 0, 856745, 440511, 893, 16384⟩
    (by decide) selected_cut_33267

theorem unmarked_context_12_110127_856746 : frontier 9 ⟨856746, by decide⟩
    (prefixCache 12 110127) (prefixPartial 12 110127) = false := by
  decide +kernel

theorem node_context_12_110127_856746 : EJMOriginalGlobalDAGData.nodes 9 ⟨856746, by decide⟩ =
    .split (coordinate 12) (![⟨856670, by decide⟩,⟨856712, by decide⟩,⟨856731, by decide⟩,⟨856745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110127_856746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110127 ⟨856746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110127
    ⟨856746, by decide⟩ (by decide) (![⟨856670, by decide⟩,⟨856712, by decide⟩,⟨856731, by decide⟩,⟨856745, by decide⟩]) unmarked_context_12_110127_856746 node_context_12_110127_856746
  intro a
  fin_cases a
  · exact context_13_440508_856670
  · exact context_13_440509_856712
  · exact context_13_440510_856731
  · exact context_13_440511_856745

theorem unmarked_context_11_27531_856747 : frontier 10 ⟨856747, by decide⟩
    (prefixCache 11 27531) (prefixPartial 11 27531) = false := by
  decide +kernel

theorem node_context_11_27531_856747 : EJMOriginalGlobalDAGData.nodes 10 ⟨856747, by decide⟩ =
    .split (coordinate 11) (![⟨856518, by decide⟩,⟨856605, by decide⟩,⟨856659, by decide⟩,⟨856746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27531_856747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27531 ⟨856747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27531
    ⟨856747, by decide⟩ (by decide) (![⟨856518, by decide⟩,⟨856605, by decide⟩,⟨856659, by decide⟩,⟨856746, by decide⟩]) unmarked_context_11_27531_856747 node_context_11_27531_856747
  intro a
  fin_cases a
  · exact context_12_110124_856518
  · exact context_12_110125_856605
  · exact context_12_110126_856659
  · exact context_12_110127_856746

theorem unmarked_context_10_6882_856748 : frontier 11 ⟨856748, by decide⟩
    (prefixCache 10 6882) (prefixPartial 10 6882) = false := by
  decide +kernel

theorem node_context_10_6882_856748 : EJMOriginalGlobalDAGData.nodes 11 ⟨856748, by decide⟩ =
    .split (coordinate 10) (![⟨855937, by decide⟩,⟨856266, by decide⟩,⟨856460, by decide⟩,⟨856747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6882_856748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6882 ⟨856748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6882
    ⟨856748, by decide⟩ (by decide) (![⟨855937, by decide⟩,⟨856266, by decide⟩,⟨856460, by decide⟩,⟨856747, by decide⟩]) unmarked_context_10_6882_856748 node_context_10_6882_856748
  intro a
  fin_cases a
  · exact context_11_27528_855937
  · exact context_11_27529_856266
  · exact context_11_27530_856460
  · exact context_11_27531_856747

theorem selected_cut_33268 : selected 8 ⟨856762, by decide⟩
    (prefixPartial 13 440512) = some ⟨13, 2, 0, 856762, 440512, 721, 16384⟩ := by
  decide +kernel

theorem context_13_440512_856762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440512 ⟨856762, by decide⟩ :=
  accepted_of_selected 13 440512 ⟨856762, by decide⟩ ⟨13, 2, 0, 856762, 440512, 721, 16384⟩
    (by decide) selected_cut_33268

theorem selected_cut_33269 : selected 8 ⟨856795, by decide⟩
    (prefixPartial 13 440513) = some ⟨13, 2, 0, 856795, 440513, 2557, 16384⟩ := by
  decide +kernel

theorem context_13_440513_856795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440513 ⟨856795, by decide⟩ :=
  accepted_of_selected 13 440513 ⟨856795, by decide⟩ ⟨13, 2, 0, 856795, 440513, 2557, 16384⟩
    (by decide) selected_cut_33269

theorem selected_cut_33270 : selected 8 ⟨856814, by decide⟩
    (prefixPartial 13 440514) = some ⟨13, 2, 0, 856814, 440514, 1417, 16384⟩ := by
  decide +kernel

theorem context_13_440514_856814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440514 ⟨856814, by decide⟩ :=
  accepted_of_selected 13 440514 ⟨856814, by decide⟩ ⟨13, 2, 0, 856814, 440514, 1417, 16384⟩
    (by decide) selected_cut_33270

theorem selected_cut_33271 : selected 8 ⟨856821, by decide⟩
    (prefixPartial 13 440515) = some ⟨13, 2, 0, 856821, 440515, 645, 16384⟩ := by
  decide +kernel

theorem context_13_440515_856821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440515 ⟨856821, by decide⟩ :=
  accepted_of_selected 13 440515 ⟨856821, by decide⟩ ⟨13, 2, 0, 856821, 440515, 645, 16384⟩
    (by decide) selected_cut_33271

theorem unmarked_context_12_110128_856822 : frontier 9 ⟨856822, by decide⟩
    (prefixCache 12 110128) (prefixPartial 12 110128) = false := by
  decide +kernel

theorem node_context_12_110128_856822 : EJMOriginalGlobalDAGData.nodes 9 ⟨856822, by decide⟩ =
    .split (coordinate 12) (![⟨856762, by decide⟩,⟨856795, by decide⟩,⟨856814, by decide⟩,⟨856821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110128_856822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110128 ⟨856822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110128
    ⟨856822, by decide⟩ (by decide) (![⟨856762, by decide⟩,⟨856795, by decide⟩,⟨856814, by decide⟩,⟨856821, by decide⟩]) unmarked_context_12_110128_856822 node_context_12_110128_856822
  intro a
  fin_cases a
  · exact context_13_440512_856762
  · exact context_13_440513_856795
  · exact context_13_440514_856814
  · exact context_13_440515_856821

theorem selected_cut_33272 : selected 8 ⟨856828, by decide⟩
    (prefixPartial 13 440516) = some ⟨13, 2, 0, 856828, 440516, 569, 16384⟩ := by
  decide +kernel

theorem context_13_440516_856828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440516 ⟨856828, by decide⟩ :=
  accepted_of_selected 13 440516 ⟨856828, by decide⟩ ⟨13, 2, 0, 856828, 440516, 569, 16384⟩
    (by decide) selected_cut_33272

theorem selected_cut_33273 : selected 8 ⟨856858, by decide⟩
    (prefixPartial 13 440517) = some ⟨13, 2, 0, 856858, 440517, 2509, 16384⟩ := by
  decide +kernel

theorem context_13_440517_856858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440517 ⟨856858, by decide⟩ :=
  accepted_of_selected 13 440517 ⟨856858, by decide⟩ ⟨13, 2, 0, 856858, 440517, 2509, 16384⟩
    (by decide) selected_cut_33273

theorem selected_cut_33274 : selected 8 ⟨856879, by decide⟩
    (prefixPartial 13 440518) = some ⟨13, 2, 0, 856879, 440518, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_440518_856879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440518 ⟨856879, by decide⟩ :=
  accepted_of_selected 13 440518 ⟨856879, by decide⟩ ⟨13, 2, 0, 856879, 440518, 1549, 16384⟩
    (by decide) selected_cut_33274

theorem selected_cut_33275 : selected 8 ⟨856886, by decide⟩
    (prefixPartial 13 440519) = some ⟨13, 2, 0, 856886, 440519, 805, 16384⟩ := by
  decide +kernel

theorem context_13_440519_856886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440519 ⟨856886, by decide⟩ :=
  accepted_of_selected 13 440519 ⟨856886, by decide⟩ ⟨13, 2, 0, 856886, 440519, 805, 16384⟩
    (by decide) selected_cut_33275

theorem unmarked_context_12_110129_856887 : frontier 9 ⟨856887, by decide⟩
    (prefixCache 12 110129) (prefixPartial 12 110129) = false := by
  decide +kernel

theorem node_context_12_110129_856887 : EJMOriginalGlobalDAGData.nodes 9 ⟨856887, by decide⟩ =
    .split (coordinate 12) (![⟨856828, by decide⟩,⟨856858, by decide⟩,⟨856879, by decide⟩,⟨856886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110129_856887 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110129 ⟨856887, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110129
    ⟨856887, by decide⟩ (by decide) (![⟨856828, by decide⟩,⟨856858, by decide⟩,⟨856879, by decide⟩,⟨856886, by decide⟩]) unmarked_context_12_110129_856887 node_context_12_110129_856887
  intro a
  fin_cases a
  · exact context_13_440516_856828
  · exact context_13_440517_856858
  · exact context_13_440518_856879
  · exact context_13_440519_856886

theorem selected_cut_33276 : selected 8 ⟨856893, by decide⟩
    (prefixPartial 13 440520) = some ⟨13, 2, 0, 856893, 440520, 401, 16384⟩ := by
  decide +kernel

theorem context_13_440520_856893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440520 ⟨856893, by decide⟩ :=
  accepted_of_selected 13 440520 ⟨856893, by decide⟩ ⟨13, 2, 0, 856893, 440520, 401, 16384⟩
    (by decide) selected_cut_33276

theorem selected_cut_33277 : selected 8 ⟨856913, by decide⟩
    (prefixPartial 13 440521) = some ⟨13, 2, 0, 856913, 440521, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_440521_856913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440521 ⟨856913, by decide⟩ :=
  accepted_of_selected 13 440521 ⟨856913, by decide⟩ ⟨13, 2, 0, 856913, 440521, 2057, 16384⟩
    (by decide) selected_cut_33277

theorem selected_cut_33278 : selected 8 ⟨856930, by decide⟩
    (prefixPartial 13 440522) = some ⟨13, 2, 0, 856930, 440522, 965, 16384⟩ := by
  decide +kernel

theorem context_13_440522_856930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440522 ⟨856930, by decide⟩ :=
  accepted_of_selected 13 440522 ⟨856930, by decide⟩ ⟨13, 2, 0, 856930, 440522, 965, 16384⟩
    (by decide) selected_cut_33278

theorem selected_cut_33279 : selected 8 ⟨856937, by decide⟩
    (prefixPartial 13 440523) = some ⟨13, 2, 0, 856937, 440523, 757, 16384⟩ := by
  decide +kernel

theorem context_13_440523_856937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440523 ⟨856937, by decide⟩ :=
  accepted_of_selected 13 440523 ⟨856937, by decide⟩ ⟨13, 2, 0, 856937, 440523, 757, 16384⟩
    (by decide) selected_cut_33279

theorem unmarked_context_12_110130_856938 : frontier 9 ⟨856938, by decide⟩
    (prefixCache 12 110130) (prefixPartial 12 110130) = false := by
  decide +kernel

theorem node_context_12_110130_856938 : EJMOriginalGlobalDAGData.nodes 9 ⟨856938, by decide⟩ =
    .split (coordinate 12) (![⟨856893, by decide⟩,⟨856913, by decide⟩,⟨856930, by decide⟩,⟨856937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110130_856938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110130 ⟨856938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110130
    ⟨856938, by decide⟩ (by decide) (![⟨856893, by decide⟩,⟨856913, by decide⟩,⟨856930, by decide⟩,⟨856937, by decide⟩]) unmarked_context_12_110130_856938 node_context_12_110130_856938
  intro a
  fin_cases a
  · exact context_13_440520_856893
  · exact context_13_440521_856913
  · exact context_13_440522_856930
  · exact context_13_440523_856937

theorem selected_cut_33280 : selected 8 ⟨856947, by decide⟩
    (prefixPartial 13 440524) = some ⟨13, 2, 0, 856947, 440524, 517, 16384⟩ := by
  decide +kernel

theorem context_13_440524_856947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440524 ⟨856947, by decide⟩ :=
  accepted_of_selected 13 440524 ⟨856947, by decide⟩ ⟨13, 2, 0, 856947, 440524, 517, 16384⟩
    (by decide) selected_cut_33280

theorem selected_cut_33281 : selected 8 ⟨856994, by decide⟩
    (prefixPartial 13 440525) = some ⟨13, 2, 0, 856994, 440525, 3137, 16384⟩ := by
  decide +kernel

theorem context_13_440525_856994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440525 ⟨856994, by decide⟩ :=
  accepted_of_selected 13 440525 ⟨856994, by decide⟩ ⟨13, 2, 0, 856994, 440525, 3137, 16384⟩
    (by decide) selected_cut_33281

theorem selected_cut_33282 : selected 8 ⟨857016, by decide⟩
    (prefixPartial 13 440526) = some ⟨13, 2, 0, 857016, 440526, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_440526_857016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440526 ⟨857016, by decide⟩ :=
  accepted_of_selected 13 440526 ⟨857016, by decide⟩ ⟨13, 2, 0, 857016, 440526, 1537, 16384⟩
    (by decide) selected_cut_33282

theorem selected_cut_33283 : selected 8 ⟨857020, by decide⟩
    (prefixPartial 13 440527) = some ⟨13, 2, 0, 857020, 440527, 833, 16384⟩ := by
  decide +kernel

theorem context_13_440527_857020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440527 ⟨857020, by decide⟩ :=
  accepted_of_selected 13 440527 ⟨857020, by decide⟩ ⟨13, 2, 0, 857020, 440527, 833, 16384⟩
    (by decide) selected_cut_33283

theorem unmarked_context_12_110131_857021 : frontier 9 ⟨857021, by decide⟩
    (prefixCache 12 110131) (prefixPartial 12 110131) = false := by
  decide +kernel

theorem node_context_12_110131_857021 : EJMOriginalGlobalDAGData.nodes 9 ⟨857021, by decide⟩ =
    .split (coordinate 12) (![⟨856947, by decide⟩,⟨856994, by decide⟩,⟨857016, by decide⟩,⟨857020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110131_857021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110131 ⟨857021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110131
    ⟨857021, by decide⟩ (by decide) (![⟨856947, by decide⟩,⟨856994, by decide⟩,⟨857016, by decide⟩,⟨857020, by decide⟩]) unmarked_context_12_110131_857021 node_context_12_110131_857021
  intro a
  fin_cases a
  · exact context_13_440524_856947
  · exact context_13_440525_856994
  · exact context_13_440526_857016
  · exact context_13_440527_857020

theorem unmarked_context_11_27532_857022 : frontier 10 ⟨857022, by decide⟩
    (prefixCache 11 27532) (prefixPartial 11 27532) = false := by
  decide +kernel

theorem node_context_11_27532_857022 : EJMOriginalGlobalDAGData.nodes 10 ⟨857022, by decide⟩ =
    .split (coordinate 11) (![⟨856822, by decide⟩,⟨856887, by decide⟩,⟨856938, by decide⟩,⟨857021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27532_857022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27532 ⟨857022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27532
    ⟨857022, by decide⟩ (by decide) (![⟨856822, by decide⟩,⟨856887, by decide⟩,⟨856938, by decide⟩,⟨857021, by decide⟩]) unmarked_context_11_27532_857022 node_context_11_27532_857022
  intro a
  fin_cases a
  · exact context_12_110128_856822
  · exact context_12_110129_856887
  · exact context_12_110130_856938
  · exact context_12_110131_857021

theorem selected_cut_33284 : selected 8 ⟨857032, by decide⟩
    (prefixPartial 13 440528) = some ⟨13, 2, 0, 857032, 440528, 481, 16384⟩ := by
  decide +kernel

theorem context_13_440528_857032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440528 ⟨857032, by decide⟩ :=
  accepted_of_selected 13 440528 ⟨857032, by decide⟩ ⟨13, 2, 0, 857032, 440528, 481, 16384⟩
    (by decide) selected_cut_33284

theorem selected_cut_33285 : selected 8 ⟨857076, by decide⟩
    (prefixPartial 13 440529) = some ⟨13, 2, 0, 857076, 440529, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_440529_857076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440529 ⟨857076, by decide⟩ :=
  accepted_of_selected 13 440529 ⟨857076, by decide⟩ ⟨13, 2, 0, 857076, 440529, 2693, 16384⟩
    (by decide) selected_cut_33285

theorem selected_cut_33286 : selected 8 ⟨857103, by decide⟩
    (prefixPartial 13 440530) = some ⟨13, 2, 0, 857103, 440530, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_440530_857103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440530 ⟨857103, by decide⟩ :=
  accepted_of_selected 13 440530 ⟨857103, by decide⟩ ⟨13, 2, 0, 857103, 440530, 1477, 16384⟩
    (by decide) selected_cut_33286

theorem selected_cut_33287 : selected 8 ⟨857110, by decide⟩
    (prefixPartial 13 440531) = some ⟨13, 2, 0, 857110, 440531, 641, 16384⟩ := by
  decide +kernel

theorem context_13_440531_857110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440531 ⟨857110, by decide⟩ :=
  accepted_of_selected 13 440531 ⟨857110, by decide⟩ ⟨13, 2, 0, 857110, 440531, 641, 16384⟩
    (by decide) selected_cut_33287

theorem unmarked_context_12_110132_857111 : frontier 9 ⟨857111, by decide⟩
    (prefixCache 12 110132) (prefixPartial 12 110132) = false := by
  decide +kernel

theorem node_context_12_110132_857111 : EJMOriginalGlobalDAGData.nodes 9 ⟨857111, by decide⟩ =
    .split (coordinate 12) (![⟨857032, by decide⟩,⟨857076, by decide⟩,⟨857103, by decide⟩,⟨857110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110132_857111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110132 ⟨857111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110132
    ⟨857111, by decide⟩ (by decide) (![⟨857032, by decide⟩,⟨857076, by decide⟩,⟨857103, by decide⟩,⟨857110, by decide⟩]) unmarked_context_12_110132_857111 node_context_12_110132_857111
  intro a
  fin_cases a
  · exact context_13_440528_857032
  · exact context_13_440529_857076
  · exact context_13_440530_857103
  · exact context_13_440531_857110

theorem selected_cut_33288 : selected 8 ⟨857118, by decide⟩
    (prefixPartial 13 440532) = some ⟨13, 2, 0, 857118, 440532, 373, 16384⟩ := by
  decide +kernel

theorem context_13_440532_857118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440532 ⟨857118, by decide⟩ :=
  accepted_of_selected 13 440532 ⟨857118, by decide⟩ ⟨13, 2, 0, 857118, 440532, 373, 16384⟩
    (by decide) selected_cut_33288

theorem selected_cut_33289 : selected 8 ⟨857144, by decide⟩
    (prefixPartial 13 440533) = some ⟨13, 2, 0, 857144, 440533, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_440533_857144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440533 ⟨857144, by decide⟩ :=
  accepted_of_selected 13 440533 ⟨857144, by decide⟩ ⟨13, 2, 0, 857144, 440533, 2273, 16384⟩
    (by decide) selected_cut_33289

theorem selected_cut_33290 : selected 8 ⟨857164, by decide⟩
    (prefixPartial 13 440534) = some ⟨13, 2, 0, 857164, 440534, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_440534_857164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440534 ⟨857164, by decide⟩ :=
  accepted_of_selected 13 440534 ⟨857164, by decide⟩ ⟨13, 2, 0, 857164, 440534, 1601, 16384⟩
    (by decide) selected_cut_33290

theorem selected_cut_33291 : selected 8 ⟨857172, by decide⟩
    (prefixPartial 13 440535) = some ⟨13, 2, 0, 857172, 440535, 697, 16384⟩ := by
  decide +kernel

theorem context_13_440535_857172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440535 ⟨857172, by decide⟩ :=
  accepted_of_selected 13 440535 ⟨857172, by decide⟩ ⟨13, 2, 0, 857172, 440535, 697, 16384⟩
    (by decide) selected_cut_33291

theorem unmarked_context_12_110133_857173 : frontier 9 ⟨857173, by decide⟩
    (prefixCache 12 110133) (prefixPartial 12 110133) = false := by
  decide +kernel

theorem node_context_12_110133_857173 : EJMOriginalGlobalDAGData.nodes 9 ⟨857173, by decide⟩ =
    .split (coordinate 12) (![⟨857118, by decide⟩,⟨857144, by decide⟩,⟨857164, by decide⟩,⟨857172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110133_857173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110133 ⟨857173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110133
    ⟨857173, by decide⟩ (by decide) (![⟨857118, by decide⟩,⟨857144, by decide⟩,⟨857164, by decide⟩,⟨857172, by decide⟩]) unmarked_context_12_110133_857173 node_context_12_110133_857173
  intro a
  fin_cases a
  · exact context_13_440532_857118
  · exact context_13_440533_857144
  · exact context_13_440534_857164
  · exact context_13_440535_857172

theorem selected_cut_33292 : selected 9 ⟨857228, by decide⟩
    (prefixPartial 12 110134) = some ⟨12, 2, 0, 857228, 110134, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_110134_857228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110134 ⟨857228, by decide⟩ :=
  accepted_of_selected 12 110134 ⟨857228, by decide⟩ ⟨12, 2, 0, 857228, 110134, 3917, 65536⟩
    (by decide) selected_cut_33292

theorem selected_cut_33293 : selected 8 ⟨857235, by decide⟩
    (prefixPartial 13 440540) = some ⟨13, 2, 0, 857235, 440540, 329, 16384⟩ := by
  decide +kernel

theorem context_13_440540_857235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440540 ⟨857235, by decide⟩ :=
  accepted_of_selected 13 440540 ⟨857235, by decide⟩ ⟨13, 2, 0, 857235, 440540, 329, 16384⟩
    (by decide) selected_cut_33293

theorem selected_cut_33294 : selected 8 ⟨857280, by decide⟩
    (prefixPartial 13 440541) = some ⟨13, 2, 0, 857280, 440541, 2977, 16384⟩ := by
  decide +kernel

theorem context_13_440541_857280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440541 ⟨857280, by decide⟩ :=
  accepted_of_selected 13 440541 ⟨857280, by decide⟩ ⟨13, 2, 0, 857280, 440541, 2977, 16384⟩
    (by decide) selected_cut_33294

theorem selected_cut_33295 : selected 8 ⟨857311, by decide⟩
    (prefixPartial 13 440542) = some ⟨13, 2, 0, 857311, 440542, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_440542_857311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440542 ⟨857311, by decide⟩ :=
  accepted_of_selected 13 440542 ⟨857311, by decide⟩ ⟨13, 2, 0, 857311, 440542, 1729, 16384⟩
    (by decide) selected_cut_33295

theorem selected_cut_33296 : selected 8 ⟨857316, by decide⟩
    (prefixPartial 13 440543) = some ⟨13, 2, 0, 857316, 440543, 781, 16384⟩ := by
  decide +kernel

theorem context_13_440543_857316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440543 ⟨857316, by decide⟩ :=
  accepted_of_selected 13 440543 ⟨857316, by decide⟩ ⟨13, 2, 0, 857316, 440543, 781, 16384⟩
    (by decide) selected_cut_33296

theorem unmarked_context_12_110135_857317 : frontier 9 ⟨857317, by decide⟩
    (prefixCache 12 110135) (prefixPartial 12 110135) = false := by
  decide +kernel

theorem node_context_12_110135_857317 : EJMOriginalGlobalDAGData.nodes 9 ⟨857317, by decide⟩ =
    .split (coordinate 12) (![⟨857235, by decide⟩,⟨857280, by decide⟩,⟨857311, by decide⟩,⟨857316, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110135_857317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110135 ⟨857317, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110135
    ⟨857317, by decide⟩ (by decide) (![⟨857235, by decide⟩,⟨857280, by decide⟩,⟨857311, by decide⟩,⟨857316, by decide⟩]) unmarked_context_12_110135_857317 node_context_12_110135_857317
  intro a
  fin_cases a
  · exact context_13_440540_857235
  · exact context_13_440541_857280
  · exact context_13_440542_857311
  · exact context_13_440543_857316

theorem unmarked_context_11_27533_857318 : frontier 10 ⟨857318, by decide⟩
    (prefixCache 11 27533) (prefixPartial 11 27533) = false := by
  decide +kernel

theorem node_context_11_27533_857318 : EJMOriginalGlobalDAGData.nodes 10 ⟨857318, by decide⟩ =
    .split (coordinate 11) (![⟨857111, by decide⟩,⟨857173, by decide⟩,⟨857228, by decide⟩,⟨857317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27533_857318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27533 ⟨857318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27533
    ⟨857318, by decide⟩ (by decide) (![⟨857111, by decide⟩,⟨857173, by decide⟩,⟨857228, by decide⟩,⟨857317, by decide⟩]) unmarked_context_11_27533_857318 node_context_11_27533_857318
  intro a
  fin_cases a
  · exact context_12_110132_857111
  · exact context_12_110133_857173
  · exact context_12_110134_857228
  · exact context_12_110135_857317

theorem selected_cut_33297 : selected 8 ⟨857321, by decide⟩
    (prefixPartial 13 440544) = some ⟨13, 2, 0, 857321, 440544, 129, 16384⟩ := by
  decide +kernel

theorem context_13_440544_857321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440544 ⟨857321, by decide⟩ :=
  accepted_of_selected 13 440544 ⟨857321, by decide⟩ ⟨13, 2, 0, 857321, 440544, 129, 16384⟩
    (by decide) selected_cut_33297

theorem selected_cut_33298 : selected 8 ⟨857345, by decide⟩
    (prefixPartial 13 440545) = some ⟨13, 2, 0, 857345, 440545, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_440545_857345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440545 ⟨857345, by decide⟩ :=
  accepted_of_selected 13 440545 ⟨857345, by decide⟩ ⟨13, 2, 0, 857345, 440545, 2277, 16384⟩
    (by decide) selected_cut_33298

theorem selected_cut_33299 : selected 8 ⟨857367, by decide⟩
    (prefixPartial 13 440546) = some ⟨13, 2, 0, 857367, 440546, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_440546_857367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440546 ⟨857367, by decide⟩ :=
  accepted_of_selected 13 440546 ⟨857367, by decide⟩ ⟨13, 2, 0, 857367, 440546, 1453, 16384⟩
    (by decide) selected_cut_33299

theorem selected_cut_33300 : selected 8 ⟨857373, by decide⟩
    (prefixPartial 13 440547) = some ⟨13, 2, 0, 857373, 440547, 565, 16384⟩ := by
  decide +kernel

theorem context_13_440547_857373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440547 ⟨857373, by decide⟩ :=
  accepted_of_selected 13 440547 ⟨857373, by decide⟩ ⟨13, 2, 0, 857373, 440547, 565, 16384⟩
    (by decide) selected_cut_33300

theorem unmarked_context_12_110136_857374 : frontier 9 ⟨857374, by decide⟩
    (prefixCache 12 110136) (prefixPartial 12 110136) = false := by
  decide +kernel

theorem node_context_12_110136_857374 : EJMOriginalGlobalDAGData.nodes 9 ⟨857374, by decide⟩ =
    .split (coordinate 12) (![⟨857321, by decide⟩,⟨857345, by decide⟩,⟨857367, by decide⟩,⟨857373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110136_857374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110136 ⟨857374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110136
    ⟨857374, by decide⟩ (by decide) (![⟨857321, by decide⟩,⟨857345, by decide⟩,⟨857367, by decide⟩,⟨857373, by decide⟩]) unmarked_context_12_110136_857374 node_context_12_110136_857374
  intro a
  fin_cases a
  · exact context_13_440544_857321
  · exact context_13_440545_857345
  · exact context_13_440546_857367
  · exact context_13_440547_857373

theorem selected_cut_33301 : selected 8 ⟨857379, by decide⟩
    (prefixPartial 13 440548) = some ⟨13, 2, 0, 857379, 440548, 113, 16384⟩ := by
  decide +kernel

theorem context_13_440548_857379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440548 ⟨857379, by decide⟩ :=
  accepted_of_selected 13 440548 ⟨857379, by decide⟩ ⟨13, 2, 0, 857379, 440548, 113, 16384⟩
    (by decide) selected_cut_33301

theorem selected_cut_33302 : selected 8 ⟨857399, by decide⟩
    (prefixPartial 13 440549) = some ⟨13, 2, 0, 857399, 440549, 1913, 16384⟩ := by
  decide +kernel

theorem context_13_440549_857399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440549 ⟨857399, by decide⟩ :=
  accepted_of_selected 13 440549 ⟨857399, by decide⟩ ⟨13, 2, 0, 857399, 440549, 1913, 16384⟩
    (by decide) selected_cut_33302

theorem selected_cut_33303 : selected 8 ⟨857413, by decide⟩
    (prefixPartial 13 440550) = some ⟨13, 2, 0, 857413, 440550, 1605, 16384⟩ := by
  decide +kernel

theorem context_13_440550_857413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440550 ⟨857413, by decide⟩ :=
  accepted_of_selected 13 440550 ⟨857413, by decide⟩ ⟨13, 2, 0, 857413, 440550, 1605, 16384⟩
    (by decide) selected_cut_33303

theorem selected_cut_33304 : selected 8 ⟨857420, by decide⟩
    (prefixPartial 13 440551) = some ⟨13, 2, 0, 857420, 440551, 637, 16384⟩ := by
  decide +kernel

theorem context_13_440551_857420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440551 ⟨857420, by decide⟩ :=
  accepted_of_selected 13 440551 ⟨857420, by decide⟩ ⟨13, 2, 0, 857420, 440551, 637, 16384⟩
    (by decide) selected_cut_33304

theorem unmarked_context_12_110137_857421 : frontier 9 ⟨857421, by decide⟩
    (prefixCache 12 110137) (prefixPartial 12 110137) = false := by
  decide +kernel

theorem node_context_12_110137_857421 : EJMOriginalGlobalDAGData.nodes 9 ⟨857421, by decide⟩ =
    .split (coordinate 12) (![⟨857379, by decide⟩,⟨857399, by decide⟩,⟨857413, by decide⟩,⟨857420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110137_857421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110137 ⟨857421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110137
    ⟨857421, by decide⟩ (by decide) (![⟨857379, by decide⟩,⟨857399, by decide⟩,⟨857413, by decide⟩,⟨857420, by decide⟩]) unmarked_context_12_110137_857421 node_context_12_110137_857421
  intro a
  fin_cases a
  · exact context_13_440548_857379
  · exact context_13_440549_857399
  · exact context_13_440550_857413
  · exact context_13_440551_857420

theorem selected_cut_33305 : selected 9 ⟨662655, by decide⟩
    (prefixPartial 12 110138) = some ⟨12, 1, 0, 662655, 110138, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110138_662655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110138 ⟨662655, by decide⟩ :=
  accepted_of_selected 12 110138 ⟨662655, by decide⟩ ⟨12, 1, 0, 662655, 110138, 1, 65536⟩
    (by decide) selected_cut_33305

theorem selected_cut_33306 : selected 8 ⟨857424, by decide⟩
    (prefixPartial 13 440556) = some ⟨13, 2, 0, 857424, 440556, 49, 16384⟩ := by
  decide +kernel

theorem context_13_440556_857424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440556 ⟨857424, by decide⟩ :=
  accepted_of_selected 13 440556 ⟨857424, by decide⟩ ⟨13, 2, 0, 857424, 440556, 49, 16384⟩
    (by decide) selected_cut_33306

theorem selected_cut_33307 : selected 8 ⟨857457, by decide⟩
    (prefixPartial 13 440557) = some ⟨13, 2, 0, 857457, 440557, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_440557_857457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440557 ⟨857457, by decide⟩ :=
  accepted_of_selected 13 440557 ⟨857457, by decide⟩ ⟨13, 2, 0, 857457, 440557, 2517, 16384⟩
    (by decide) selected_cut_33307

theorem selected_cut_33308 : selected 8 ⟨857470, by decide⟩
    (prefixPartial 13 440558) = some ⟨13, 2, 0, 857470, 440558, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_440558_857470 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440558 ⟨857470, by decide⟩ :=
  accepted_of_selected 13 440558 ⟨857470, by decide⟩ ⟨13, 2, 0, 857470, 440558, 1589, 16384⟩
    (by decide) selected_cut_33308

theorem selected_cut_33309 : selected 8 ⟨857476, by decide⟩
    (prefixPartial 13 440559) = some ⟨13, 2, 0, 857476, 440559, 617, 16384⟩ := by
  decide +kernel

theorem context_13_440559_857476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440559 ⟨857476, by decide⟩ :=
  accepted_of_selected 13 440559 ⟨857476, by decide⟩ ⟨13, 2, 0, 857476, 440559, 617, 16384⟩
    (by decide) selected_cut_33309

theorem unmarked_context_12_110139_857477 : frontier 9 ⟨857477, by decide⟩
    (prefixCache 12 110139) (prefixPartial 12 110139) = false := by
  decide +kernel

theorem node_context_12_110139_857477 : EJMOriginalGlobalDAGData.nodes 9 ⟨857477, by decide⟩ =
    .split (coordinate 12) (![⟨857424, by decide⟩,⟨857457, by decide⟩,⟨857470, by decide⟩,⟨857476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110139_857477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110139 ⟨857477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110139
    ⟨857477, by decide⟩ (by decide) (![⟨857424, by decide⟩,⟨857457, by decide⟩,⟨857470, by decide⟩,⟨857476, by decide⟩]) unmarked_context_12_110139_857477 node_context_12_110139_857477
  intro a
  fin_cases a
  · exact context_13_440556_857424
  · exact context_13_440557_857457
  · exact context_13_440558_857470
  · exact context_13_440559_857476

theorem unmarked_context_11_27534_857478 : frontier 10 ⟨857478, by decide⟩
    (prefixCache 11 27534) (prefixPartial 11 27534) = false := by
  decide +kernel

theorem node_context_11_27534_857478 : EJMOriginalGlobalDAGData.nodes 10 ⟨857478, by decide⟩ =
    .split (coordinate 11) (![⟨857374, by decide⟩,⟨857421, by decide⟩,⟨662655, by decide⟩,⟨857477, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27534_857478 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27534 ⟨857478, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27534
    ⟨857478, by decide⟩ (by decide) (![⟨857374, by decide⟩,⟨857421, by decide⟩,⟨662655, by decide⟩,⟨857477, by decide⟩]) unmarked_context_11_27534_857478 node_context_11_27534_857478
  intro a
  fin_cases a
  · exact context_12_110136_857374
  · exact context_12_110137_857421
  · exact context_12_110138_662655
  · exact context_12_110139_857477

theorem selected_cut_33310 : selected 10 ⟨793294, by decide⟩
    (prefixPartial 11 27535) = some ⟨11, 1, 0, 793294, 27535, 1, 262144⟩ := by
  decide +kernel

theorem context_11_27535_793294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27535 ⟨793294, by decide⟩ :=
  accepted_of_selected 11 27535 ⟨793294, by decide⟩ ⟨11, 1, 0, 793294, 27535, 1, 262144⟩
    (by decide) selected_cut_33310

theorem unmarked_context_10_6883_857479 : frontier 11 ⟨857479, by decide⟩
    (prefixCache 10 6883) (prefixPartial 10 6883) = false := by
  decide +kernel

theorem node_context_10_6883_857479 : EJMOriginalGlobalDAGData.nodes 11 ⟨857479, by decide⟩ =
    .split (coordinate 10) (![⟨857022, by decide⟩,⟨857318, by decide⟩,⟨857478, by decide⟩,⟨793294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6883_857479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6883 ⟨857479, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6883
    ⟨857479, by decide⟩ (by decide) (![⟨857022, by decide⟩,⟨857318, by decide⟩,⟨857478, by decide⟩,⟨793294, by decide⟩]) unmarked_context_10_6883_857479 node_context_10_6883_857479
  intro a
  fin_cases a
  · exact context_11_27532_857022
  · exact context_11_27533_857318
  · exact context_11_27534_857478
  · exact context_11_27535_793294

theorem unmarked_context_9_1720_857480 : frontier 12 ⟨857480, by decide⟩
    (prefixCache 9 1720) (prefixPartial 9 1720) = false := by
  decide +kernel

theorem node_context_9_1720_857480 : EJMOriginalGlobalDAGData.nodes 12 ⟨857480, by decide⟩ =
    .split (coordinate 9) (![⟨854127, by decide⟩,⟨855599, by decide⟩,⟨856748, by decide⟩,⟨857479, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1720_857480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1720 ⟨857480, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1720
    ⟨857480, by decide⟩ (by decide) (![⟨854127, by decide⟩,⟨855599, by decide⟩,⟨856748, by decide⟩,⟨857479, by decide⟩]) unmarked_context_9_1720_857480 node_context_9_1720_857480
  intro a
  fin_cases a
  · exact context_10_6880_854127
  · exact context_10_6881_855599
  · exact context_10_6882_856748
  · exact context_10_6883_857479

theorem selected_cut_33311 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 440576) = some ⟨13, 1, 0, 3444, 440576, 1, 16384⟩ := by
  decide +kernel

theorem context_13_440576_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440576 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 440576 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 440576, 1, 16384⟩
    (by decide) selected_cut_33311

theorem selected_cut_33312 : selected 8 ⟨857539, by decide⟩
    (prefixPartial 13 440577) = some ⟨13, 2, 0, 857539, 440577, 3089, 16384⟩ := by
  decide +kernel

theorem context_13_440577_857539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440577 ⟨857539, by decide⟩ :=
  accepted_of_selected 13 440577 ⟨857539, by decide⟩ ⟨13, 2, 0, 857539, 440577, 3089, 16384⟩
    (by decide) selected_cut_33312

theorem selected_cut_33313 : selected 8 ⟨857571, by decide⟩
    (prefixPartial 13 440578) = some ⟨13, 2, 0, 857571, 440578, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_440578_857571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440578 ⟨857571, by decide⟩ :=
  accepted_of_selected 13 440578 ⟨857571, by decide⟩ ⟨13, 2, 0, 857571, 440578, 1493, 16384⟩
    (by decide) selected_cut_33313

theorem selected_cut_33314 : selected 8 ⟨857576, by decide⟩
    (prefixPartial 13 440579) = some ⟨13, 2, 0, 857576, 440579, 665, 16384⟩ := by
  decide +kernel

theorem context_13_440579_857576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 440579 ⟨857576, by decide⟩ :=
  accepted_of_selected 13 440579 ⟨857576, by decide⟩ ⟨13, 2, 0, 857576, 440579, 665, 16384⟩
    (by decide) selected_cut_33314

theorem unmarked_context_12_110144_857577 : frontier 9 ⟨857577, by decide⟩
    (prefixCache 12 110144) (prefixPartial 12 110144) = false := by
  decide +kernel

theorem node_context_12_110144_857577 : EJMOriginalGlobalDAGData.nodes 9 ⟨857577, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨857539, by decide⟩,⟨857571, by decide⟩,⟨857576, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110144_857577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110144 ⟨857577, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110144
    ⟨857577, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨857539, by decide⟩,⟨857571, by decide⟩,⟨857576, by decide⟩]) unmarked_context_12_110144_857577 node_context_12_110144_857577
  intro a
  fin_cases a
  · exact context_13_440576_3444
  · exact context_13_440577_857539
  · exact context_13_440578_857571
  · exact context_13_440579_857576

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
