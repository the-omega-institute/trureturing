/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover239
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_23043 : selected 9 ⟨583824, by decide⟩
    (prefixPartial 12 76107) = some ⟨12, 2, 0, 583824, 76107, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_76107_583824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76107 ⟨583824, by decide⟩ :=
  accepted_of_selected 12 76107 ⟨583824, by decide⟩ ⟨12, 2, 0, 583824, 76107, 3837, 65536⟩
    (by decide) selected_cut_23043

theorem unmarked_context_11_19026_583825 : frontier 10 ⟨583825, by decide⟩
    (prefixCache 11 19026) (prefixPartial 11 19026) = false := by
  decide +kernel

theorem node_context_11_19026_583825 : EJMOriginalGlobalDAGData.nodes 10 ⟨583825, by decide⟩ =
    .split (coordinate 11) (![⟨583695, by decide⟩,⟨583731, by decide⟩,⟨583781, by decide⟩,⟨583824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19026_583825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19026 ⟨583825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19026
    ⟨583825, by decide⟩ (by decide) (![⟨583695, by decide⟩,⟨583731, by decide⟩,⟨583781, by decide⟩,⟨583824, by decide⟩]) unmarked_context_11_19026_583825 node_context_11_19026_583825
  intro a
  fin_cases a
  · exact context_12_76104_583695
  · exact context_12_76105_583731
  · exact context_12_76106_583781
  · exact context_12_76107_583824

theorem selected_cut_23044 : selected 9 ⟨583867, by decide⟩
    (prefixPartial 12 76108) = some ⟨12, 2, 0, 583867, 76108, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_76108_583867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76108 ⟨583867, by decide⟩ :=
  accepted_of_selected 12 76108 ⟨583867, by decide⟩ ⟨12, 2, 0, 583867, 76108, 3557, 65536⟩
    (by decide) selected_cut_23044

theorem selected_cut_23045 : selected 9 ⟨583904, by decide⟩
    (prefixPartial 12 76109) = some ⟨12, 2, 0, 583904, 76109, 3033, 65536⟩ := by
  decide +kernel

theorem context_12_76109_583904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76109 ⟨583904, by decide⟩ :=
  accepted_of_selected 12 76109 ⟨583904, by decide⟩ ⟨12, 2, 0, 583904, 76109, 3033, 65536⟩
    (by decide) selected_cut_23045

theorem selected_cut_23046 : selected 9 ⟨583949, by decide⟩
    (prefixPartial 12 76110) = some ⟨12, 2, 0, 583949, 76110, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_76110_583949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76110 ⟨583949, by decide⟩ :=
  accepted_of_selected 12 76110 ⟨583949, by decide⟩ ⟨12, 2, 0, 583949, 76110, 4089, 65536⟩
    (by decide) selected_cut_23046

theorem selected_cut_23047 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304444) = some ⟨13, 1, 0, 3444, 304444, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304444_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304444 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304444 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304444, 1, 16384⟩
    (by decide) selected_cut_23047

theorem selected_cut_23048 : selected 8 ⟨583969, by decide⟩
    (prefixPartial 13 304445) = some ⟨13, 2, 0, 583969, 304445, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_304445_583969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304445 ⟨583969, by decide⟩ :=
  accepted_of_selected 13 304445 ⟨583969, by decide⟩ ⟨13, 2, 0, 583969, 304445, 1617, 16384⟩
    (by decide) selected_cut_23048

theorem selected_cut_23049 : selected 8 ⟨583988, by decide⟩
    (prefixPartial 13 304446) = some ⟨13, 2, 0, 583988, 304446, 1681, 16384⟩ := by
  decide +kernel

theorem context_13_304446_583988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304446 ⟨583988, by decide⟩ :=
  accepted_of_selected 13 304446 ⟨583988, by decide⟩ ⟨13, 2, 0, 583988, 304446, 1681, 16384⟩
    (by decide) selected_cut_23049

theorem selected_cut_23050 : selected 8 ⟨583996, by decide⟩
    (prefixPartial 13 304447) = some ⟨13, 2, 0, 583996, 304447, 981, 16384⟩ := by
  decide +kernel

theorem context_13_304447_583996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304447 ⟨583996, by decide⟩ :=
  accepted_of_selected 13 304447 ⟨583996, by decide⟩ ⟨13, 2, 0, 583996, 304447, 981, 16384⟩
    (by decide) selected_cut_23050

theorem unmarked_context_12_76111_583997 : frontier 9 ⟨583997, by decide⟩
    (prefixCache 12 76111) (prefixPartial 12 76111) = false := by
  decide +kernel

theorem node_context_12_76111_583997 : EJMOriginalGlobalDAGData.nodes 9 ⟨583997, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨583969, by decide⟩,⟨583988, by decide⟩,⟨583996, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76111_583997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76111 ⟨583997, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76111
    ⟨583997, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨583969, by decide⟩,⟨583988, by decide⟩,⟨583996, by decide⟩]) unmarked_context_12_76111_583997 node_context_12_76111_583997
  intro a
  fin_cases a
  · exact context_13_304444_3444
  · exact context_13_304445_583969
  · exact context_13_304446_583988
  · exact context_13_304447_583996

theorem unmarked_context_11_19027_583998 : frontier 10 ⟨583998, by decide⟩
    (prefixCache 11 19027) (prefixPartial 11 19027) = false := by
  decide +kernel

theorem node_context_11_19027_583998 : EJMOriginalGlobalDAGData.nodes 10 ⟨583998, by decide⟩ =
    .split (coordinate 11) (![⟨583867, by decide⟩,⟨583904, by decide⟩,⟨583949, by decide⟩,⟨583997, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19027_583998 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19027 ⟨583998, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19027
    ⟨583998, by decide⟩ (by decide) (![⟨583867, by decide⟩,⟨583904, by decide⟩,⟨583949, by decide⟩,⟨583997, by decide⟩]) unmarked_context_11_19027_583998 node_context_11_19027_583998
  intro a
  fin_cases a
  · exact context_12_76108_583867
  · exact context_12_76109_583904
  · exact context_12_76110_583949
  · exact context_12_76111_583997

theorem unmarked_context_10_4756_583999 : frontier 11 ⟨583999, by decide⟩
    (prefixCache 10 4756) (prefixPartial 10 4756) = false := by
  decide +kernel

theorem node_context_10_4756_583999 : EJMOriginalGlobalDAGData.nodes 11 ⟨583999, by decide⟩ =
    .split (coordinate 10) (![⟨583520, by decide⟩,⟨583652, by decide⟩,⟨583825, by decide⟩,⟨583998, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4756_583999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4756 ⟨583999, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4756
    ⟨583999, by decide⟩ (by decide) (![⟨583520, by decide⟩,⟨583652, by decide⟩,⟨583825, by decide⟩,⟨583998, by decide⟩]) unmarked_context_10_4756_583999 node_context_10_4756_583999
  intro a
  fin_cases a
  · exact context_11_19024_583520
  · exact context_11_19025_583652
  · exact context_11_19026_583825
  · exact context_11_19027_583998

theorem selected_cut_23051 : selected 9 ⟨584044, by decide⟩
    (prefixPartial 12 76112) = some ⟨12, 2, 0, 584044, 76112, 3981, 65536⟩ := by
  decide +kernel

theorem context_12_76112_584044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76112 ⟨584044, by decide⟩ :=
  accepted_of_selected 12 76112 ⟨584044, by decide⟩ ⟨12, 2, 0, 584044, 76112, 3981, 65536⟩
    (by decide) selected_cut_23051

theorem selected_cut_23052 : selected 9 ⟨584085, by decide⟩
    (prefixPartial 12 76113) = some ⟨12, 2, 0, 584085, 76113, 3769, 65536⟩ := by
  decide +kernel

theorem context_12_76113_584085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76113 ⟨584085, by decide⟩ :=
  accepted_of_selected 12 76113 ⟨584085, by decide⟩ ⟨12, 2, 0, 584085, 76113, 3769, 65536⟩
    (by decide) selected_cut_23052

theorem selected_cut_23053 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304456) = some ⟨13, 1, 0, 3444, 304456, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304456_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304456 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304456 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304456, 1, 16384⟩
    (by decide) selected_cut_23053

theorem selected_cut_23054 : selected 8 ⟨584109, by decide⟩
    (prefixPartial 13 304457) = some ⟨13, 2, 0, 584109, 304457, 1885, 16384⟩ := by
  decide +kernel

theorem context_13_304457_584109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304457 ⟨584109, by decide⟩ :=
  accepted_of_selected 13 304457 ⟨584109, by decide⟩ ⟨13, 2, 0, 584109, 304457, 1885, 16384⟩
    (by decide) selected_cut_23054

theorem selected_cut_23055 : selected 8 ⟨584132, by decide⟩
    (prefixPartial 13 304458) = some ⟨13, 2, 0, 584132, 304458, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_304458_584132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304458 ⟨584132, by decide⟩ :=
  accepted_of_selected 13 304458 ⟨584132, by decide⟩ ⟨13, 2, 0, 584132, 304458, 2061, 16384⟩
    (by decide) selected_cut_23055

theorem selected_cut_23056 : selected 8 ⟨584139, by decide⟩
    (prefixPartial 13 304459) = some ⟨13, 2, 0, 584139, 304459, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_304459_584139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304459 ⟨584139, by decide⟩ :=
  accepted_of_selected 13 304459 ⟨584139, by decide⟩ ⟨13, 2, 0, 584139, 304459, 1073, 16384⟩
    (by decide) selected_cut_23056

theorem unmarked_context_12_76114_584140 : frontier 9 ⟨584140, by decide⟩
    (prefixCache 12 76114) (prefixPartial 12 76114) = false := by
  decide +kernel

theorem node_context_12_76114_584140 : EJMOriginalGlobalDAGData.nodes 9 ⟨584140, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584109, by decide⟩,⟨584132, by decide⟩,⟨584139, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76114_584140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76114 ⟨584140, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76114
    ⟨584140, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584109, by decide⟩,⟨584132, by decide⟩,⟨584139, by decide⟩]) unmarked_context_12_76114_584140 node_context_12_76114_584140
  intro a
  fin_cases a
  · exact context_13_304456_3444
  · exact context_13_304457_584109
  · exact context_13_304458_584132
  · exact context_13_304459_584139

theorem selected_cut_23057 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304460) = some ⟨13, 1, 0, 3444, 304460, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304460_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304460 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304460 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304460, 1, 16384⟩
    (by decide) selected_cut_23057

theorem selected_cut_23058 : selected 8 ⟨584157, by decide⟩
    (prefixPartial 13 304461) = some ⟨13, 2, 0, 584157, 304461, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_304461_584157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304461 ⟨584157, by decide⟩ :=
  accepted_of_selected 13 304461 ⟨584157, by decide⟩ ⟨13, 2, 0, 584157, 304461, 1801, 16384⟩
    (by decide) selected_cut_23058

theorem selected_cut_23059 : selected 8 ⟨584178, by decide⟩
    (prefixPartial 13 304462) = some ⟨13, 2, 0, 584178, 304462, 2165, 16384⟩ := by
  decide +kernel

theorem context_13_304462_584178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304462 ⟨584178, by decide⟩ :=
  accepted_of_selected 13 304462 ⟨584178, by decide⟩ ⟨13, 2, 0, 584178, 304462, 2165, 16384⟩
    (by decide) selected_cut_23059

theorem selected_cut_23060 : selected 8 ⟨584184, by decide⟩
    (prefixPartial 13 304463) = some ⟨13, 2, 0, 584184, 304463, 929, 16384⟩ := by
  decide +kernel

theorem context_13_304463_584184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304463 ⟨584184, by decide⟩ :=
  accepted_of_selected 13 304463 ⟨584184, by decide⟩ ⟨13, 2, 0, 584184, 304463, 929, 16384⟩
    (by decide) selected_cut_23060

theorem unmarked_context_12_76115_584185 : frontier 9 ⟨584185, by decide⟩
    (prefixCache 12 76115) (prefixPartial 12 76115) = false := by
  decide +kernel

theorem node_context_12_76115_584185 : EJMOriginalGlobalDAGData.nodes 9 ⟨584185, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584157, by decide⟩,⟨584178, by decide⟩,⟨584184, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76115_584185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76115 ⟨584185, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76115
    ⟨584185, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584157, by decide⟩,⟨584178, by decide⟩,⟨584184, by decide⟩]) unmarked_context_12_76115_584185 node_context_12_76115_584185
  intro a
  fin_cases a
  · exact context_13_304460_3444
  · exact context_13_304461_584157
  · exact context_13_304462_584178
  · exact context_13_304463_584184

theorem unmarked_context_11_19028_584186 : frontier 10 ⟨584186, by decide⟩
    (prefixCache 11 19028) (prefixPartial 11 19028) = false := by
  decide +kernel

theorem node_context_11_19028_584186 : EJMOriginalGlobalDAGData.nodes 10 ⟨584186, by decide⟩ =
    .split (coordinate 11) (![⟨584044, by decide⟩,⟨584085, by decide⟩,⟨584140, by decide⟩,⟨584185, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19028_584186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19028 ⟨584186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19028
    ⟨584186, by decide⟩ (by decide) (![⟨584044, by decide⟩,⟨584085, by decide⟩,⟨584140, by decide⟩,⟨584185, by decide⟩]) unmarked_context_11_19028_584186 node_context_11_19028_584186
  intro a
  fin_cases a
  · exact context_12_76112_584044
  · exact context_12_76113_584085
  · exact context_12_76114_584140
  · exact context_12_76115_584185

theorem selected_cut_23061 : selected 9 ⟨584228, by decide⟩
    (prefixPartial 12 76116) = some ⟨12, 2, 0, 584228, 76116, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_76116_584228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76116 ⟨584228, by decide⟩ :=
  accepted_of_selected 12 76116 ⟨584228, by decide⟩ ⟨12, 2, 0, 584228, 76116, 3481, 65536⟩
    (by decide) selected_cut_23061

theorem selected_cut_23062 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 76117) = some ⟨12, 1, 0, 439069, 76117, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76117_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76117 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 76117 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 76117, 1, 65536⟩
    (by decide) selected_cut_23062

theorem selected_cut_23063 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304472) = some ⟨13, 1, 0, 3444, 304472, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304472_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304472 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304472 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304472, 1, 16384⟩
    (by decide) selected_cut_23063

theorem selected_cut_23064 : selected 8 ⟨584245, by decide⟩
    (prefixPartial 13 304473) = some ⟨13, 2, 0, 584245, 304473, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_304473_584245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304473 ⟨584245, by decide⟩ :=
  accepted_of_selected 13 304473 ⟨584245, by decide⟩ ⟨13, 2, 0, 584245, 304473, 1485, 16384⟩
    (by decide) selected_cut_23064

theorem selected_cut_23065 : selected 8 ⟨584266, by decide⟩
    (prefixPartial 13 304474) = some ⟨13, 2, 0, 584266, 304474, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_304474_584266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304474 ⟨584266, by decide⟩ :=
  accepted_of_selected 13 304474 ⟨584266, by decide⟩ ⟨13, 2, 0, 584266, 304474, 1745, 16384⟩
    (by decide) selected_cut_23065

theorem selected_cut_23066 : selected 8 ⟨584273, by decide⟩
    (prefixPartial 13 304475) = some ⟨13, 2, 0, 584273, 304475, 1037, 16384⟩ := by
  decide +kernel

theorem context_13_304475_584273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304475 ⟨584273, by decide⟩ :=
  accepted_of_selected 13 304475 ⟨584273, by decide⟩ ⟨13, 2, 0, 584273, 304475, 1037, 16384⟩
    (by decide) selected_cut_23066

theorem unmarked_context_12_76118_584274 : frontier 9 ⟨584274, by decide⟩
    (prefixCache 12 76118) (prefixPartial 12 76118) = false := by
  decide +kernel

theorem node_context_12_76118_584274 : EJMOriginalGlobalDAGData.nodes 9 ⟨584274, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584245, by decide⟩,⟨584266, by decide⟩,⟨584273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76118_584274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76118 ⟨584274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76118
    ⟨584274, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584245, by decide⟩,⟨584266, by decide⟩,⟨584273, by decide⟩]) unmarked_context_12_76118_584274 node_context_12_76118_584274
  intro a
  fin_cases a
  · exact context_13_304472_3444
  · exact context_13_304473_584245
  · exact context_13_304474_584266
  · exact context_13_304475_584273

theorem selected_cut_23067 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304476) = some ⟨13, 1, 0, 3444, 304476, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304476_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304476 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304476 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304476, 1, 16384⟩
    (by decide) selected_cut_23067

theorem selected_cut_23068 : selected 8 ⟨584289, by decide⟩
    (prefixPartial 13 304477) = some ⟨13, 2, 0, 584289, 304477, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_304477_584289 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304477 ⟨584289, by decide⟩ :=
  accepted_of_selected 13 304477 ⟨584289, by decide⟩ ⟨13, 2, 0, 584289, 304477, 1557, 16384⟩
    (by decide) selected_cut_23068

theorem selected_cut_23069 : selected 8 ⟨584307, by decide⟩
    (prefixPartial 13 304478) = some ⟨13, 2, 0, 584307, 304478, 1969, 16384⟩ := by
  decide +kernel

theorem context_13_304478_584307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304478 ⟨584307, by decide⟩ :=
  accepted_of_selected 13 304478 ⟨584307, by decide⟩ ⟨13, 2, 0, 584307, 304478, 1969, 16384⟩
    (by decide) selected_cut_23069

theorem selected_cut_23070 : selected 8 ⟨584314, by decide⟩
    (prefixPartial 13 304479) = some ⟨13, 2, 0, 584314, 304479, 853, 16384⟩ := by
  decide +kernel

theorem context_13_304479_584314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304479 ⟨584314, by decide⟩ :=
  accepted_of_selected 13 304479 ⟨584314, by decide⟩ ⟨13, 2, 0, 584314, 304479, 853, 16384⟩
    (by decide) selected_cut_23070

theorem unmarked_context_12_76119_584315 : frontier 9 ⟨584315, by decide⟩
    (prefixCache 12 76119) (prefixPartial 12 76119) = false := by
  decide +kernel

theorem node_context_12_76119_584315 : EJMOriginalGlobalDAGData.nodes 9 ⟨584315, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584289, by decide⟩,⟨584307, by decide⟩,⟨584314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76119_584315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76119 ⟨584315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76119
    ⟨584315, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584289, by decide⟩,⟨584307, by decide⟩,⟨584314, by decide⟩]) unmarked_context_12_76119_584315 node_context_12_76119_584315
  intro a
  fin_cases a
  · exact context_13_304476_3444
  · exact context_13_304477_584289
  · exact context_13_304478_584307
  · exact context_13_304479_584314

theorem unmarked_context_11_19029_584316 : frontier 10 ⟨584316, by decide⟩
    (prefixCache 11 19029) (prefixPartial 11 19029) = false := by
  decide +kernel

theorem node_context_11_19029_584316 : EJMOriginalGlobalDAGData.nodes 10 ⟨584316, by decide⟩ =
    .split (coordinate 11) (![⟨584228, by decide⟩,⟨439069, by decide⟩,⟨584274, by decide⟩,⟨584315, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19029_584316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19029 ⟨584316, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19029
    ⟨584316, by decide⟩ (by decide) (![⟨584228, by decide⟩,⟨439069, by decide⟩,⟨584274, by decide⟩,⟨584315, by decide⟩]) unmarked_context_11_19029_584316 node_context_11_19029_584316
  intro a
  fin_cases a
  · exact context_12_76116_584228
  · exact context_12_76117_439069
  · exact context_12_76118_584274
  · exact context_12_76119_584315

theorem selected_cut_23071 : selected 9 ⟨584355, by decide⟩
    (prefixPartial 12 76120) = some ⟨12, 2, 0, 584355, 76120, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_76120_584355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76120 ⟨584355, by decide⟩ :=
  accepted_of_selected 12 76120 ⟨584355, by decide⟩ ⟨12, 2, 0, 584355, 76120, 3777, 65536⟩
    (by decide) selected_cut_23071

theorem selected_cut_23072 : selected 9 ⟨584395, by decide⟩
    (prefixPartial 12 76121) = some ⟨12, 2, 0, 584395, 76121, 3577, 65536⟩ := by
  decide +kernel

theorem context_12_76121_584395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76121 ⟨584395, by decide⟩ :=
  accepted_of_selected 12 76121 ⟨584395, by decide⟩ ⟨12, 2, 0, 584395, 76121, 3577, 65536⟩
    (by decide) selected_cut_23072

theorem selected_cut_23073 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304488) = some ⟨13, 1, 0, 3444, 304488, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304488_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304488 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304488 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304488, 1, 16384⟩
    (by decide) selected_cut_23073

theorem selected_cut_23074 : selected 8 ⟨584409, by decide⟩
    (prefixPartial 13 304489) = some ⟨13, 2, 0, 584409, 304489, 1401, 16384⟩ := by
  decide +kernel

theorem context_13_304489_584409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304489 ⟨584409, by decide⟩ :=
  accepted_of_selected 13 304489 ⟨584409, by decide⟩ ⟨13, 2, 0, 584409, 304489, 1401, 16384⟩
    (by decide) selected_cut_23074

theorem selected_cut_23075 : selected 8 ⟨584429, by decide⟩
    (prefixPartial 13 304490) = some ⟨13, 2, 0, 584429, 304490, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_304490_584429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304490 ⟨584429, by decide⟩ :=
  accepted_of_selected 13 304490 ⟨584429, by decide⟩ ⟨13, 2, 0, 584429, 304490, 1797, 16384⟩
    (by decide) selected_cut_23075

theorem selected_cut_23076 : selected 8 ⟨584436, by decide⟩
    (prefixPartial 13 304491) = some ⟨13, 2, 0, 584436, 304491, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_304491_584436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304491 ⟨584436, by decide⟩ :=
  accepted_of_selected 13 304491 ⟨584436, by decide⟩ ⟨13, 2, 0, 584436, 304491, 1049, 16384⟩
    (by decide) selected_cut_23076

theorem unmarked_context_12_76122_584437 : frontier 9 ⟨584437, by decide⟩
    (prefixCache 12 76122) (prefixPartial 12 76122) = false := by
  decide +kernel

theorem node_context_12_76122_584437 : EJMOriginalGlobalDAGData.nodes 9 ⟨584437, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584409, by decide⟩,⟨584429, by decide⟩,⟨584436, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76122_584437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76122 ⟨584437, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76122
    ⟨584437, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584409, by decide⟩,⟨584429, by decide⟩,⟨584436, by decide⟩]) unmarked_context_12_76122_584437 node_context_12_76122_584437
  intro a
  fin_cases a
  · exact context_13_304488_3444
  · exact context_13_304489_584409
  · exact context_13_304490_584429
  · exact context_13_304491_584436

theorem selected_cut_23077 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304492) = some ⟨13, 1, 0, 3444, 304492, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304492_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304492 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304492 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304492, 1, 16384⟩
    (by decide) selected_cut_23077

theorem selected_cut_23078 : selected 8 ⟨584453, by decide⟩
    (prefixPartial 13 304493) = some ⟨13, 2, 0, 584453, 304493, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_304493_584453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304493 ⟨584453, by decide⟩ :=
  accepted_of_selected 13 304493 ⟨584453, by decide⟩ ⟨13, 2, 0, 584453, 304493, 1465, 16384⟩
    (by decide) selected_cut_23078

theorem selected_cut_23079 : selected 8 ⟨584468, by decide⟩
    (prefixPartial 13 304494) = some ⟨13, 2, 0, 584468, 304494, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_304494_584468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304494 ⟨584468, by decide⟩ :=
  accepted_of_selected 13 304494 ⟨584468, by decide⟩ ⟨13, 2, 0, 584468, 304494, 2025, 16384⟩
    (by decide) selected_cut_23079

theorem selected_cut_23080 : selected 8 ⟨584475, by decide⟩
    (prefixPartial 13 304495) = some ⟨13, 2, 0, 584475, 304495, 881, 16384⟩ := by
  decide +kernel

theorem context_13_304495_584475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304495 ⟨584475, by decide⟩ :=
  accepted_of_selected 13 304495 ⟨584475, by decide⟩ ⟨13, 2, 0, 584475, 304495, 881, 16384⟩
    (by decide) selected_cut_23080

theorem unmarked_context_12_76123_584476 : frontier 9 ⟨584476, by decide⟩
    (prefixCache 12 76123) (prefixPartial 12 76123) = false := by
  decide +kernel

theorem node_context_12_76123_584476 : EJMOriginalGlobalDAGData.nodes 9 ⟨584476, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584453, by decide⟩,⟨584468, by decide⟩,⟨584475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76123_584476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76123 ⟨584476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76123
    ⟨584476, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584453, by decide⟩,⟨584468, by decide⟩,⟨584475, by decide⟩]) unmarked_context_12_76123_584476 node_context_12_76123_584476
  intro a
  fin_cases a
  · exact context_13_304492_3444
  · exact context_13_304493_584453
  · exact context_13_304494_584468
  · exact context_13_304495_584475

theorem unmarked_context_11_19030_584477 : frontier 10 ⟨584477, by decide⟩
    (prefixCache 11 19030) (prefixPartial 11 19030) = false := by
  decide +kernel

theorem node_context_11_19030_584477 : EJMOriginalGlobalDAGData.nodes 10 ⟨584477, by decide⟩ =
    .split (coordinate 11) (![⟨584355, by decide⟩,⟨584395, by decide⟩,⟨584437, by decide⟩,⟨584476, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19030_584477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19030 ⟨584477, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19030
    ⟨584477, by decide⟩ (by decide) (![⟨584355, by decide⟩,⟨584395, by decide⟩,⟨584437, by decide⟩,⟨584476, by decide⟩]) unmarked_context_11_19030_584477 node_context_11_19030_584477
  intro a
  fin_cases a
  · exact context_12_76120_584355
  · exact context_12_76121_584395
  · exact context_12_76122_584437
  · exact context_12_76123_584476

theorem selected_cut_23081 : selected 9 ⟨584516, by decide⟩
    (prefixPartial 12 76124) = some ⟨12, 2, 0, 584516, 76124, 3901, 65536⟩ := by
  decide +kernel

theorem context_12_76124_584516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76124 ⟨584516, by decide⟩ :=
  accepted_of_selected 12 76124 ⟨584516, by decide⟩ ⟨12, 2, 0, 584516, 76124, 3901, 65536⟩
    (by decide) selected_cut_23081

theorem selected_cut_23082 : selected 9 ⟨584551, by decide⟩
    (prefixPartial 12 76125) = some ⟨12, 2, 0, 584551, 76125, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_76125_584551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76125 ⟨584551, by decide⟩ :=
  accepted_of_selected 12 76125 ⟨584551, by decide⟩ ⟨12, 2, 0, 584551, 76125, 3453, 65536⟩
    (by decide) selected_cut_23082

theorem selected_cut_23083 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304504) = some ⟨13, 1, 0, 3444, 304504, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304504_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304504 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304504 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304504, 1, 16384⟩
    (by decide) selected_cut_23083

theorem selected_cut_23084 : selected 8 ⟨584564, by decide⟩
    (prefixPartial 13 304505) = some ⟨13, 2, 0, 584564, 304505, 1465, 16384⟩ := by
  decide +kernel

theorem context_13_304505_584564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304505 ⟨584564, by decide⟩ :=
  accepted_of_selected 13 304505 ⟨584564, by decide⟩ ⟨13, 2, 0, 584564, 304505, 1465, 16384⟩
    (by decide) selected_cut_23084

theorem selected_cut_23085 : selected 8 ⟨584584, by decide⟩
    (prefixPartial 13 304506) = some ⟨13, 2, 0, 584584, 304506, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_304506_584584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304506 ⟨584584, by decide⟩ :=
  accepted_of_selected 13 304506 ⟨584584, by decide⟩ ⟨13, 2, 0, 584584, 304506, 1861, 16384⟩
    (by decide) selected_cut_23085

theorem selected_cut_23086 : selected 8 ⟨584594, by decide⟩
    (prefixPartial 13 304507) = some ⟨13, 2, 0, 584594, 304507, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_304507_584594 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304507 ⟨584594, by decide⟩ :=
  accepted_of_selected 13 304507 ⟨584594, by decide⟩ ⟨13, 2, 0, 584594, 304507, 1141, 16384⟩
    (by decide) selected_cut_23086

theorem unmarked_context_12_76126_584595 : frontier 9 ⟨584595, by decide⟩
    (prefixCache 12 76126) (prefixPartial 12 76126) = false := by
  decide +kernel

theorem node_context_12_76126_584595 : EJMOriginalGlobalDAGData.nodes 9 ⟨584595, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584564, by decide⟩,⟨584584, by decide⟩,⟨584594, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76126_584595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76126 ⟨584595, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76126
    ⟨584595, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584564, by decide⟩,⟨584584, by decide⟩,⟨584594, by decide⟩]) unmarked_context_12_76126_584595 node_context_12_76126_584595
  intro a
  fin_cases a
  · exact context_13_304504_3444
  · exact context_13_304505_584564
  · exact context_13_304506_584584
  · exact context_13_304507_584594

theorem selected_cut_23087 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304508) = some ⟨13, 1, 0, 3444, 304508, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304508_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304508 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304508 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304508, 1, 16384⟩
    (by decide) selected_cut_23087

theorem selected_cut_23088 : selected 8 ⟨584606, by decide⟩
    (prefixPartial 13 304509) = some ⟨13, 2, 0, 584606, 304509, 1493, 16384⟩ := by
  decide +kernel

theorem context_13_304509_584606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304509 ⟨584606, by decide⟩ :=
  accepted_of_selected 13 304509 ⟨584606, by decide⟩ ⟨13, 2, 0, 584606, 304509, 1493, 16384⟩
    (by decide) selected_cut_23088

theorem selected_cut_23089 : selected 8 ⟨584625, by decide⟩
    (prefixPartial 13 304510) = some ⟨13, 2, 0, 584625, 304510, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_304510_584625 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304510 ⟨584625, by decide⟩ :=
  accepted_of_selected 13 304510 ⟨584625, by decide⟩ ⟨13, 2, 0, 584625, 304510, 2053, 16384⟩
    (by decide) selected_cut_23089

theorem selected_cut_23090 : selected 8 ⟨584631, by decide⟩
    (prefixPartial 13 304511) = some ⟨13, 2, 0, 584631, 304511, 973, 16384⟩ := by
  decide +kernel

theorem context_13_304511_584631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304511 ⟨584631, by decide⟩ :=
  accepted_of_selected 13 304511 ⟨584631, by decide⟩ ⟨13, 2, 0, 584631, 304511, 973, 16384⟩
    (by decide) selected_cut_23090

theorem unmarked_context_12_76127_584632 : frontier 9 ⟨584632, by decide⟩
    (prefixCache 12 76127) (prefixPartial 12 76127) = false := by
  decide +kernel

theorem node_context_12_76127_584632 : EJMOriginalGlobalDAGData.nodes 9 ⟨584632, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584606, by decide⟩,⟨584625, by decide⟩,⟨584631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76127_584632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76127 ⟨584632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76127
    ⟨584632, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584606, by decide⟩,⟨584625, by decide⟩,⟨584631, by decide⟩]) unmarked_context_12_76127_584632 node_context_12_76127_584632
  intro a
  fin_cases a
  · exact context_13_304508_3444
  · exact context_13_304509_584606
  · exact context_13_304510_584625
  · exact context_13_304511_584631

theorem unmarked_context_11_19031_584633 : frontier 10 ⟨584633, by decide⟩
    (prefixCache 11 19031) (prefixPartial 11 19031) = false := by
  decide +kernel

theorem node_context_11_19031_584633 : EJMOriginalGlobalDAGData.nodes 10 ⟨584633, by decide⟩ =
    .split (coordinate 11) (![⟨584516, by decide⟩,⟨584551, by decide⟩,⟨584595, by decide⟩,⟨584632, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19031_584633 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19031 ⟨584633, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19031
    ⟨584633, by decide⟩ (by decide) (![⟨584516, by decide⟩,⟨584551, by decide⟩,⟨584595, by decide⟩,⟨584632, by decide⟩]) unmarked_context_11_19031_584633 node_context_11_19031_584633
  intro a
  fin_cases a
  · exact context_12_76124_584516
  · exact context_12_76125_584551
  · exact context_12_76126_584595
  · exact context_12_76127_584632

theorem unmarked_context_10_4757_584634 : frontier 11 ⟨584634, by decide⟩
    (prefixCache 10 4757) (prefixPartial 10 4757) = false := by
  decide +kernel

theorem node_context_10_4757_584634 : EJMOriginalGlobalDAGData.nodes 11 ⟨584634, by decide⟩ =
    .split (coordinate 10) (![⟨584186, by decide⟩,⟨584316, by decide⟩,⟨584477, by decide⟩,⟨584633, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4757_584634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4757 ⟨584634, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4757
    ⟨584634, by decide⟩ (by decide) (![⟨584186, by decide⟩,⟨584316, by decide⟩,⟨584477, by decide⟩,⟨584633, by decide⟩]) unmarked_context_10_4757_584634 node_context_10_4757_584634
  intro a
  fin_cases a
  · exact context_11_19028_584186
  · exact context_11_19029_584316
  · exact context_11_19030_584477
  · exact context_11_19031_584633

theorem selected_cut_23091 : selected 9 ⟨584677, by decide⟩
    (prefixPartial 12 76128) = some ⟨12, 2, 0, 584677, 76128, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_76128_584677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76128 ⟨584677, by decide⟩ :=
  accepted_of_selected 12 76128 ⟨584677, by decide⟩ ⟨12, 2, 0, 584677, 76128, 3245, 65536⟩
    (by decide) selected_cut_23091

theorem selected_cut_23092 : selected 9 ⟨584708, by decide⟩
    (prefixPartial 12 76129) = some ⟨12, 2, 0, 584708, 76129, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_76129_584708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76129 ⟨584708, by decide⟩ :=
  accepted_of_selected 12 76129 ⟨584708, by decide⟩ ⟨12, 2, 0, 584708, 76129, 3009, 65536⟩
    (by decide) selected_cut_23092

theorem selected_cut_23093 : selected 9 ⟨584751, by decide⟩
    (prefixPartial 12 76130) = some ⟨12, 2, 0, 584751, 76130, 3725, 65536⟩ := by
  decide +kernel

theorem context_12_76130_584751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76130 ⟨584751, by decide⟩ :=
  accepted_of_selected 12 76130 ⟨584751, by decide⟩ ⟨12, 2, 0, 584751, 76130, 3725, 65536⟩
    (by decide) selected_cut_23093

theorem selected_cut_23094 : selected 9 ⟨584791, by decide⟩
    (prefixPartial 12 76131) = some ⟨12, 2, 0, 584791, 76131, 3917, 65536⟩ := by
  decide +kernel

theorem context_12_76131_584791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76131 ⟨584791, by decide⟩ :=
  accepted_of_selected 12 76131 ⟨584791, by decide⟩ ⟨12, 2, 0, 584791, 76131, 3917, 65536⟩
    (by decide) selected_cut_23094

theorem unmarked_context_11_19032_584792 : frontier 10 ⟨584792, by decide⟩
    (prefixCache 11 19032) (prefixPartial 11 19032) = false := by
  decide +kernel

theorem node_context_11_19032_584792 : EJMOriginalGlobalDAGData.nodes 10 ⟨584792, by decide⟩ =
    .split (coordinate 11) (![⟨584677, by decide⟩,⟨584708, by decide⟩,⟨584751, by decide⟩,⟨584791, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19032_584792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19032 ⟨584792, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19032
    ⟨584792, by decide⟩ (by decide) (![⟨584677, by decide⟩,⟨584708, by decide⟩,⟨584751, by decide⟩,⟨584791, by decide⟩]) unmarked_context_11_19032_584792 node_context_11_19032_584792
  intro a
  fin_cases a
  · exact context_12_76128_584677
  · exact context_12_76129_584708
  · exact context_12_76130_584751
  · exact context_12_76131_584791

theorem selected_cut_23095 : selected 9 ⟨584825, by decide⟩
    (prefixPartial 12 76132) = some ⟨12, 2, 0, 584825, 76132, 2909, 65536⟩ := by
  decide +kernel

theorem context_12_76132_584825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76132 ⟨584825, by decide⟩ :=
  accepted_of_selected 12 76132 ⟨584825, by decide⟩ ⟨12, 2, 0, 584825, 76132, 2909, 65536⟩
    (by decide) selected_cut_23095

theorem selected_cut_23096 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 76133) = some ⟨12, 1, 0, 441672, 76133, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76133_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76133 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 76133 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 76133, 1, 65536⟩
    (by decide) selected_cut_23096

theorem selected_cut_23097 : selected 9 ⟨584860, by decide⟩
    (prefixPartial 12 76134) = some ⟨12, 2, 0, 584860, 76134, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_76134_584860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76134 ⟨584860, by decide⟩ :=
  accepted_of_selected 12 76134 ⟨584860, by decide⟩ ⟨12, 2, 0, 584860, 76134, 3185, 65536⟩
    (by decide) selected_cut_23097

theorem selected_cut_23098 : selected 9 ⟨584902, by decide⟩
    (prefixPartial 12 76135) = some ⟨12, 2, 0, 584902, 76135, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_76135_584902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76135 ⟨584902, by decide⟩ :=
  accepted_of_selected 12 76135 ⟨584902, by decide⟩ ⟨12, 2, 0, 584902, 76135, 3505, 65536⟩
    (by decide) selected_cut_23098

theorem unmarked_context_11_19033_584903 : frontier 10 ⟨584903, by decide⟩
    (prefixCache 11 19033) (prefixPartial 11 19033) = false := by
  decide +kernel

theorem node_context_11_19033_584903 : EJMOriginalGlobalDAGData.nodes 10 ⟨584903, by decide⟩ =
    .split (coordinate 11) (![⟨584825, by decide⟩,⟨441672, by decide⟩,⟨584860, by decide⟩,⟨584902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19033_584903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19033 ⟨584903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19033
    ⟨584903, by decide⟩ (by decide) (![⟨584825, by decide⟩,⟨441672, by decide⟩,⟨584860, by decide⟩,⟨584902, by decide⟩]) unmarked_context_11_19033_584903 node_context_11_19033_584903
  intro a
  fin_cases a
  · exact context_12_76132_584825
  · exact context_12_76133_441672
  · exact context_12_76134_584860
  · exact context_12_76135_584902

theorem selected_cut_23099 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304544) = some ⟨13, 1, 0, 3444, 304544, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304544_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304544 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304544 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304544, 1, 16384⟩
    (by decide) selected_cut_23099

theorem selected_cut_23100 : selected 8 ⟨584912, by decide⟩
    (prefixPartial 13 304545) = some ⟨13, 2, 0, 584912, 304545, 961, 16384⟩ := by
  decide +kernel

theorem context_13_304545_584912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304545 ⟨584912, by decide⟩ :=
  accepted_of_selected 13 304545 ⟨584912, by decide⟩ ⟨13, 2, 0, 584912, 304545, 961, 16384⟩
    (by decide) selected_cut_23100

theorem selected_cut_23101 : selected 8 ⟨584933, by decide⟩
    (prefixPartial 13 304546) = some ⟨13, 2, 0, 584933, 304546, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_304546_584933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304546 ⟨584933, by decide⟩ :=
  accepted_of_selected 13 304546 ⟨584933, by decide⟩ ⟨13, 2, 0, 584933, 304546, 2033, 16384⟩
    (by decide) selected_cut_23101

theorem selected_cut_23102 : selected 8 ⟨584951, by decide⟩
    (prefixPartial 13 304547) = some ⟨13, 2, 0, 584951, 304547, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_304547_584951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304547 ⟨584951, by decide⟩ :=
  accepted_of_selected 13 304547 ⟨584951, by decide⟩ ⟨13, 2, 0, 584951, 304547, 1381, 16384⟩
    (by decide) selected_cut_23102

theorem unmarked_context_12_76136_584952 : frontier 9 ⟨584952, by decide⟩
    (prefixCache 12 76136) (prefixPartial 12 76136) = false := by
  decide +kernel

theorem node_context_12_76136_584952 : EJMOriginalGlobalDAGData.nodes 9 ⟨584952, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨584912, by decide⟩,⟨584933, by decide⟩,⟨584951, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76136_584952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76136 ⟨584952, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76136
    ⟨584952, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨584912, by decide⟩,⟨584933, by decide⟩,⟨584951, by decide⟩]) unmarked_context_12_76136_584952 node_context_12_76136_584952
  intro a
  fin_cases a
  · exact context_13_304544_3444
  · exact context_13_304545_584912
  · exact context_13_304546_584933
  · exact context_13_304547_584951

theorem selected_cut_23103 : selected 9 ⟨584996, by decide⟩
    (prefixPartial 12 76137) = some ⟨12, 2, 0, 584996, 76137, 3933, 65536⟩ := by
  decide +kernel

theorem context_12_76137_584996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76137 ⟨584996, by decide⟩ :=
  accepted_of_selected 12 76137 ⟨584996, by decide⟩ ⟨12, 2, 0, 584996, 76137, 3933, 65536⟩
    (by decide) selected_cut_23103

theorem selected_cut_23104 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 76138) = some ⟨12, 1, 0, 474208, 76138, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76138_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76138 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 76138 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 76138, 1, 65536⟩
    (by decide) selected_cut_23104

theorem selected_cut_23105 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 304556) = some ⟨13, 1, 0, 3444, 304556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_304556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 304556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 304556, 1, 16384⟩
    (by decide) selected_cut_23105

theorem selected_cut_23106 : selected 8 ⟨585005, by decide⟩
    (prefixPartial 13 304557) = some ⟨13, 2, 0, 585005, 304557, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_304557_585005 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304557 ⟨585005, by decide⟩ :=
  accepted_of_selected 13 304557 ⟨585005, by decide⟩ ⟨13, 2, 0, 585005, 304557, 1029, 16384⟩
    (by decide) selected_cut_23106

theorem selected_cut_23107 : selected 8 ⟨585037, by decide⟩
    (prefixPartial 13 304558) = some ⟨13, 2, 0, 585037, 304558, 2417, 16384⟩ := by
  decide +kernel

theorem context_13_304558_585037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304558 ⟨585037, by decide⟩ :=
  accepted_of_selected 13 304558 ⟨585037, by decide⟩ ⟨13, 2, 0, 585037, 304558, 2417, 16384⟩
    (by decide) selected_cut_23107

theorem selected_cut_23108 : selected 8 ⟨585050, by decide⟩
    (prefixPartial 13 304559) = some ⟨13, 2, 0, 585050, 304559, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_304559_585050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 304559 ⟨585050, by decide⟩ :=
  accepted_of_selected 13 304559 ⟨585050, by decide⟩ ⟨13, 2, 0, 585050, 304559, 1193, 16384⟩
    (by decide) selected_cut_23108

theorem unmarked_context_12_76139_585051 : frontier 9 ⟨585051, by decide⟩
    (prefixCache 12 76139) (prefixPartial 12 76139) = false := by
  decide +kernel

theorem node_context_12_76139_585051 : EJMOriginalGlobalDAGData.nodes 9 ⟨585051, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨585005, by decide⟩,⟨585037, by decide⟩,⟨585050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76139_585051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76139 ⟨585051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76139
    ⟨585051, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨585005, by decide⟩,⟨585037, by decide⟩,⟨585050, by decide⟩]) unmarked_context_12_76139_585051 node_context_12_76139_585051
  intro a
  fin_cases a
  · exact context_13_304556_3444
  · exact context_13_304557_585005
  · exact context_13_304558_585037
  · exact context_13_304559_585050

theorem unmarked_context_11_19034_585052 : frontier 10 ⟨585052, by decide⟩
    (prefixCache 11 19034) (prefixPartial 11 19034) = false := by
  decide +kernel

theorem node_context_11_19034_585052 : EJMOriginalGlobalDAGData.nodes 10 ⟨585052, by decide⟩ =
    .split (coordinate 11) (![⟨584952, by decide⟩,⟨584996, by decide⟩,⟨474208, by decide⟩,⟨585051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19034_585052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19034 ⟨585052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19034
    ⟨585052, by decide⟩ (by decide) (![⟨584952, by decide⟩,⟨584996, by decide⟩,⟨474208, by decide⟩,⟨585051, by decide⟩]) unmarked_context_11_19034_585052 node_context_11_19034_585052
  intro a
  fin_cases a
  · exact context_12_76136_584952
  · exact context_12_76137_584996
  · exact context_12_76138_474208
  · exact context_12_76139_585051

theorem selected_cut_23109 : selected 9 ⟨585090, by decide⟩
    (prefixPartial 12 76140) = some ⟨12, 2, 0, 585090, 76140, 3269, 65536⟩ := by
  decide +kernel

theorem context_12_76140_585090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76140 ⟨585090, by decide⟩ :=
  accepted_of_selected 12 76140 ⟨585090, by decide⟩ ⟨12, 2, 0, 585090, 76140, 3269, 65536⟩
    (by decide) selected_cut_23109

theorem selected_cut_23110 : selected 9 ⟨585119, by decide⟩
    (prefixPartial 12 76141) = some ⟨12, 2, 0, 585119, 76141, 2873, 65536⟩ := by
  decide +kernel

theorem context_12_76141_585119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76141 ⟨585119, by decide⟩ :=
  accepted_of_selected 12 76141 ⟨585119, by decide⟩ ⟨12, 2, 0, 585119, 76141, 2873, 65536⟩
    (by decide) selected_cut_23110

theorem selected_cut_23111 : selected 9 ⟨585162, by decide⟩
    (prefixPartial 12 76142) = some ⟨12, 2, 0, 585162, 76142, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_76142_585162 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76142 ⟨585162, by decide⟩ :=
  accepted_of_selected 12 76142 ⟨585162, by decide⟩ ⟨12, 2, 0, 585162, 76142, 3365, 65536⟩
    (by decide) selected_cut_23111

theorem selected_cut_23112 : selected 9 ⟨585195, by decide⟩
    (prefixPartial 12 76143) = some ⟨12, 2, 0, 585195, 76143, 3677, 65536⟩ := by
  decide +kernel

theorem context_12_76143_585195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76143 ⟨585195, by decide⟩ :=
  accepted_of_selected 12 76143 ⟨585195, by decide⟩ ⟨12, 2, 0, 585195, 76143, 3677, 65536⟩
    (by decide) selected_cut_23112

theorem unmarked_context_11_19035_585196 : frontier 10 ⟨585196, by decide⟩
    (prefixCache 11 19035) (prefixPartial 11 19035) = false := by
  decide +kernel

theorem node_context_11_19035_585196 : EJMOriginalGlobalDAGData.nodes 10 ⟨585196, by decide⟩ =
    .split (coordinate 11) (![⟨585090, by decide⟩,⟨585119, by decide⟩,⟨585162, by decide⟩,⟨585195, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19035_585196 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19035 ⟨585196, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19035
    ⟨585196, by decide⟩ (by decide) (![⟨585090, by decide⟩,⟨585119, by decide⟩,⟨585162, by decide⟩,⟨585195, by decide⟩]) unmarked_context_11_19035_585196 node_context_11_19035_585196
  intro a
  fin_cases a
  · exact context_12_76140_585090
  · exact context_12_76141_585119
  · exact context_12_76142_585162
  · exact context_12_76143_585195

theorem unmarked_context_10_4758_585197 : frontier 11 ⟨585197, by decide⟩
    (prefixCache 10 4758) (prefixPartial 10 4758) = false := by
  decide +kernel

theorem node_context_10_4758_585197 : EJMOriginalGlobalDAGData.nodes 11 ⟨585197, by decide⟩ =
    .split (coordinate 10) (![⟨584792, by decide⟩,⟨584903, by decide⟩,⟨585052, by decide⟩,⟨585196, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4758_585197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4758 ⟨585197, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4758
    ⟨585197, by decide⟩ (by decide) (![⟨584792, by decide⟩,⟨584903, by decide⟩,⟨585052, by decide⟩,⟨585196, by decide⟩]) unmarked_context_10_4758_585197 node_context_10_4758_585197
  intro a
  fin_cases a
  · exact context_11_19032_584792
  · exact context_11_19033_584903
  · exact context_11_19034_585052
  · exact context_11_19035_585196

theorem selected_cut_23113 : selected 9 ⟨585240, by decide⟩
    (prefixPartial 12 76144) = some ⟨12, 2, 0, 585240, 76144, 3453, 65536⟩ := by
  decide +kernel

theorem context_12_76144_585240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76144 ⟨585240, by decide⟩ :=
  accepted_of_selected 12 76144 ⟨585240, by decide⟩ ⟨12, 2, 0, 585240, 76144, 3453, 65536⟩
    (by decide) selected_cut_23113

theorem selected_cut_23114 : selected 9 ⟨585277, by decide⟩
    (prefixPartial 12 76145) = some ⟨12, 2, 0, 585277, 76145, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_76145_585277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76145 ⟨585277, by decide⟩ :=
  accepted_of_selected 12 76145 ⟨585277, by decide⟩ ⟨12, 2, 0, 585277, 76145, 3309, 65536⟩
    (by decide) selected_cut_23114

theorem selected_cut_23115 : selected 9 ⟨585315, by decide⟩
    (prefixPartial 12 76146) = some ⟨12, 2, 0, 585315, 76146, 3977, 65536⟩ := by
  decide +kernel

theorem context_12_76146_585315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76146 ⟨585315, by decide⟩ :=
  accepted_of_selected 12 76146 ⟨585315, by decide⟩ ⟨12, 2, 0, 585315, 76146, 3977, 65536⟩
    (by decide) selected_cut_23115

theorem selected_cut_23116 : selected 9 ⟨585357, by decide⟩
    (prefixPartial 12 76147) = some ⟨12, 2, 0, 585357, 76147, 3777, 65536⟩ := by
  decide +kernel

theorem context_12_76147_585357 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76147 ⟨585357, by decide⟩ :=
  accepted_of_selected 12 76147 ⟨585357, by decide⟩ ⟨12, 2, 0, 585357, 76147, 3777, 65536⟩
    (by decide) selected_cut_23116

theorem unmarked_context_11_19036_585358 : frontier 10 ⟨585358, by decide⟩
    (prefixCache 11 19036) (prefixPartial 11 19036) = false := by
  decide +kernel

theorem node_context_11_19036_585358 : EJMOriginalGlobalDAGData.nodes 10 ⟨585358, by decide⟩ =
    .split (coordinate 11) (![⟨585240, by decide⟩,⟨585277, by decide⟩,⟨585315, by decide⟩,⟨585357, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19036_585358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19036 ⟨585358, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19036
    ⟨585358, by decide⟩ (by decide) (![⟨585240, by decide⟩,⟨585277, by decide⟩,⟨585315, by decide⟩,⟨585357, by decide⟩]) unmarked_context_11_19036_585358 node_context_11_19036_585358
  intro a
  fin_cases a
  · exact context_12_76144_585240
  · exact context_12_76145_585277
  · exact context_12_76146_585315
  · exact context_12_76147_585357

theorem selected_cut_23117 : selected 9 ⟨585393, by decide⟩
    (prefixPartial 12 76148) = some ⟨12, 2, 0, 585393, 76148, 3053, 65536⟩ := by
  decide +kernel

theorem context_12_76148_585393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76148 ⟨585393, by decide⟩ :=
  accepted_of_selected 12 76148 ⟨585393, by decide⟩ ⟨12, 2, 0, 585393, 76148, 3053, 65536⟩
    (by decide) selected_cut_23117

theorem selected_cut_23118 : selected 9 ⟨441672, by decide⟩
    (prefixPartial 12 76149) = some ⟨12, 1, 0, 441672, 76149, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76149_441672 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76149 ⟨441672, by decide⟩ :=
  accepted_of_selected 12 76149 ⟨441672, by decide⟩ ⟨12, 1, 0, 441672, 76149, 1, 65536⟩
    (by decide) selected_cut_23118

theorem selected_cut_23119 : selected 9 ⟨585426, by decide⟩
    (prefixPartial 12 76150) = some ⟨12, 2, 0, 585426, 76150, 3401, 65536⟩ := by
  decide +kernel

theorem context_12_76150_585426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76150 ⟨585426, by decide⟩ :=
  accepted_of_selected 12 76150 ⟨585426, by decide⟩ ⟨12, 2, 0, 585426, 76150, 3401, 65536⟩
    (by decide) selected_cut_23119

theorem selected_cut_23120 : selected 9 ⟨585457, by decide⟩
    (prefixPartial 12 76151) = some ⟨12, 2, 0, 585457, 76151, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_76151_585457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76151 ⟨585457, by decide⟩ :=
  accepted_of_selected 12 76151 ⟨585457, by decide⟩ ⟨12, 2, 0, 585457, 76151, 3293, 65536⟩
    (by decide) selected_cut_23120

theorem unmarked_context_11_19037_585458 : frontier 10 ⟨585458, by decide⟩
    (prefixCache 11 19037) (prefixPartial 11 19037) = false := by
  decide +kernel

theorem node_context_11_19037_585458 : EJMOriginalGlobalDAGData.nodes 10 ⟨585458, by decide⟩ =
    .split (coordinate 11) (![⟨585393, by decide⟩,⟨441672, by decide⟩,⟨585426, by decide⟩,⟨585457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19037_585458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19037 ⟨585458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19037
    ⟨585458, by decide⟩ (by decide) (![⟨585393, by decide⟩,⟨441672, by decide⟩,⟨585426, by decide⟩,⟨585457, by decide⟩]) unmarked_context_11_19037_585458 node_context_11_19037_585458
  intro a
  fin_cases a
  · exact context_12_76148_585393
  · exact context_12_76149_441672
  · exact context_12_76150_585426
  · exact context_12_76151_585457

theorem selected_cut_23121 : selected 9 ⟨585488, by decide⟩
    (prefixPartial 12 76152) = some ⟨12, 2, 0, 585488, 76152, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_76152_585488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76152 ⟨585488, by decide⟩ :=
  accepted_of_selected 12 76152 ⟨585488, by decide⟩ ⟨12, 2, 0, 585488, 76152, 3225, 65536⟩
    (by decide) selected_cut_23121

theorem selected_cut_23122 : selected 9 ⟨585518, by decide⟩
    (prefixPartial 12 76153) = some ⟨12, 2, 0, 585518, 76153, 3093, 65536⟩ := by
  decide +kernel

theorem context_12_76153_585518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76153 ⟨585518, by decide⟩ :=
  accepted_of_selected 12 76153 ⟨585518, by decide⟩ ⟨12, 2, 0, 585518, 76153, 3093, 65536⟩
    (by decide) selected_cut_23122

theorem selected_cut_23123 : selected 9 ⟨585555, by decide⟩
    (prefixPartial 12 76154) = some ⟨12, 2, 0, 585555, 76154, 3409, 65536⟩ := by
  decide +kernel

theorem context_12_76154_585555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76154 ⟨585555, by decide⟩ :=
  accepted_of_selected 12 76154 ⟨585555, by decide⟩ ⟨12, 2, 0, 585555, 76154, 3409, 65536⟩
    (by decide) selected_cut_23123

theorem selected_cut_23124 : selected 9 ⟨585590, by decide⟩
    (prefixPartial 12 76155) = some ⟨12, 2, 0, 585590, 76155, 3277, 65536⟩ := by
  decide +kernel

theorem context_12_76155_585590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76155 ⟨585590, by decide⟩ :=
  accepted_of_selected 12 76155 ⟨585590, by decide⟩ ⟨12, 2, 0, 585590, 76155, 3277, 65536⟩
    (by decide) selected_cut_23124

theorem unmarked_context_11_19038_585591 : frontier 10 ⟨585591, by decide⟩
    (prefixCache 11 19038) (prefixPartial 11 19038) = false := by
  decide +kernel

theorem node_context_11_19038_585591 : EJMOriginalGlobalDAGData.nodes 10 ⟨585591, by decide⟩ =
    .split (coordinate 11) (![⟨585488, by decide⟩,⟨585518, by decide⟩,⟨585555, by decide⟩,⟨585590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19038_585591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19038 ⟨585591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19038
    ⟨585591, by decide⟩ (by decide) (![⟨585488, by decide⟩,⟨585518, by decide⟩,⟨585555, by decide⟩,⟨585590, by decide⟩]) unmarked_context_11_19038_585591 node_context_11_19038_585591
  intro a
  fin_cases a
  · exact context_12_76152_585488
  · exact context_12_76153_585518
  · exact context_12_76154_585555
  · exact context_12_76155_585590

theorem selected_cut_23125 : selected 9 ⟨585623, by decide⟩
    (prefixPartial 12 76156) = some ⟨12, 2, 0, 585623, 76156, 3057, 65536⟩ := by
  decide +kernel

theorem context_12_76156_585623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76156 ⟨585623, by decide⟩ :=
  accepted_of_selected 12 76156 ⟨585623, by decide⟩ ⟨12, 2, 0, 585623, 76156, 3057, 65536⟩
    (by decide) selected_cut_23125

theorem selected_cut_23126 : selected 9 ⟨585650, by decide⟩
    (prefixPartial 12 76157) = some ⟨12, 2, 0, 585650, 76157, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_76157_585650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76157 ⟨585650, by decide⟩ :=
  accepted_of_selected 12 76157 ⟨585650, by decide⟩ ⟨12, 2, 0, 585650, 76157, 2809, 65536⟩
    (by decide) selected_cut_23126

theorem selected_cut_23127 : selected 9 ⟨585686, by decide⟩
    (prefixPartial 12 76158) = some ⟨12, 2, 0, 585686, 76158, 3289, 65536⟩ := by
  decide +kernel

theorem context_12_76158_585686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76158 ⟨585686, by decide⟩ :=
  accepted_of_selected 12 76158 ⟨585686, by decide⟩ ⟨12, 2, 0, 585686, 76158, 3289, 65536⟩
    (by decide) selected_cut_23127

theorem selected_cut_23128 : selected 9 ⟨585715, by decide⟩
    (prefixPartial 12 76159) = some ⟨12, 2, 0, 585715, 76159, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_76159_585715 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76159 ⟨585715, by decide⟩ :=
  accepted_of_selected 12 76159 ⟨585715, by decide⟩ ⟨12, 2, 0, 585715, 76159, 3125, 65536⟩
    (by decide) selected_cut_23128

theorem unmarked_context_11_19039_585716 : frontier 10 ⟨585716, by decide⟩
    (prefixCache 11 19039) (prefixPartial 11 19039) = false := by
  decide +kernel

theorem node_context_11_19039_585716 : EJMOriginalGlobalDAGData.nodes 10 ⟨585716, by decide⟩ =
    .split (coordinate 11) (![⟨585623, by decide⟩,⟨585650, by decide⟩,⟨585686, by decide⟩,⟨585715, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19039_585716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19039 ⟨585716, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19039
    ⟨585716, by decide⟩ (by decide) (![⟨585623, by decide⟩,⟨585650, by decide⟩,⟨585686, by decide⟩,⟨585715, by decide⟩]) unmarked_context_11_19039_585716 node_context_11_19039_585716
  intro a
  fin_cases a
  · exact context_12_76156_585623
  · exact context_12_76157_585650
  · exact context_12_76158_585686
  · exact context_12_76159_585715

theorem unmarked_context_10_4759_585717 : frontier 11 ⟨585717, by decide⟩
    (prefixCache 10 4759) (prefixPartial 10 4759) = false := by
  decide +kernel

theorem node_context_10_4759_585717 : EJMOriginalGlobalDAGData.nodes 11 ⟨585717, by decide⟩ =
    .split (coordinate 10) (![⟨585358, by decide⟩,⟨585458, by decide⟩,⟨585591, by decide⟩,⟨585716, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4759_585717 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4759 ⟨585717, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4759
    ⟨585717, by decide⟩ (by decide) (![⟨585358, by decide⟩,⟨585458, by decide⟩,⟨585591, by decide⟩,⟨585716, by decide⟩]) unmarked_context_10_4759_585717 node_context_10_4759_585717
  intro a
  fin_cases a
  · exact context_11_19036_585358
  · exact context_11_19037_585458
  · exact context_11_19038_585591
  · exact context_11_19039_585716

theorem unmarked_context_9_1189_585718 : frontier 12 ⟨585718, by decide⟩
    (prefixCache 9 1189) (prefixPartial 9 1189) = false := by
  decide +kernel

theorem node_context_9_1189_585718 : EJMOriginalGlobalDAGData.nodes 12 ⟨585718, by decide⟩ =
    .split (coordinate 9) (![⟨583999, by decide⟩,⟨584634, by decide⟩,⟨585197, by decide⟩,⟨585717, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1189_585718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1189 ⟨585718, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1189
    ⟨585718, by decide⟩ (by decide) (![⟨583999, by decide⟩,⟨584634, by decide⟩,⟨585197, by decide⟩,⟨585717, by decide⟩]) unmarked_context_9_1189_585718 node_context_9_1189_585718
  intro a
  fin_cases a
  · exact context_10_4756_583999
  · exact context_10_4757_584634
  · exact context_10_4758_585197
  · exact context_10_4759_585717

theorem selected_cut_23129 : selected 9 ⟨585741, by decide⟩
    (prefixPartial 12 76160) = some ⟨12, 2, 0, 585741, 76160, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_76160_585741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76160 ⟨585741, by decide⟩ :=
  accepted_of_selected 12 76160 ⟨585741, by decide⟩ ⟨12, 2, 0, 585741, 76160, 1893, 65536⟩
    (by decide) selected_cut_23129

theorem selected_cut_23130 : selected 9 ⟨585765, by decide⟩
    (prefixPartial 12 76161) = some ⟨12, 2, 0, 585765, 76161, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_76161_585765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76161 ⟨585765, by decide⟩ :=
  accepted_of_selected 12 76161 ⟨585765, by decide⟩ ⟨12, 2, 0, 585765, 76161, 2021, 65536⟩
    (by decide) selected_cut_23130

theorem selected_cut_23131 : selected 9 ⟨585797, by decide⟩
    (prefixPartial 12 76162) = some ⟨12, 2, 0, 585797, 76162, 2633, 65536⟩ := by
  decide +kernel

theorem context_12_76162_585797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76162 ⟨585797, by decide⟩ :=
  accepted_of_selected 12 76162 ⟨585797, by decide⟩ ⟨12, 2, 0, 585797, 76162, 2633, 65536⟩
    (by decide) selected_cut_23131

theorem selected_cut_23132 : selected 9 ⟨585824, by decide⟩
    (prefixPartial 12 76163) = some ⟨12, 2, 0, 585824, 76163, 2357, 65536⟩ := by
  decide +kernel

theorem context_12_76163_585824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76163 ⟨585824, by decide⟩ :=
  accepted_of_selected 12 76163 ⟨585824, by decide⟩ ⟨12, 2, 0, 585824, 76163, 2357, 65536⟩
    (by decide) selected_cut_23132

theorem unmarked_context_11_19040_585825 : frontier 10 ⟨585825, by decide⟩
    (prefixCache 11 19040) (prefixPartial 11 19040) = false := by
  decide +kernel

theorem node_context_11_19040_585825 : EJMOriginalGlobalDAGData.nodes 10 ⟨585825, by decide⟩ =
    .split (coordinate 11) (![⟨585741, by decide⟩,⟨585765, by decide⟩,⟨585797, by decide⟩,⟨585824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19040_585825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19040 ⟨585825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19040
    ⟨585825, by decide⟩ (by decide) (![⟨585741, by decide⟩,⟨585765, by decide⟩,⟨585797, by decide⟩,⟨585824, by decide⟩]) unmarked_context_11_19040_585825 node_context_11_19040_585825
  intro a
  fin_cases a
  · exact context_12_76160_585741
  · exact context_12_76161_585765
  · exact context_12_76162_585797
  · exact context_12_76163_585824

theorem selected_cut_23133 : selected 9 ⟨585846, by decide⟩
    (prefixPartial 12 76164) = some ⟨12, 2, 0, 585846, 76164, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_76164_585846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76164 ⟨585846, by decide⟩ :=
  accepted_of_selected 12 76164 ⟨585846, by decide⟩ ⟨12, 2, 0, 585846, 76164, 1617, 65536⟩
    (by decide) selected_cut_23133

theorem selected_cut_23134 : selected 9 ⟨585872, by decide⟩
    (prefixPartial 12 76165) = some ⟨12, 2, 0, 585872, 76165, 2945, 65536⟩ := by
  decide +kernel

theorem context_12_76165_585872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76165 ⟨585872, by decide⟩ :=
  accepted_of_selected 12 76165 ⟨585872, by decide⟩ ⟨12, 2, 0, 585872, 76165, 2945, 65536⟩
    (by decide) selected_cut_23134

theorem selected_cut_23135 : selected 9 ⟨585895, by decide⟩
    (prefixPartial 12 76166) = some ⟨12, 2, 0, 585895, 76166, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_76166_585895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76166 ⟨585895, by decide⟩ :=
  accepted_of_selected 12 76166 ⟨585895, by decide⟩ ⟨12, 2, 0, 585895, 76166, 2149, 65536⟩
    (by decide) selected_cut_23135

theorem selected_cut_23136 : selected 9 ⟨585916, by decide⟩
    (prefixPartial 12 76167) = some ⟨12, 2, 0, 585916, 76167, 2009, 65536⟩ := by
  decide +kernel

theorem context_12_76167_585916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76167 ⟨585916, by decide⟩ :=
  accepted_of_selected 12 76167 ⟨585916, by decide⟩ ⟨12, 2, 0, 585916, 76167, 2009, 65536⟩
    (by decide) selected_cut_23136

theorem unmarked_context_11_19041_585917 : frontier 10 ⟨585917, by decide⟩
    (prefixCache 11 19041) (prefixPartial 11 19041) = false := by
  decide +kernel

theorem node_context_11_19041_585917 : EJMOriginalGlobalDAGData.nodes 10 ⟨585917, by decide⟩ =
    .split (coordinate 11) (![⟨585846, by decide⟩,⟨585872, by decide⟩,⟨585895, by decide⟩,⟨585916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19041_585917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19041 ⟨585917, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19041
    ⟨585917, by decide⟩ (by decide) (![⟨585846, by decide⟩,⟨585872, by decide⟩,⟨585895, by decide⟩,⟨585916, by decide⟩]) unmarked_context_11_19041_585917 node_context_11_19041_585917
  intro a
  fin_cases a
  · exact context_12_76164_585846
  · exact context_12_76165_585872
  · exact context_12_76166_585895
  · exact context_12_76167_585916

theorem selected_cut_23137 : selected 9 ⟨585942, by decide⟩
    (prefixPartial 12 76168) = some ⟨12, 2, 0, 585942, 76168, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_76168_585942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76168 ⟨585942, by decide⟩ :=
  accepted_of_selected 12 76168 ⟨585942, by decide⟩ ⟨12, 2, 0, 585942, 76168, 1809, 65536⟩
    (by decide) selected_cut_23137

theorem selected_cut_23138 : selected 9 ⟨585966, by decide⟩
    (prefixPartial 12 76169) = some ⟨12, 2, 0, 585966, 76169, 1957, 65536⟩ := by
  decide +kernel

theorem context_12_76169_585966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76169 ⟨585966, by decide⟩ :=
  accepted_of_selected 12 76169 ⟨585966, by decide⟩ ⟨12, 2, 0, 585966, 76169, 1957, 65536⟩
    (by decide) selected_cut_23138

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
