/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover220
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21219 : selected 8 ⟨542757, by decide⟩
    (prefixPartial 13 299418) = some ⟨13, 2, 0, 542757, 299418, 1837, 16384⟩ := by
  decide +kernel

theorem context_13_299418_542757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299418 ⟨542757, by decide⟩ :=
  accepted_of_selected 13 299418 ⟨542757, by decide⟩ ⟨13, 2, 0, 542757, 299418, 1837, 16384⟩
    (by decide) selected_cut_21219

theorem selected_cut_21220 : selected 8 ⟨542775, by decide⟩
    (prefixPartial 13 299419) = some ⟨13, 2, 0, 542775, 299419, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_299419_542775 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299419 ⟨542775, by decide⟩ :=
  accepted_of_selected 13 299419 ⟨542775, by decide⟩ ⟨13, 2, 0, 542775, 299419, 1145, 16384⟩
    (by decide) selected_cut_21220

theorem unmarked_context_12_74854_542776 : frontier 9 ⟨542776, by decide⟩
    (prefixCache 12 74854) (prefixPartial 12 74854) = false := by
  decide +kernel

theorem node_context_12_74854_542776 : EJMOriginalGlobalDAGData.nodes 9 ⟨542776, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542731, by decide⟩,⟨542757, by decide⟩,⟨542775, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74854_542776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74854 ⟨542776, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74854
    ⟨542776, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542731, by decide⟩,⟨542757, by decide⟩,⟨542775, by decide⟩]) unmarked_context_12_74854_542776 node_context_12_74854_542776
  intro a
  fin_cases a
  · exact context_13_299416_3444
  · exact context_13_299417_542731
  · exact context_13_299418_542757
  · exact context_13_299419_542775

theorem selected_cut_21221 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299420) = some ⟨13, 1, 0, 3444, 299420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299420, 1, 16384⟩
    (by decide) selected_cut_21221

theorem selected_cut_21222 : selected 8 ⟨542789, by decide⟩
    (prefixPartial 13 299421) = some ⟨13, 2, 0, 542789, 299421, 1265, 16384⟩ := by
  decide +kernel

theorem context_13_299421_542789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299421 ⟨542789, by decide⟩ :=
  accepted_of_selected 13 299421 ⟨542789, by decide⟩ ⟨13, 2, 0, 542789, 299421, 1265, 16384⟩
    (by decide) selected_cut_21222

theorem selected_cut_21223 : selected 8 ⟨542815, by decide⟩
    (prefixPartial 13 299422) = some ⟨13, 2, 0, 542815, 299422, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_299422_542815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299422 ⟨542815, by decide⟩ :=
  accepted_of_selected 13 299422 ⟨542815, by decide⟩ ⟨13, 2, 0, 542815, 299422, 1985, 16384⟩
    (by decide) selected_cut_21223

theorem selected_cut_21224 : selected 8 ⟨542822, by decide⟩
    (prefixPartial 13 299423) = some ⟨13, 2, 0, 542822, 299423, 989, 16384⟩ := by
  decide +kernel

theorem context_13_299423_542822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299423 ⟨542822, by decide⟩ :=
  accepted_of_selected 13 299423 ⟨542822, by decide⟩ ⟨13, 2, 0, 542822, 299423, 989, 16384⟩
    (by decide) selected_cut_21224

theorem unmarked_context_12_74855_542823 : frontier 9 ⟨542823, by decide⟩
    (prefixCache 12 74855) (prefixPartial 12 74855) = false := by
  decide +kernel

theorem node_context_12_74855_542823 : EJMOriginalGlobalDAGData.nodes 9 ⟨542823, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨542789, by decide⟩,⟨542815, by decide⟩,⟨542822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74855_542823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74855 ⟨542823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74855
    ⟨542823, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨542789, by decide⟩,⟨542815, by decide⟩,⟨542822, by decide⟩]) unmarked_context_12_74855_542823 node_context_12_74855_542823
  intro a
  fin_cases a
  · exact context_13_299420_3444
  · exact context_13_299421_542789
  · exact context_13_299422_542815
  · exact context_13_299423_542822

theorem unmarked_context_11_18713_542824 : frontier 10 ⟨542824, by decide⟩
    (prefixCache 11 18713) (prefixPartial 11 18713) = false := by
  decide +kernel

theorem node_context_11_18713_542824 : EJMOriginalGlobalDAGData.nodes 10 ⟨542824, by decide⟩ =
    .split (coordinate 11) (![⟨542658, by decide⟩,⟨542700, by decide⟩,⟨542776, by decide⟩,⟨542823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18713_542824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18713 ⟨542824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18713
    ⟨542824, by decide⟩ (by decide) (![⟨542658, by decide⟩,⟨542700, by decide⟩,⟨542776, by decide⟩,⟨542823, by decide⟩]) unmarked_context_11_18713_542824 node_context_11_18713_542824
  intro a
  fin_cases a
  · exact context_12_74852_542658
  · exact context_12_74853_542700
  · exact context_12_74854_542776
  · exact context_12_74855_542823

theorem selected_cut_21225 : selected 9 ⟨542864, by decide⟩
    (prefixPartial 12 74856) = some ⟨12, 2, 0, 542864, 74856, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_74856_542864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74856 ⟨542864, by decide⟩ :=
  accepted_of_selected 12 74856 ⟨542864, by decide⟩ ⟨12, 2, 0, 542864, 74856, 3493, 65536⟩
    (by decide) selected_cut_21225

theorem selected_cut_21226 : selected 9 ⟨542903, by decide⟩
    (prefixPartial 12 74857) = some ⟨12, 2, 0, 542903, 74857, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_74857_542903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74857 ⟨542903, by decide⟩ :=
  accepted_of_selected 12 74857 ⟨542903, by decide⟩ ⟨12, 2, 0, 542903, 74857, 3705, 65536⟩
    (by decide) selected_cut_21226

theorem selected_cut_21227 : selected 9 ⟨542955, by decide⟩
    (prefixPartial 12 74858) = some ⟨12, 2, 0, 542955, 74858, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_74858_542955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74858 ⟨542955, by decide⟩ :=
  accepted_of_selected 12 74858 ⟨542955, by decide⟩ ⟨12, 2, 0, 542955, 74858, 3893, 65536⟩
    (by decide) selected_cut_21227

theorem selected_cut_21228 : selected 9 ⟨543003, by decide⟩
    (prefixPartial 12 74859) = some ⟨12, 2, 0, 543003, 74859, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_74859_543003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74859 ⟨543003, by decide⟩ :=
  accepted_of_selected 12 74859 ⟨543003, by decide⟩ ⟨12, 2, 0, 543003, 74859, 3965, 65536⟩
    (by decide) selected_cut_21228

theorem unmarked_context_11_18714_543004 : frontier 10 ⟨543004, by decide⟩
    (prefixCache 11 18714) (prefixPartial 11 18714) = false := by
  decide +kernel

theorem node_context_11_18714_543004 : EJMOriginalGlobalDAGData.nodes 10 ⟨543004, by decide⟩ =
    .split (coordinate 11) (![⟨542864, by decide⟩,⟨542903, by decide⟩,⟨542955, by decide⟩,⟨543003, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18714_543004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18714 ⟨543004, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18714
    ⟨543004, by decide⟩ (by decide) (![⟨542864, by decide⟩,⟨542903, by decide⟩,⟨542955, by decide⟩,⟨543003, by decide⟩]) unmarked_context_11_18714_543004 node_context_11_18714_543004
  intro a
  fin_cases a
  · exact context_12_74856_542864
  · exact context_12_74857_542903
  · exact context_12_74858_542955
  · exact context_12_74859_543003

theorem selected_cut_21229 : selected 9 ⟨543039, by decide⟩
    (prefixPartial 12 74860) = some ⟨12, 2, 0, 543039, 74860, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_74860_543039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74860 ⟨543039, by decide⟩ :=
  accepted_of_selected 12 74860 ⟨543039, by decide⟩ ⟨12, 2, 0, 543039, 74860, 3465, 65536⟩
    (by decide) selected_cut_21229

theorem selected_cut_21230 : selected 9 ⟨543076, by decide⟩
    (prefixPartial 12 74861) = some ⟨12, 2, 0, 543076, 74861, 3633, 65536⟩ := by
  decide +kernel

theorem context_12_74861_543076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74861 ⟨543076, by decide⟩ :=
  accepted_of_selected 12 74861 ⟨543076, by decide⟩ ⟨12, 2, 0, 543076, 74861, 3633, 65536⟩
    (by decide) selected_cut_21230

theorem selected_cut_21231 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 299448) = some ⟨13, 1, 0, 3444, 299448, 1, 16384⟩ := by
  decide +kernel

theorem context_13_299448_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299448 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 299448 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 299448, 1, 16384⟩
    (by decide) selected_cut_21231

theorem selected_cut_21232 : selected 8 ⟨543099, by decide⟩
    (prefixPartial 13 299449) = some ⟨13, 2, 0, 543099, 299449, 1169, 16384⟩ := by
  decide +kernel

theorem context_13_299449_543099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299449 ⟨543099, by decide⟩ :=
  accepted_of_selected 13 299449 ⟨543099, by decide⟩ ⟨13, 2, 0, 543099, 299449, 1169, 16384⟩
    (by decide) selected_cut_21232

theorem selected_cut_21233 : selected 8 ⟨543125, by decide⟩
    (prefixPartial 13 299450) = some ⟨13, 2, 0, 543125, 299450, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_299450_543125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299450 ⟨543125, by decide⟩ :=
  accepted_of_selected 13 299450 ⟨543125, by decide⟩ ⟨13, 2, 0, 543125, 299450, 1941, 16384⟩
    (by decide) selected_cut_21233

theorem selected_cut_21234 : selected 8 ⟨543131, by decide⟩
    (prefixPartial 13 299451) = some ⟨13, 2, 0, 543131, 299451, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_299451_543131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 299451 ⟨543131, by decide⟩ :=
  accepted_of_selected 13 299451 ⟨543131, by decide⟩ ⟨13, 2, 0, 543131, 299451, 1109, 16384⟩
    (by decide) selected_cut_21234

theorem unmarked_context_12_74862_543132 : frontier 9 ⟨543132, by decide⟩
    (prefixCache 12 74862) (prefixPartial 12 74862) = false := by
  decide +kernel

theorem node_context_12_74862_543132 : EJMOriginalGlobalDAGData.nodes 9 ⟨543132, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨543099, by decide⟩,⟨543125, by decide⟩,⟨543131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_74862_543132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74862 ⟨543132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 74862
    ⟨543132, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨543099, by decide⟩,⟨543125, by decide⟩,⟨543131, by decide⟩]) unmarked_context_12_74862_543132 node_context_12_74862_543132
  intro a
  fin_cases a
  · exact context_13_299448_3444
  · exact context_13_299449_543099
  · exact context_13_299450_543125
  · exact context_13_299451_543131

theorem selected_cut_21235 : selected 9 ⟨543171, by decide⟩
    (prefixPartial 12 74863) = some ⟨12, 2, 0, 543171, 74863, 3721, 65536⟩ := by
  decide +kernel

theorem context_12_74863_543171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74863 ⟨543171, by decide⟩ :=
  accepted_of_selected 12 74863 ⟨543171, by decide⟩ ⟨12, 2, 0, 543171, 74863, 3721, 65536⟩
    (by decide) selected_cut_21235

theorem unmarked_context_11_18715_543172 : frontier 10 ⟨543172, by decide⟩
    (prefixCache 11 18715) (prefixPartial 11 18715) = false := by
  decide +kernel

theorem node_context_11_18715_543172 : EJMOriginalGlobalDAGData.nodes 10 ⟨543172, by decide⟩ =
    .split (coordinate 11) (![⟨543039, by decide⟩,⟨543076, by decide⟩,⟨543132, by decide⟩,⟨543171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18715_543172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18715 ⟨543172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18715
    ⟨543172, by decide⟩ (by decide) (![⟨543039, by decide⟩,⟨543076, by decide⟩,⟨543132, by decide⟩,⟨543171, by decide⟩]) unmarked_context_11_18715_543172 node_context_11_18715_543172
  intro a
  fin_cases a
  · exact context_12_74860_543039
  · exact context_12_74861_543076
  · exact context_12_74862_543132
  · exact context_12_74863_543171

theorem unmarked_context_10_4678_543173 : frontier 11 ⟨543173, by decide⟩
    (prefixCache 10 4678) (prefixPartial 10 4678) = false := by
  decide +kernel

theorem node_context_10_4678_543173 : EJMOriginalGlobalDAGData.nodes 11 ⟨543173, by decide⟩ =
    .split (coordinate 10) (![⟨542613, by decide⟩,⟨542824, by decide⟩,⟨543004, by decide⟩,⟨543172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4678_543173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4678 ⟨543173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4678
    ⟨543173, by decide⟩ (by decide) (![⟨542613, by decide⟩,⟨542824, by decide⟩,⟨543004, by decide⟩,⟨543172, by decide⟩]) unmarked_context_10_4678_543173 node_context_10_4678_543173
  intro a
  fin_cases a
  · exact context_11_18712_542613
  · exact context_11_18713_542824
  · exact context_11_18714_543004
  · exact context_11_18715_543172

theorem selected_cut_21236 : selected 9 ⟨543329, by decide⟩
    (prefixPartial 12 74864) = some ⟨12, 2, 0, 543329, 74864, 2337, 65536⟩ := by
  decide +kernel

theorem context_12_74864_543329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74864 ⟨543329, by decide⟩ :=
  accepted_of_selected 12 74864 ⟨543329, by decide⟩ ⟨12, 2, 0, 543329, 74864, 2337, 65536⟩
    (by decide) selected_cut_21236

theorem selected_cut_21237 : selected 9 ⟨543360, by decide⟩
    (prefixPartial 12 74865) = some ⟨12, 2, 0, 543360, 74865, 3185, 65536⟩ := by
  decide +kernel

theorem context_12_74865_543360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74865 ⟨543360, by decide⟩ :=
  accepted_of_selected 12 74865 ⟨543360, by decide⟩ ⟨12, 2, 0, 543360, 74865, 3185, 65536⟩
    (by decide) selected_cut_21237

theorem selected_cut_21238 : selected 9 ⟨543394, by decide⟩
    (prefixPartial 12 74866) = some ⟨12, 2, 0, 543394, 74866, 3517, 65536⟩ := by
  decide +kernel

theorem context_12_74866_543394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74866 ⟨543394, by decide⟩ :=
  accepted_of_selected 12 74866 ⟨543394, by decide⟩ ⟨12, 2, 0, 543394, 74866, 3517, 65536⟩
    (by decide) selected_cut_21238

theorem selected_cut_21239 : selected 9 ⟨543440, by decide⟩
    (prefixPartial 12 74867) = some ⟨12, 2, 0, 543440, 74867, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_74867_543440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74867 ⟨543440, by decide⟩ :=
  accepted_of_selected 12 74867 ⟨543440, by decide⟩ ⟨12, 2, 0, 543440, 74867, 3425, 65536⟩
    (by decide) selected_cut_21239

theorem unmarked_context_11_18716_543441 : frontier 10 ⟨543441, by decide⟩
    (prefixCache 11 18716) (prefixPartial 11 18716) = false := by
  decide +kernel

theorem node_context_11_18716_543441 : EJMOriginalGlobalDAGData.nodes 10 ⟨543441, by decide⟩ =
    .split (coordinate 11) (![⟨543329, by decide⟩,⟨543360, by decide⟩,⟨543394, by decide⟩,⟨543440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18716_543441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18716 ⟨543441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18716
    ⟨543441, by decide⟩ (by decide) (![⟨543329, by decide⟩,⟨543360, by decide⟩,⟨543394, by decide⟩,⟨543440, by decide⟩]) unmarked_context_11_18716_543441 node_context_11_18716_543441
  intro a
  fin_cases a
  · exact context_12_74864_543329
  · exact context_12_74865_543360
  · exact context_12_74866_543394
  · exact context_12_74867_543440

theorem selected_cut_21240 : selected 9 ⟨543479, by decide⟩
    (prefixPartial 12 74868) = some ⟨12, 2, 0, 543479, 74868, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_74868_543479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74868 ⟨543479, by decide⟩ :=
  accepted_of_selected 12 74868 ⟨543479, by decide⟩ ⟨12, 2, 0, 543479, 74868, 3293, 65536⟩
    (by decide) selected_cut_21240

theorem selected_cut_21241 : selected 9 ⟨543507, by decide⟩
    (prefixPartial 12 74869) = some ⟨12, 2, 0, 543507, 74869, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_74869_543507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74869 ⟨543507, by decide⟩ :=
  accepted_of_selected 12 74869 ⟨543507, by decide⟩ ⟨12, 2, 0, 543507, 74869, 3217, 65536⟩
    (by decide) selected_cut_21241

theorem selected_cut_21242 : selected 9 ⟨543562, by decide⟩
    (prefixPartial 12 74870) = some ⟨12, 2, 0, 543562, 74870, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_74870_543562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74870 ⟨543562, by decide⟩ :=
  accepted_of_selected 12 74870 ⟨543562, by decide⟩ ⟨12, 2, 0, 543562, 74870, 3857, 65536⟩
    (by decide) selected_cut_21242

theorem selected_cut_21243 : selected 9 ⟨543618, by decide⟩
    (prefixPartial 12 74871) = some ⟨12, 2, 0, 543618, 74871, 3825, 65536⟩ := by
  decide +kernel

theorem context_12_74871_543618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74871 ⟨543618, by decide⟩ :=
  accepted_of_selected 12 74871 ⟨543618, by decide⟩ ⟨12, 2, 0, 543618, 74871, 3825, 65536⟩
    (by decide) selected_cut_21243

theorem unmarked_context_11_18717_543619 : frontier 10 ⟨543619, by decide⟩
    (prefixCache 11 18717) (prefixPartial 11 18717) = false := by
  decide +kernel

theorem node_context_11_18717_543619 : EJMOriginalGlobalDAGData.nodes 10 ⟨543619, by decide⟩ =
    .split (coordinate 11) (![⟨543479, by decide⟩,⟨543507, by decide⟩,⟨543562, by decide⟩,⟨543618, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18717_543619 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18717 ⟨543619, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18717
    ⟨543619, by decide⟩ (by decide) (![⟨543479, by decide⟩,⟨543507, by decide⟩,⟨543562, by decide⟩,⟨543618, by decide⟩]) unmarked_context_11_18717_543619 node_context_11_18717_543619
  intro a
  fin_cases a
  · exact context_12_74868_543479
  · exact context_12_74869_543507
  · exact context_12_74870_543562
  · exact context_12_74871_543618

theorem selected_cut_21244 : selected 9 ⟨543660, by decide⟩
    (prefixPartial 12 74872) = some ⟨12, 2, 0, 543660, 74872, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_74872_543660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74872 ⟨543660, by decide⟩ :=
  accepted_of_selected 12 74872 ⟨543660, by decide⟩ ⟨12, 2, 0, 543660, 74872, 3229, 65536⟩
    (by decide) selected_cut_21244

theorem selected_cut_21245 : selected 9 ⟨543708, by decide⟩
    (prefixPartial 12 74873) = some ⟨12, 2, 0, 543708, 74873, 3413, 65536⟩ := by
  decide +kernel

theorem context_12_74873_543708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74873 ⟨543708, by decide⟩ :=
  accepted_of_selected 12 74873 ⟨543708, by decide⟩ ⟨12, 2, 0, 543708, 74873, 3413, 65536⟩
    (by decide) selected_cut_21245

theorem selected_cut_21246 : selected 9 ⟨543770, by decide⟩
    (prefixPartial 12 74874) = some ⟨12, 2, 0, 543770, 74874, 3561, 65536⟩ := by
  decide +kernel

theorem context_12_74874_543770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74874 ⟨543770, by decide⟩ :=
  accepted_of_selected 12 74874 ⟨543770, by decide⟩ ⟨12, 2, 0, 543770, 74874, 3561, 65536⟩
    (by decide) selected_cut_21246

theorem selected_cut_21247 : selected 9 ⟨543832, by decide⟩
    (prefixPartial 12 74875) = some ⟨12, 2, 0, 543832, 74875, 3673, 65536⟩ := by
  decide +kernel

theorem context_12_74875_543832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74875 ⟨543832, by decide⟩ :=
  accepted_of_selected 12 74875 ⟨543832, by decide⟩ ⟨12, 2, 0, 543832, 74875, 3673, 65536⟩
    (by decide) selected_cut_21247

theorem unmarked_context_11_18718_543833 : frontier 10 ⟨543833, by decide⟩
    (prefixCache 11 18718) (prefixPartial 11 18718) = false := by
  decide +kernel

theorem node_context_11_18718_543833 : EJMOriginalGlobalDAGData.nodes 10 ⟨543833, by decide⟩ =
    .split (coordinate 11) (![⟨543660, by decide⟩,⟨543708, by decide⟩,⟨543770, by decide⟩,⟨543832, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18718_543833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18718 ⟨543833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18718
    ⟨543833, by decide⟩ (by decide) (![⟨543660, by decide⟩,⟨543708, by decide⟩,⟨543770, by decide⟩,⟨543832, by decide⟩]) unmarked_context_11_18718_543833 node_context_11_18718_543833
  intro a
  fin_cases a
  · exact context_12_74872_543660
  · exact context_12_74873_543708
  · exact context_12_74874_543770
  · exact context_12_74875_543832

theorem selected_cut_21248 : selected 9 ⟨543868, by decide⟩
    (prefixPartial 12 74876) = some ⟨12, 2, 0, 543868, 74876, 2953, 65536⟩ := by
  decide +kernel

theorem context_12_74876_543868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74876 ⟨543868, by decide⟩ :=
  accepted_of_selected 12 74876 ⟨543868, by decide⟩ ⟨12, 2, 0, 543868, 74876, 2953, 65536⟩
    (by decide) selected_cut_21248

theorem selected_cut_21249 : selected 9 ⟨543904, by decide⟩
    (prefixPartial 12 74877) = some ⟨12, 2, 0, 543904, 74877, 3097, 65536⟩ := by
  decide +kernel

theorem context_12_74877_543904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74877 ⟨543904, by decide⟩ :=
  accepted_of_selected 12 74877 ⟨543904, by decide⟩ ⟨12, 2, 0, 543904, 74877, 3097, 65536⟩
    (by decide) selected_cut_21249

theorem selected_cut_21250 : selected 9 ⟨543944, by decide⟩
    (prefixPartial 12 74878) = some ⟨12, 2, 0, 543944, 74878, 3465, 65536⟩ := by
  decide +kernel

theorem context_12_74878_543944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74878 ⟨543944, by decide⟩ :=
  accepted_of_selected 12 74878 ⟨543944, by decide⟩ ⟨12, 2, 0, 543944, 74878, 3465, 65536⟩
    (by decide) selected_cut_21250

theorem selected_cut_21251 : selected 9 ⟨543988, by decide⟩
    (prefixPartial 12 74879) = some ⟨12, 2, 0, 543988, 74879, 3081, 65536⟩ := by
  decide +kernel

theorem context_12_74879_543988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74879 ⟨543988, by decide⟩ :=
  accepted_of_selected 12 74879 ⟨543988, by decide⟩ ⟨12, 2, 0, 543988, 74879, 3081, 65536⟩
    (by decide) selected_cut_21251

theorem unmarked_context_11_18719_543989 : frontier 10 ⟨543989, by decide⟩
    (prefixCache 11 18719) (prefixPartial 11 18719) = false := by
  decide +kernel

theorem node_context_11_18719_543989 : EJMOriginalGlobalDAGData.nodes 10 ⟨543989, by decide⟩ =
    .split (coordinate 11) (![⟨543868, by decide⟩,⟨543904, by decide⟩,⟨543944, by decide⟩,⟨543988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18719_543989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18719 ⟨543989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18719
    ⟨543989, by decide⟩ (by decide) (![⟨543868, by decide⟩,⟨543904, by decide⟩,⟨543944, by decide⟩,⟨543988, by decide⟩]) unmarked_context_11_18719_543989 node_context_11_18719_543989
  intro a
  fin_cases a
  · exact context_12_74876_543868
  · exact context_12_74877_543904
  · exact context_12_74878_543944
  · exact context_12_74879_543988

theorem unmarked_context_10_4679_543990 : frontier 11 ⟨543990, by decide⟩
    (prefixCache 10 4679) (prefixPartial 10 4679) = false := by
  decide +kernel

theorem node_context_10_4679_543990 : EJMOriginalGlobalDAGData.nodes 11 ⟨543990, by decide⟩ =
    .split (coordinate 10) (![⟨543441, by decide⟩,⟨543619, by decide⟩,⟨543833, by decide⟩,⟨543989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4679_543990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4679 ⟨543990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4679
    ⟨543990, by decide⟩ (by decide) (![⟨543441, by decide⟩,⟨543619, by decide⟩,⟨543833, by decide⟩,⟨543989, by decide⟩]) unmarked_context_10_4679_543990 node_context_10_4679_543990
  intro a
  fin_cases a
  · exact context_11_18716_543441
  · exact context_11_18717_543619
  · exact context_11_18718_543833
  · exact context_11_18719_543989

theorem unmarked_context_9_1169_543991 : frontier 12 ⟨543991, by decide⟩
    (prefixCache 9 1169) (prefixPartial 9 1169) = false := by
  decide +kernel

theorem node_context_9_1169_543991 : EJMOriginalGlobalDAGData.nodes 12 ⟨543991, by decide⟩ =
    .split (coordinate 9) (![⟨541907, by decide⟩,⟨542400, by decide⟩,⟨543173, by decide⟩,⟨543990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1169_543991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1169 ⟨543991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1169
    ⟨543991, by decide⟩ (by decide) (![⟨541907, by decide⟩,⟨542400, by decide⟩,⟨543173, by decide⟩,⟨543990, by decide⟩]) unmarked_context_9_1169_543991 node_context_9_1169_543991
  intro a
  fin_cases a
  · exact context_10_4676_541907
  · exact context_10_4677_542400
  · exact context_10_4678_543173
  · exact context_10_4679_543990

theorem selected_cut_21252 : selected 9 ⟨450982, by decide⟩
    (prefixPartial 12 74880) = some ⟨12, 1, 0, 450982, 74880, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74880_450982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74880 ⟨450982, by decide⟩ :=
  accepted_of_selected 12 74880 ⟨450982, by decide⟩ ⟨12, 1, 0, 450982, 74880, 1, 65536⟩
    (by decide) selected_cut_21252

theorem selected_cut_21253 : selected 9 ⟨544008, by decide⟩
    (prefixPartial 12 74881) = some ⟨12, 2, 0, 544008, 74881, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_74881_544008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74881 ⟨544008, by decide⟩ :=
  accepted_of_selected 12 74881 ⟨544008, by decide⟩ ⟨12, 2, 0, 544008, 74881, 1817, 65536⟩
    (by decide) selected_cut_21253

theorem selected_cut_21254 : selected 9 ⟨544028, by decide⟩
    (prefixPartial 12 74882) = some ⟨12, 2, 0, 544028, 74882, 1757, 65536⟩ := by
  decide +kernel

theorem context_12_74882_544028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74882 ⟨544028, by decide⟩ :=
  accepted_of_selected 12 74882 ⟨544028, by decide⟩ ⟨12, 2, 0, 544028, 74882, 1757, 65536⟩
    (by decide) selected_cut_21254

theorem selected_cut_21255 : selected 9 ⟨544051, by decide⟩
    (prefixPartial 12 74883) = some ⟨12, 2, 0, 544051, 74883, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_74883_544051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74883 ⟨544051, by decide⟩ :=
  accepted_of_selected 12 74883 ⟨544051, by decide⟩ ⟨12, 2, 0, 544051, 74883, 1813, 65536⟩
    (by decide) selected_cut_21255

theorem unmarked_context_11_18720_544052 : frontier 10 ⟨544052, by decide⟩
    (prefixCache 11 18720) (prefixPartial 11 18720) = false := by
  decide +kernel

theorem node_context_11_18720_544052 : EJMOriginalGlobalDAGData.nodes 10 ⟨544052, by decide⟩ =
    .split (coordinate 11) (![⟨450982, by decide⟩,⟨544008, by decide⟩,⟨544028, by decide⟩,⟨544051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18720_544052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18720 ⟨544052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18720
    ⟨544052, by decide⟩ (by decide) (![⟨450982, by decide⟩,⟨544008, by decide⟩,⟨544028, by decide⟩,⟨544051, by decide⟩]) unmarked_context_11_18720_544052 node_context_11_18720_544052
  intro a
  fin_cases a
  · exact context_12_74880_450982
  · exact context_12_74881_544008
  · exact context_12_74882_544028
  · exact context_12_74883_544051

theorem selected_cut_21256 : selected 9 ⟨544072, by decide⟩
    (prefixPartial 12 74884) = some ⟨12, 2, 0, 544072, 74884, 1725, 65536⟩ := by
  decide +kernel

theorem context_12_74884_544072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74884 ⟨544072, by decide⟩ :=
  accepted_of_selected 12 74884 ⟨544072, by decide⟩ ⟨12, 2, 0, 544072, 74884, 1725, 65536⟩
    (by decide) selected_cut_21256

theorem selected_cut_21257 : selected 9 ⟨544088, by decide⟩
    (prefixPartial 12 74885) = some ⟨12, 2, 0, 544088, 74885, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_74885_544088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74885 ⟨544088, by decide⟩ :=
  accepted_of_selected 12 74885 ⟨544088, by decide⟩ ⟨12, 2, 0, 544088, 74885, 1937, 65536⟩
    (by decide) selected_cut_21257

theorem selected_cut_21258 : selected 9 ⟨544110, by decide⟩
    (prefixPartial 12 74886) = some ⟨12, 2, 0, 544110, 74886, 2021, 65536⟩ := by
  decide +kernel

theorem context_12_74886_544110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74886 ⟨544110, by decide⟩ :=
  accepted_of_selected 12 74886 ⟨544110, by decide⟩ ⟨12, 2, 0, 544110, 74886, 2021, 65536⟩
    (by decide) selected_cut_21258

theorem selected_cut_21259 : selected 9 ⟨544135, by decide⟩
    (prefixPartial 12 74887) = some ⟨12, 2, 0, 544135, 74887, 2117, 65536⟩ := by
  decide +kernel

theorem context_12_74887_544135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74887 ⟨544135, by decide⟩ :=
  accepted_of_selected 12 74887 ⟨544135, by decide⟩ ⟨12, 2, 0, 544135, 74887, 2117, 65536⟩
    (by decide) selected_cut_21259

theorem unmarked_context_11_18721_544136 : frontier 10 ⟨544136, by decide⟩
    (prefixCache 11 18721) (prefixPartial 11 18721) = false := by
  decide +kernel

theorem node_context_11_18721_544136 : EJMOriginalGlobalDAGData.nodes 10 ⟨544136, by decide⟩ =
    .split (coordinate 11) (![⟨544072, by decide⟩,⟨544088, by decide⟩,⟨544110, by decide⟩,⟨544135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18721_544136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18721 ⟨544136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18721
    ⟨544136, by decide⟩ (by decide) (![⟨544072, by decide⟩,⟨544088, by decide⟩,⟨544110, by decide⟩,⟨544135, by decide⟩]) unmarked_context_11_18721_544136 node_context_11_18721_544136
  intro a
  fin_cases a
  · exact context_12_74884_544072
  · exact context_12_74885_544088
  · exact context_12_74886_544110
  · exact context_12_74887_544135

theorem selected_cut_21260 : selected 9 ⟨544155, by decide⟩
    (prefixPartial 12 74888) = some ⟨12, 2, 0, 544155, 74888, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_74888_544155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74888 ⟨544155, by decide⟩ :=
  accepted_of_selected 12 74888 ⟨544155, by decide⟩ ⟨12, 2, 0, 544155, 74888, 1917, 65536⟩
    (by decide) selected_cut_21260

theorem selected_cut_21261 : selected 9 ⟨544184, by decide⟩
    (prefixPartial 12 74889) = some ⟨12, 2, 0, 544184, 74889, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_74889_544184 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74889 ⟨544184, by decide⟩ :=
  accepted_of_selected 12 74889 ⟨544184, by decide⟩ ⟨12, 2, 0, 544184, 74889, 2229, 65536⟩
    (by decide) selected_cut_21261

theorem selected_cut_21262 : selected 9 ⟨544211, by decide⟩
    (prefixPartial 12 74890) = some ⟨12, 2, 0, 544211, 74890, 2101, 65536⟩ := by
  decide +kernel

theorem context_12_74890_544211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74890 ⟨544211, by decide⟩ :=
  accepted_of_selected 12 74890 ⟨544211, by decide⟩ ⟨12, 2, 0, 544211, 74890, 2101, 65536⟩
    (by decide) selected_cut_21262

theorem selected_cut_21263 : selected 9 ⟨544243, by decide⟩
    (prefixPartial 12 74891) = some ⟨12, 2, 0, 544243, 74891, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_74891_544243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74891 ⟨544243, by decide⟩ :=
  accepted_of_selected 12 74891 ⟨544243, by decide⟩ ⟨12, 2, 0, 544243, 74891, 2177, 65536⟩
    (by decide) selected_cut_21263

theorem unmarked_context_11_18722_544244 : frontier 10 ⟨544244, by decide⟩
    (prefixCache 11 18722) (prefixPartial 11 18722) = false := by
  decide +kernel

theorem node_context_11_18722_544244 : EJMOriginalGlobalDAGData.nodes 10 ⟨544244, by decide⟩ =
    .split (coordinate 11) (![⟨544155, by decide⟩,⟨544184, by decide⟩,⟨544211, by decide⟩,⟨544243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18722_544244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18722 ⟨544244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18722
    ⟨544244, by decide⟩ (by decide) (![⟨544155, by decide⟩,⟨544184, by decide⟩,⟨544211, by decide⟩,⟨544243, by decide⟩]) unmarked_context_11_18722_544244 node_context_11_18722_544244
  intro a
  fin_cases a
  · exact context_12_74888_544155
  · exact context_12_74889_544184
  · exact context_12_74890_544211
  · exact context_12_74891_544243

theorem selected_cut_21264 : selected 9 ⟨544258, by decide⟩
    (prefixPartial 12 74892) = some ⟨12, 2, 0, 544258, 74892, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_74892_544258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74892 ⟨544258, by decide⟩ :=
  accepted_of_selected 12 74892 ⟨544258, by decide⟩ ⟨12, 2, 0, 544258, 74892, 1645, 65536⟩
    (by decide) selected_cut_21264

theorem selected_cut_21265 : selected 9 ⟨544275, by decide⟩
    (prefixPartial 12 74893) = some ⟨12, 2, 0, 544275, 74893, 1901, 65536⟩ := by
  decide +kernel

theorem context_12_74893_544275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74893 ⟨544275, by decide⟩ :=
  accepted_of_selected 12 74893 ⟨544275, by decide⟩ ⟨12, 2, 0, 544275, 74893, 1901, 65536⟩
    (by decide) selected_cut_21265

theorem selected_cut_21266 : selected 9 ⟨544300, by decide⟩
    (prefixPartial 12 74894) = some ⟨12, 2, 0, 544300, 74894, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_74894_544300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74894 ⟨544300, by decide⟩ :=
  accepted_of_selected 12 74894 ⟨544300, by decide⟩ ⟨12, 2, 0, 544300, 74894, 1961, 65536⟩
    (by decide) selected_cut_21266

theorem selected_cut_21267 : selected 9 ⟨544318, by decide⟩
    (prefixPartial 12 74895) = some ⟨12, 2, 0, 544318, 74895, 1849, 65536⟩ := by
  decide +kernel

theorem context_12_74895_544318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74895 ⟨544318, by decide⟩ :=
  accepted_of_selected 12 74895 ⟨544318, by decide⟩ ⟨12, 2, 0, 544318, 74895, 1849, 65536⟩
    (by decide) selected_cut_21267

theorem unmarked_context_11_18723_544319 : frontier 10 ⟨544319, by decide⟩
    (prefixCache 11 18723) (prefixPartial 11 18723) = false := by
  decide +kernel

theorem node_context_11_18723_544319 : EJMOriginalGlobalDAGData.nodes 10 ⟨544319, by decide⟩ =
    .split (coordinate 11) (![⟨544258, by decide⟩,⟨544275, by decide⟩,⟨544300, by decide⟩,⟨544318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18723_544319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18723 ⟨544319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18723
    ⟨544319, by decide⟩ (by decide) (![⟨544258, by decide⟩,⟨544275, by decide⟩,⟨544300, by decide⟩,⟨544318, by decide⟩]) unmarked_context_11_18723_544319 node_context_11_18723_544319
  intro a
  fin_cases a
  · exact context_12_74892_544258
  · exact context_12_74893_544275
  · exact context_12_74894_544300
  · exact context_12_74895_544318

theorem unmarked_context_10_4680_544320 : frontier 11 ⟨544320, by decide⟩
    (prefixCache 10 4680) (prefixPartial 10 4680) = false := by
  decide +kernel

theorem node_context_10_4680_544320 : EJMOriginalGlobalDAGData.nodes 11 ⟨544320, by decide⟩ =
    .split (coordinate 10) (![⟨544052, by decide⟩,⟨544136, by decide⟩,⟨544244, by decide⟩,⟨544319, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4680_544320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4680 ⟨544320, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4680
    ⟨544320, by decide⟩ (by decide) (![⟨544052, by decide⟩,⟨544136, by decide⟩,⟨544244, by decide⟩,⟨544319, by decide⟩]) unmarked_context_10_4680_544320 node_context_10_4680_544320
  intro a
  fin_cases a
  · exact context_11_18720_544052
  · exact context_11_18721_544136
  · exact context_11_18722_544244
  · exact context_11_18723_544319

theorem selected_cut_21268 : selected 9 ⟨544359, by decide⟩
    (prefixPartial 12 74896) = some ⟨12, 2, 0, 544359, 74896, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_74896_544359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74896 ⟨544359, by decide⟩ :=
  accepted_of_selected 12 74896 ⟨544359, by decide⟩ ⟨12, 2, 0, 544359, 74896, 2937, 65536⟩
    (by decide) selected_cut_21268

theorem selected_cut_21269 : selected 9 ⟨544376, by decide⟩
    (prefixPartial 12 74897) = some ⟨12, 2, 0, 544376, 74897, 1989, 65536⟩ := by
  decide +kernel

theorem context_12_74897_544376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74897 ⟨544376, by decide⟩ :=
  accepted_of_selected 12 74897 ⟨544376, by decide⟩ ⟨12, 2, 0, 544376, 74897, 1989, 65536⟩
    (by decide) selected_cut_21269

theorem selected_cut_21270 : selected 9 ⟨544396, by decide⟩
    (prefixPartial 12 74898) = some ⟨12, 2, 0, 544396, 74898, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_74898_544396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74898 ⟨544396, by decide⟩ :=
  accepted_of_selected 12 74898 ⟨544396, by decide⟩ ⟨12, 2, 0, 544396, 74898, 2089, 65536⟩
    (by decide) selected_cut_21270

theorem selected_cut_21271 : selected 9 ⟨544413, by decide⟩
    (prefixPartial 12 74899) = some ⟨12, 2, 0, 544413, 74899, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_74899_544413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74899 ⟨544413, by decide⟩ :=
  accepted_of_selected 12 74899 ⟨544413, by decide⟩ ⟨12, 2, 0, 544413, 74899, 2105, 65536⟩
    (by decide) selected_cut_21271

theorem unmarked_context_11_18724_544414 : frontier 10 ⟨544414, by decide⟩
    (prefixCache 11 18724) (prefixPartial 11 18724) = false := by
  decide +kernel

theorem node_context_11_18724_544414 : EJMOriginalGlobalDAGData.nodes 10 ⟨544414, by decide⟩ =
    .split (coordinate 11) (![⟨544359, by decide⟩,⟨544376, by decide⟩,⟨544396, by decide⟩,⟨544413, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18724_544414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18724 ⟨544414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18724
    ⟨544414, by decide⟩ (by decide) (![⟨544359, by decide⟩,⟨544376, by decide⟩,⟨544396, by decide⟩,⟨544413, by decide⟩]) unmarked_context_11_18724_544414 node_context_11_18724_544414
  intro a
  fin_cases a
  · exact context_12_74896_544359
  · exact context_12_74897_544376
  · exact context_12_74898_544396
  · exact context_12_74899_544413

theorem selected_cut_21272 : selected 9 ⟨544441, by decide⟩
    (prefixPartial 12 74900) = some ⟨12, 2, 0, 544441, 74900, 2649, 65536⟩ := by
  decide +kernel

theorem context_12_74900_544441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74900 ⟨544441, by decide⟩ :=
  accepted_of_selected 12 74900 ⟨544441, by decide⟩ ⟨12, 2, 0, 544441, 74900, 2649, 65536⟩
    (by decide) selected_cut_21272

theorem selected_cut_21273 : selected 9 ⟨449506, by decide⟩
    (prefixPartial 12 74901) = some ⟨12, 1, 0, 449506, 74901, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74901_449506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74901 ⟨449506, by decide⟩ :=
  accepted_of_selected 12 74901 ⟨449506, by decide⟩ ⟨12, 1, 0, 449506, 74901, 1, 65536⟩
    (by decide) selected_cut_21273

theorem selected_cut_21274 : selected 9 ⟨544504, by decide⟩
    (prefixPartial 12 74902) = some ⟨12, 2, 0, 544504, 74902, 2961, 65536⟩ := by
  decide +kernel

theorem context_12_74902_544504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74902 ⟨544504, by decide⟩ :=
  accepted_of_selected 12 74902 ⟨544504, by decide⟩ ⟨12, 2, 0, 544504, 74902, 2961, 65536⟩
    (by decide) selected_cut_21274

theorem selected_cut_21275 : selected 9 ⟨544565, by decide⟩
    (prefixPartial 12 74903) = some ⟨12, 2, 0, 544565, 74903, 3137, 65536⟩ := by
  decide +kernel

theorem context_12_74903_544565 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74903 ⟨544565, by decide⟩ :=
  accepted_of_selected 12 74903 ⟨544565, by decide⟩ ⟨12, 2, 0, 544565, 74903, 3137, 65536⟩
    (by decide) selected_cut_21275

theorem unmarked_context_11_18725_544566 : frontier 10 ⟨544566, by decide⟩
    (prefixCache 11 18725) (prefixPartial 11 18725) = false := by
  decide +kernel

theorem node_context_11_18725_544566 : EJMOriginalGlobalDAGData.nodes 10 ⟨544566, by decide⟩ =
    .split (coordinate 11) (![⟨544441, by decide⟩,⟨449506, by decide⟩,⟨544504, by decide⟩,⟨544565, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18725_544566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18725 ⟨544566, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18725
    ⟨544566, by decide⟩ (by decide) (![⟨544441, by decide⟩,⟨449506, by decide⟩,⟨544504, by decide⟩,⟨544565, by decide⟩]) unmarked_context_11_18725_544566 node_context_11_18725_544566
  intro a
  fin_cases a
  · exact context_12_74900_544441
  · exact context_12_74901_449506
  · exact context_12_74902_544504
  · exact context_12_74903_544565

theorem selected_cut_21276 : selected 9 ⟨544584, by decide⟩
    (prefixPartial 12 74904) = some ⟨12, 2, 0, 544584, 74904, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_74904_544584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74904 ⟨544584, by decide⟩ :=
  accepted_of_selected 12 74904 ⟨544584, by decide⟩ ⟨12, 2, 0, 544584, 74904, 2237, 65536⟩
    (by decide) selected_cut_21276

theorem selected_cut_21277 : selected 9 ⟨544609, by decide⟩
    (prefixPartial 12 74905) = some ⟨12, 2, 0, 544609, 74905, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_74905_544609 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74905 ⟨544609, by decide⟩ :=
  accepted_of_selected 12 74905 ⟨544609, by decide⟩ ⟨12, 2, 0, 544609, 74905, 2289, 65536⟩
    (by decide) selected_cut_21277

theorem selected_cut_21278 : selected 9 ⟨544634, by decide⟩
    (prefixPartial 12 74906) = some ⟨12, 2, 0, 544634, 74906, 2217, 65536⟩ := by
  decide +kernel

theorem context_12_74906_544634 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74906 ⟨544634, by decide⟩ :=
  accepted_of_selected 12 74906 ⟨544634, by decide⟩ ⟨12, 2, 0, 544634, 74906, 2217, 65536⟩
    (by decide) selected_cut_21278

theorem selected_cut_21279 : selected 9 ⟨544660, by decide⟩
    (prefixPartial 12 74907) = some ⟨12, 2, 0, 544660, 74907, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_74907_544660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74907 ⟨544660, by decide⟩ :=
  accepted_of_selected 12 74907 ⟨544660, by decide⟩ ⟨12, 2, 0, 544660, 74907, 2389, 65536⟩
    (by decide) selected_cut_21279

theorem unmarked_context_11_18726_544661 : frontier 10 ⟨544661, by decide⟩
    (prefixCache 11 18726) (prefixPartial 11 18726) = false := by
  decide +kernel

theorem node_context_11_18726_544661 : EJMOriginalGlobalDAGData.nodes 10 ⟨544661, by decide⟩ =
    .split (coordinate 11) (![⟨544584, by decide⟩,⟨544609, by decide⟩,⟨544634, by decide⟩,⟨544660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18726_544661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18726 ⟨544661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18726
    ⟨544661, by decide⟩ (by decide) (![⟨544584, by decide⟩,⟨544609, by decide⟩,⟨544634, by decide⟩,⟨544660, by decide⟩]) unmarked_context_11_18726_544661 node_context_11_18726_544661
  intro a
  fin_cases a
  · exact context_12_74904_544584
  · exact context_12_74905_544609
  · exact context_12_74906_544634
  · exact context_12_74907_544660

theorem selected_cut_21280 : selected 9 ⟨544680, by decide⟩
    (prefixPartial 12 74908) = some ⟨12, 2, 0, 544680, 74908, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_74908_544680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74908 ⟨544680, by decide⟩ :=
  accepted_of_selected 12 74908 ⟨544680, by decide⟩ ⟨12, 2, 0, 544680, 74908, 1797, 65536⟩
    (by decide) selected_cut_21280

theorem selected_cut_21281 : selected 9 ⟨544701, by decide⟩
    (prefixPartial 12 74909) = some ⟨12, 2, 0, 544701, 74909, 1833, 65536⟩ := by
  decide +kernel

theorem context_12_74909_544701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74909 ⟨544701, by decide⟩ :=
  accepted_of_selected 12 74909 ⟨544701, by decide⟩ ⟨12, 2, 0, 544701, 74909, 1833, 65536⟩
    (by decide) selected_cut_21281

theorem selected_cut_21282 : selected 9 ⟨544722, by decide⟩
    (prefixPartial 12 74910) = some ⟨12, 2, 0, 544722, 74910, 2089, 65536⟩ := by
  decide +kernel

theorem context_12_74910_544722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74910 ⟨544722, by decide⟩ :=
  accepted_of_selected 12 74910 ⟨544722, by decide⟩ ⟨12, 2, 0, 544722, 74910, 2089, 65536⟩
    (by decide) selected_cut_21282

theorem selected_cut_21283 : selected 9 ⟨544739, by decide⟩
    (prefixPartial 12 74911) = some ⟨12, 2, 0, 544739, 74911, 1973, 65536⟩ := by
  decide +kernel

theorem context_12_74911_544739 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74911 ⟨544739, by decide⟩ :=
  accepted_of_selected 12 74911 ⟨544739, by decide⟩ ⟨12, 2, 0, 544739, 74911, 1973, 65536⟩
    (by decide) selected_cut_21283

theorem unmarked_context_11_18727_544740 : frontier 10 ⟨544740, by decide⟩
    (prefixCache 11 18727) (prefixPartial 11 18727) = false := by
  decide +kernel

theorem node_context_11_18727_544740 : EJMOriginalGlobalDAGData.nodes 10 ⟨544740, by decide⟩ =
    .split (coordinate 11) (![⟨544680, by decide⟩,⟨544701, by decide⟩,⟨544722, by decide⟩,⟨544739, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18727_544740 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18727 ⟨544740, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18727
    ⟨544740, by decide⟩ (by decide) (![⟨544680, by decide⟩,⟨544701, by decide⟩,⟨544722, by decide⟩,⟨544739, by decide⟩]) unmarked_context_11_18727_544740 node_context_11_18727_544740
  intro a
  fin_cases a
  · exact context_12_74908_544680
  · exact context_12_74909_544701
  · exact context_12_74910_544722
  · exact context_12_74911_544739

theorem unmarked_context_10_4681_544741 : frontier 11 ⟨544741, by decide⟩
    (prefixCache 10 4681) (prefixPartial 10 4681) = false := by
  decide +kernel

theorem node_context_10_4681_544741 : EJMOriginalGlobalDAGData.nodes 11 ⟨544741, by decide⟩ =
    .split (coordinate 10) (![⟨544414, by decide⟩,⟨544566, by decide⟩,⟨544661, by decide⟩,⟨544740, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4681_544741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4681 ⟨544741, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4681
    ⟨544741, by decide⟩ (by decide) (![⟨544414, by decide⟩,⟨544566, by decide⟩,⟨544661, by decide⟩,⟨544740, by decide⟩]) unmarked_context_10_4681_544741 node_context_10_4681_544741
  intro a
  fin_cases a
  · exact context_11_18724_544414
  · exact context_11_18725_544566
  · exact context_11_18726_544661
  · exact context_11_18727_544740

theorem selected_cut_21284 : selected 9 ⟨544742, by decide⟩
    (prefixPartial 12 74912) = some ⟨12, 1, 0, 544742, 74912, 1, 65536⟩ := by
  decide +kernel

theorem context_12_74912_544742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74912 ⟨544742, by decide⟩ :=
  accepted_of_selected 12 74912 ⟨544742, by decide⟩ ⟨12, 1, 0, 544742, 74912, 1, 65536⟩
    (by decide) selected_cut_21284

theorem selected_cut_21285 : selected 9 ⟨544753, by decide⟩
    (prefixPartial 12 74913) = some ⟨12, 2, 0, 544753, 74913, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_74913_544753 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74913 ⟨544753, by decide⟩ :=
  accepted_of_selected 12 74913 ⟨544753, by decide⟩ ⟨12, 2, 0, 544753, 74913, 1377, 65536⟩
    (by decide) selected_cut_21285

theorem selected_cut_21286 : selected 9 ⟨544765, by decide⟩
    (prefixPartial 12 74914) = some ⟨12, 2, 0, 544765, 74914, 1429, 65536⟩ := by
  decide +kernel

theorem context_12_74914_544765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74914 ⟨544765, by decide⟩ :=
  accepted_of_selected 12 74914 ⟨544765, by decide⟩ ⟨12, 2, 0, 544765, 74914, 1429, 65536⟩
    (by decide) selected_cut_21286

theorem selected_cut_21287 : selected 9 ⟨544777, by decide⟩
    (prefixPartial 12 74915) = some ⟨12, 2, 0, 544777, 74915, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_74915_544777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74915 ⟨544777, by decide⟩ :=
  accepted_of_selected 12 74915 ⟨544777, by decide⟩ ⟨12, 2, 0, 544777, 74915, 1405, 65536⟩
    (by decide) selected_cut_21287

theorem unmarked_context_11_18728_544778 : frontier 10 ⟨544778, by decide⟩
    (prefixCache 11 18728) (prefixPartial 11 18728) = false := by
  decide +kernel

theorem node_context_11_18728_544778 : EJMOriginalGlobalDAGData.nodes 10 ⟨544778, by decide⟩ =
    .split (coordinate 11) (![⟨544742, by decide⟩,⟨544753, by decide⟩,⟨544765, by decide⟩,⟨544777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18728_544778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18728 ⟨544778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18728
    ⟨544778, by decide⟩ (by decide) (![⟨544742, by decide⟩,⟨544753, by decide⟩,⟨544765, by decide⟩,⟨544777, by decide⟩]) unmarked_context_11_18728_544778 node_context_11_18728_544778
  intro a
  fin_cases a
  · exact context_12_74912_544742
  · exact context_12_74913_544753
  · exact context_12_74914_544765
  · exact context_12_74915_544777

theorem selected_cut_21288 : selected 9 ⟨544797, by decide⟩
    (prefixPartial 12 74916) = some ⟨12, 2, 0, 544797, 74916, 1701, 65536⟩ := by
  decide +kernel

theorem context_12_74916_544797 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74916 ⟨544797, by decide⟩ :=
  accepted_of_selected 12 74916 ⟨544797, by decide⟩ ⟨12, 2, 0, 544797, 74916, 1701, 65536⟩
    (by decide) selected_cut_21288

theorem selected_cut_21289 : selected 9 ⟨544813, by decide⟩
    (prefixPartial 12 74917) = some ⟨12, 2, 0, 544813, 74917, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_74917_544813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74917 ⟨544813, by decide⟩ :=
  accepted_of_selected 12 74917 ⟨544813, by decide⟩ ⟨12, 2, 0, 544813, 74917, 1513, 65536⟩
    (by decide) selected_cut_21289

theorem selected_cut_21290 : selected 9 ⟨544835, by decide⟩
    (prefixPartial 12 74918) = some ⟨12, 2, 0, 544835, 74918, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_74918_544835 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74918 ⟨544835, by decide⟩ :=
  accepted_of_selected 12 74918 ⟨544835, by decide⟩ ⟨12, 2, 0, 544835, 74918, 1737, 65536⟩
    (by decide) selected_cut_21290

theorem selected_cut_21291 : selected 9 ⟨544853, by decide⟩
    (prefixPartial 12 74919) = some ⟨12, 2, 0, 544853, 74919, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_74919_544853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74919 ⟨544853, by decide⟩ :=
  accepted_of_selected 12 74919 ⟨544853, by decide⟩ ⟨12, 2, 0, 544853, 74919, 1741, 65536⟩
    (by decide) selected_cut_21291

theorem unmarked_context_11_18729_544854 : frontier 10 ⟨544854, by decide⟩
    (prefixCache 11 18729) (prefixPartial 11 18729) = false := by
  decide +kernel

theorem node_context_11_18729_544854 : EJMOriginalGlobalDAGData.nodes 10 ⟨544854, by decide⟩ =
    .split (coordinate 11) (![⟨544797, by decide⟩,⟨544813, by decide⟩,⟨544835, by decide⟩,⟨544853, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18729_544854 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18729 ⟨544854, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18729
    ⟨544854, by decide⟩ (by decide) (![⟨544797, by decide⟩,⟨544813, by decide⟩,⟨544835, by decide⟩,⟨544853, by decide⟩]) unmarked_context_11_18729_544854 node_context_11_18729_544854
  intro a
  fin_cases a
  · exact context_12_74916_544797
  · exact context_12_74917_544813
  · exact context_12_74918_544835
  · exact context_12_74919_544853

theorem selected_cut_21292 : selected 9 ⟨544869, by decide⟩
    (prefixPartial 12 74920) = some ⟨12, 2, 0, 544869, 74920, 1573, 65536⟩ := by
  decide +kernel

theorem context_12_74920_544869 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74920 ⟨544869, by decide⟩ :=
  accepted_of_selected 12 74920 ⟨544869, by decide⟩ ⟨12, 2, 0, 544869, 74920, 1573, 65536⟩
    (by decide) selected_cut_21292

theorem selected_cut_21293 : selected 9 ⟨544886, by decide⟩
    (prefixPartial 12 74921) = some ⟨12, 2, 0, 544886, 74921, 1557, 65536⟩ := by
  decide +kernel

theorem context_12_74921_544886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74921 ⟨544886, by decide⟩ :=
  accepted_of_selected 12 74921 ⟨544886, by decide⟩ ⟨12, 2, 0, 544886, 74921, 1557, 65536⟩
    (by decide) selected_cut_21293

theorem selected_cut_21294 : selected 9 ⟨544907, by decide⟩
    (prefixPartial 12 74922) = some ⟨12, 2, 0, 544907, 74922, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_74922_544907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74922 ⟨544907, by decide⟩ :=
  accepted_of_selected 12 74922 ⟨544907, by decide⟩ ⟨12, 2, 0, 544907, 74922, 1601, 65536⟩
    (by decide) selected_cut_21294

theorem selected_cut_21295 : selected 9 ⟨544930, by decide⟩
    (prefixPartial 12 74923) = some ⟨12, 2, 0, 544930, 74923, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_74923_544930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74923 ⟨544930, by decide⟩ :=
  accepted_of_selected 12 74923 ⟨544930, by decide⟩ ⟨12, 2, 0, 544930, 74923, 1585, 65536⟩
    (by decide) selected_cut_21295

theorem unmarked_context_11_18730_544931 : frontier 10 ⟨544931, by decide⟩
    (prefixCache 11 18730) (prefixPartial 11 18730) = false := by
  decide +kernel

theorem node_context_11_18730_544931 : EJMOriginalGlobalDAGData.nodes 10 ⟨544931, by decide⟩ =
    .split (coordinate 11) (![⟨544869, by decide⟩,⟨544886, by decide⟩,⟨544907, by decide⟩,⟨544930, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18730_544931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18730 ⟨544931, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18730
    ⟨544931, by decide⟩ (by decide) (![⟨544869, by decide⟩,⟨544886, by decide⟩,⟨544907, by decide⟩,⟨544930, by decide⟩]) unmarked_context_11_18730_544931 node_context_11_18730_544931
  intro a
  fin_cases a
  · exact context_12_74920_544869
  · exact context_12_74921_544886
  · exact context_12_74922_544907
  · exact context_12_74923_544930

theorem selected_cut_21296 : selected 9 ⟨544945, by decide⟩
    (prefixPartial 12 74924) = some ⟨12, 2, 0, 544945, 74924, 1337, 65536⟩ := by
  decide +kernel

theorem context_12_74924_544945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74924 ⟨544945, by decide⟩ :=
  accepted_of_selected 12 74924 ⟨544945, by decide⟩ ⟨12, 2, 0, 544945, 74924, 1337, 65536⟩
    (by decide) selected_cut_21296

theorem selected_cut_21297 : selected 9 ⟨544958, by decide⟩
    (prefixPartial 12 74925) = some ⟨12, 2, 0, 544958, 74925, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_74925_544958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74925 ⟨544958, by decide⟩ :=
  accepted_of_selected 12 74925 ⟨544958, by decide⟩ ⟨12, 2, 0, 544958, 74925, 1301, 65536⟩
    (by decide) selected_cut_21297

theorem selected_cut_21298 : selected 9 ⟨544974, by decide⟩
    (prefixPartial 12 74926) = some ⟨12, 2, 0, 544974, 74926, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_74926_544974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74926 ⟨544974, by decide⟩ :=
  accepted_of_selected 12 74926 ⟨544974, by decide⟩ ⟨12, 2, 0, 544974, 74926, 1461, 65536⟩
    (by decide) selected_cut_21298

theorem selected_cut_21299 : selected 9 ⟨544987, by decide⟩
    (prefixPartial 12 74927) = some ⟨12, 2, 0, 544987, 74927, 1365, 65536⟩ := by
  decide +kernel

theorem context_12_74927_544987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74927 ⟨544987, by decide⟩ :=
  accepted_of_selected 12 74927 ⟨544987, by decide⟩ ⟨12, 2, 0, 544987, 74927, 1365, 65536⟩
    (by decide) selected_cut_21299

theorem unmarked_context_11_18731_544988 : frontier 10 ⟨544988, by decide⟩
    (prefixCache 11 18731) (prefixPartial 11 18731) = false := by
  decide +kernel

theorem node_context_11_18731_544988 : EJMOriginalGlobalDAGData.nodes 10 ⟨544988, by decide⟩ =
    .split (coordinate 11) (![⟨544945, by decide⟩,⟨544958, by decide⟩,⟨544974, by decide⟩,⟨544987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18731_544988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18731 ⟨544988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18731
    ⟨544988, by decide⟩ (by decide) (![⟨544945, by decide⟩,⟨544958, by decide⟩,⟨544974, by decide⟩,⟨544987, by decide⟩]) unmarked_context_11_18731_544988 node_context_11_18731_544988
  intro a
  fin_cases a
  · exact context_12_74924_544945
  · exact context_12_74925_544958
  · exact context_12_74926_544974
  · exact context_12_74927_544987

theorem unmarked_context_10_4682_544989 : frontier 11 ⟨544989, by decide⟩
    (prefixCache 10 4682) (prefixPartial 10 4682) = false := by
  decide +kernel

theorem node_context_10_4682_544989 : EJMOriginalGlobalDAGData.nodes 11 ⟨544989, by decide⟩ =
    .split (coordinate 10) (![⟨544778, by decide⟩,⟨544854, by decide⟩,⟨544931, by decide⟩,⟨544988, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4682_544989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4682 ⟨544989, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4682
    ⟨544989, by decide⟩ (by decide) (![⟨544778, by decide⟩,⟨544854, by decide⟩,⟨544931, by decide⟩,⟨544988, by decide⟩]) unmarked_context_10_4682_544989 node_context_10_4682_544989
  intro a
  fin_cases a
  · exact context_11_18728_544778
  · exact context_11_18729_544854
  · exact context_11_18730_544931
  · exact context_11_18731_544988

theorem selected_cut_21300 : selected 9 ⟨545021, by decide⟩
    (prefixPartial 12 74928) = some ⟨12, 2, 0, 545021, 74928, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_74928_545021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74928 ⟨545021, by decide⟩ :=
  accepted_of_selected 12 74928 ⟨545021, by decide⟩ ⟨12, 2, 0, 545021, 74928, 1917, 65536⟩
    (by decide) selected_cut_21300

theorem selected_cut_21301 : selected 9 ⟨545034, by decide⟩
    (prefixPartial 12 74929) = some ⟨12, 2, 0, 545034, 74929, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_74929_545034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74929 ⟨545034, by decide⟩ :=
  accepted_of_selected 12 74929 ⟨545034, by decide⟩ ⟨12, 2, 0, 545034, 74929, 1181, 65536⟩
    (by decide) selected_cut_21301

theorem selected_cut_21302 : selected 9 ⟨545051, by decide⟩
    (prefixPartial 12 74930) = some ⟨12, 2, 0, 545051, 74930, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_74930_545051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74930 ⟨545051, by decide⟩ :=
  accepted_of_selected 12 74930 ⟨545051, by decide⟩ ⟨12, 2, 0, 545051, 74930, 1325, 65536⟩
    (by decide) selected_cut_21302

theorem selected_cut_21303 : selected 9 ⟨545064, by decide⟩
    (prefixPartial 12 74931) = some ⟨12, 2, 0, 545064, 74931, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_74931_545064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74931 ⟨545064, by decide⟩ :=
  accepted_of_selected 12 74931 ⟨545064, by decide⟩ ⟨12, 2, 0, 545064, 74931, 1197, 65536⟩
    (by decide) selected_cut_21303

theorem unmarked_context_11_18732_545065 : frontier 10 ⟨545065, by decide⟩
    (prefixCache 11 18732) (prefixPartial 11 18732) = false := by
  decide +kernel

theorem node_context_11_18732_545065 : EJMOriginalGlobalDAGData.nodes 10 ⟨545065, by decide⟩ =
    .split (coordinate 11) (![⟨545021, by decide⟩,⟨545034, by decide⟩,⟨545051, by decide⟩,⟨545064, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18732_545065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18732 ⟨545065, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18732
    ⟨545065, by decide⟩ (by decide) (![⟨545021, by decide⟩,⟨545034, by decide⟩,⟨545051, by decide⟩,⟨545064, by decide⟩]) unmarked_context_11_18732_545065 node_context_11_18732_545065
  intro a
  fin_cases a
  · exact context_12_74928_545021
  · exact context_12_74929_545034
  · exact context_12_74930_545051
  · exact context_12_74931_545064

theorem selected_cut_21304 : selected 9 ⟨545081, by decide⟩
    (prefixPartial 12 74932) = some ⟨12, 2, 0, 545081, 74932, 1317, 65536⟩ := by
  decide +kernel

theorem context_12_74932_545081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74932 ⟨545081, by decide⟩ :=
  accepted_of_selected 12 74932 ⟨545081, by decide⟩ ⟨12, 2, 0, 545081, 74932, 1317, 65536⟩
    (by decide) selected_cut_21304

theorem selected_cut_21305 : selected 9 ⟨545093, by decide⟩
    (prefixPartial 12 74933) = some ⟨12, 2, 0, 545093, 74933, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_74933_545093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74933 ⟨545093, by decide⟩ :=
  accepted_of_selected 12 74933 ⟨545093, by decide⟩ ⟨12, 2, 0, 545093, 74933, 1189, 65536⟩
    (by decide) selected_cut_21305

theorem selected_cut_21306 : selected 9 ⟨545117, by decide⟩
    (prefixPartial 12 74934) = some ⟨12, 2, 0, 545117, 74934, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_74934_545117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74934 ⟨545117, by decide⟩ :=
  accepted_of_selected 12 74934 ⟨545117, by decide⟩ ⟨12, 2, 0, 545117, 74934, 1477, 65536⟩
    (by decide) selected_cut_21306

theorem selected_cut_21307 : selected 9 ⟨545136, by decide⟩
    (prefixPartial 12 74935) = some ⟨12, 2, 0, 545136, 74935, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_74935_545136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74935 ⟨545136, by decide⟩ :=
  accepted_of_selected 12 74935 ⟨545136, by decide⟩ ⟨12, 2, 0, 545136, 74935, 1437, 65536⟩
    (by decide) selected_cut_21307

theorem unmarked_context_11_18733_545137 : frontier 10 ⟨545137, by decide⟩
    (prefixCache 11 18733) (prefixPartial 11 18733) = false := by
  decide +kernel

theorem node_context_11_18733_545137 : EJMOriginalGlobalDAGData.nodes 10 ⟨545137, by decide⟩ =
    .split (coordinate 11) (![⟨545081, by decide⟩,⟨545093, by decide⟩,⟨545117, by decide⟩,⟨545136, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18733_545137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18733 ⟨545137, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18733
    ⟨545137, by decide⟩ (by decide) (![⟨545081, by decide⟩,⟨545093, by decide⟩,⟨545117, by decide⟩,⟨545136, by decide⟩]) unmarked_context_11_18733_545137 node_context_11_18733_545137
  intro a
  fin_cases a
  · exact context_12_74932_545081
  · exact context_12_74933_545093
  · exact context_12_74934_545117
  · exact context_12_74935_545136

theorem selected_cut_21308 : selected 9 ⟨545152, by decide⟩
    (prefixPartial 12 74936) = some ⟨12, 2, 0, 545152, 74936, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_74936_545152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74936 ⟨545152, by decide⟩ :=
  accepted_of_selected 12 74936 ⟨545152, by decide⟩ ⟨12, 2, 0, 545152, 74936, 1293, 65536⟩
    (by decide) selected_cut_21308

theorem selected_cut_21309 : selected 9 ⟨545170, by decide⟩
    (prefixPartial 12 74937) = some ⟨12, 2, 0, 545170, 74937, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_74937_545170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74937 ⟨545170, by decide⟩ :=
  accepted_of_selected 12 74937 ⟨545170, by decide⟩ ⟨12, 2, 0, 545170, 74937, 1265, 65536⟩
    (by decide) selected_cut_21309

theorem selected_cut_21310 : selected 9 ⟨545189, by decide⟩
    (prefixPartial 12 74938) = some ⟨12, 2, 0, 545189, 74938, 1361, 65536⟩ := by
  decide +kernel

theorem context_12_74938_545189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74938 ⟨545189, by decide⟩ :=
  accepted_of_selected 12 74938 ⟨545189, by decide⟩ ⟨12, 2, 0, 545189, 74938, 1361, 65536⟩
    (by decide) selected_cut_21310

theorem selected_cut_21311 : selected 9 ⟨545202, by decide⟩
    (prefixPartial 12 74939) = some ⟨12, 2, 0, 545202, 74939, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_74939_545202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 74939 ⟨545202, by decide⟩ :=
  accepted_of_selected 12 74939 ⟨545202, by decide⟩ ⟨12, 2, 0, 545202, 74939, 1293, 65536⟩
    (by decide) selected_cut_21311

theorem unmarked_context_11_18734_545203 : frontier 10 ⟨545203, by decide⟩
    (prefixCache 11 18734) (prefixPartial 11 18734) = false := by
  decide +kernel

theorem node_context_11_18734_545203 : EJMOriginalGlobalDAGData.nodes 10 ⟨545203, by decide⟩ =
    .split (coordinate 11) (![⟨545152, by decide⟩,⟨545170, by decide⟩,⟨545189, by decide⟩,⟨545202, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18734_545203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18734 ⟨545203, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18734
    ⟨545203, by decide⟩ (by decide) (![⟨545152, by decide⟩,⟨545170, by decide⟩,⟨545189, by decide⟩,⟨545202, by decide⟩]) unmarked_context_11_18734_545203 node_context_11_18734_545203
  intro a
  fin_cases a
  · exact context_12_74936_545152
  · exact context_12_74937_545170
  · exact context_12_74938_545189
  · exact context_12_74939_545202

theorem selected_cut_21312 : selected 10 ⟨545249, by decide⟩
    (prefixPartial 11 18735) = some ⟨11, 2, 0, 545249, 18735, 4085, 262144⟩ := by
  decide +kernel

theorem context_11_18735_545249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18735 ⟨545249, by decide⟩ :=
  accepted_of_selected 11 18735 ⟨545249, by decide⟩ ⟨11, 2, 0, 545249, 18735, 4085, 262144⟩
    (by decide) selected_cut_21312

theorem unmarked_context_10_4683_545250 : frontier 11 ⟨545250, by decide⟩
    (prefixCache 10 4683) (prefixPartial 10 4683) = false := by
  decide +kernel

theorem node_context_10_4683_545250 : EJMOriginalGlobalDAGData.nodes 11 ⟨545250, by decide⟩ =
    .split (coordinate 10) (![⟨545065, by decide⟩,⟨545137, by decide⟩,⟨545203, by decide⟩,⟨545249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4683_545250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4683 ⟨545250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4683
    ⟨545250, by decide⟩ (by decide) (![⟨545065, by decide⟩,⟨545137, by decide⟩,⟨545203, by decide⟩,⟨545249, by decide⟩]) unmarked_context_10_4683_545250 node_context_10_4683_545250
  intro a
  fin_cases a
  · exact context_11_18732_545065
  · exact context_11_18733_545137
  · exact context_11_18734_545203
  · exact context_11_18735_545249

theorem unmarked_context_9_1170_545251 : frontier 12 ⟨545251, by decide⟩
    (prefixCache 9 1170) (prefixPartial 9 1170) = false := by
  decide +kernel

theorem node_context_9_1170_545251 : EJMOriginalGlobalDAGData.nodes 12 ⟨545251, by decide⟩ =
    .split (coordinate 9) (![⟨544320, by decide⟩,⟨544741, by decide⟩,⟨544989, by decide⟩,⟨545250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1170_545251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1170 ⟨545251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1170
    ⟨545251, by decide⟩ (by decide) (![⟨544320, by decide⟩,⟨544741, by decide⟩,⟨544989, by decide⟩,⟨545250, by decide⟩]) unmarked_context_9_1170_545251 node_context_9_1170_545251
  intro a
  fin_cases a
  · exact context_10_4680_544320
  · exact context_10_4681_544741
  · exact context_10_4682_544989
  · exact context_10_4683_545250

theorem selected_cut_21313 : selected 10 ⟨545276, by decide⟩
    (prefixPartial 11 18736) = some ⟨11, 2, 0, 545276, 18736, 2005, 262144⟩ := by
  decide +kernel

theorem context_11_18736_545276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18736 ⟨545276, by decide⟩ :=
  accepted_of_selected 11 18736 ⟨545276, by decide⟩ ⟨11, 2, 0, 545276, 18736, 2005, 262144⟩
    (by decide) selected_cut_21313

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
