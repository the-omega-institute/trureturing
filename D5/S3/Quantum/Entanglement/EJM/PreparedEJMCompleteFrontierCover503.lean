/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover502
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_48292 : selected 9 ⟨1354440, by decide⟩
    (prefixPartial 12 375835) = some ⟨12, 2, 0, 1354440, 375835, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_375835_1354440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375835 ⟨1354440, by decide⟩ :=
  accepted_of_selected 12 375835 ⟨1354440, by decide⟩ ⟨12, 2, 0, 1354440, 375835, 2809, 65536⟩
    (by decide) selected_cut_48292

theorem unmarked_context_11_93958_1354441 : frontier 10 ⟨1354441, by decide⟩
    (prefixCache 11 93958) (prefixPartial 11 93958) = false := by
  decide +kernel

theorem node_context_11_93958_1354441 : EJMOriginalGlobalDAGData.nodes 10 ⟨1354441, by decide⟩ =
    .split (coordinate 11) (![⟨994572, by decide⟩,⟨1354384, by decide⟩,⟨806997, by decide⟩,⟨1354440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93958_1354441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93958 ⟨1354441, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93958
    ⟨1354441, by decide⟩ (by decide) (![⟨994572, by decide⟩,⟨1354384, by decide⟩,⟨806997, by decide⟩,⟨1354440, by decide⟩]) unmarked_context_11_93958_1354441 node_context_11_93958_1354441
  intro a
  fin_cases a
  · exact context_12_375832_994572
  · exact context_12_375833_1354384
  · exact context_12_375834_806997
  · exact context_12_375835_1354440

theorem selected_cut_48293 : selected 9 ⟨1354487, by decide⟩
    (prefixPartial 12 375836) = some ⟨12, 2, 0, 1354487, 375836, 2269, 65536⟩ := by
  decide +kernel

theorem context_12_375836_1354487 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375836 ⟨1354487, by decide⟩ :=
  accepted_of_selected 12 375836 ⟨1354487, by decide⟩ ⟨12, 2, 0, 1354487, 375836, 2269, 65536⟩
    (by decide) selected_cut_48293

theorem selected_cut_48294 : selected 9 ⟨1354529, by decide⟩
    (prefixPartial 12 375837) = some ⟨12, 2, 0, 1354529, 375837, 2497, 65536⟩ := by
  decide +kernel

theorem context_12_375837_1354529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375837 ⟨1354529, by decide⟩ :=
  accepted_of_selected 12 375837 ⟨1354529, by decide⟩ ⟨12, 2, 0, 1354529, 375837, 2497, 65536⟩
    (by decide) selected_cut_48294

theorem selected_cut_48295 : selected 9 ⟨1354574, by decide⟩
    (prefixPartial 12 375838) = some ⟨12, 2, 0, 1354574, 375838, 2393, 65536⟩ := by
  decide +kernel

theorem context_12_375838_1354574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375838 ⟨1354574, by decide⟩ :=
  accepted_of_selected 12 375838 ⟨1354574, by decide⟩ ⟨12, 2, 0, 1354574, 375838, 2393, 65536⟩
    (by decide) selected_cut_48295

theorem selected_cut_48296 : selected 9 ⟨1053916, by decide⟩
    (prefixPartial 12 375839) = some ⟨12, 1, 0, 1053916, 375839, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375839_1053916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375839 ⟨1053916, by decide⟩ :=
  accepted_of_selected 12 375839 ⟨1053916, by decide⟩ ⟨12, 1, 0, 1053916, 375839, 1, 65536⟩
    (by decide) selected_cut_48296

theorem unmarked_context_11_93959_1354575 : frontier 10 ⟨1354575, by decide⟩
    (prefixCache 11 93959) (prefixPartial 11 93959) = false := by
  decide +kernel

theorem node_context_11_93959_1354575 : EJMOriginalGlobalDAGData.nodes 10 ⟨1354575, by decide⟩ =
    .split (coordinate 11) (![⟨1354487, by decide⟩,⟨1354529, by decide⟩,⟨1354574, by decide⟩,⟨1053916, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93959_1354575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93959 ⟨1354575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93959
    ⟨1354575, by decide⟩ (by decide) (![⟨1354487, by decide⟩,⟨1354529, by decide⟩,⟨1354574, by decide⟩,⟨1053916, by decide⟩]) unmarked_context_11_93959_1354575 node_context_11_93959_1354575
  intro a
  fin_cases a
  · exact context_12_375836_1354487
  · exact context_12_375837_1354529
  · exact context_12_375838_1354574
  · exact context_12_375839_1053916

theorem unmarked_context_10_23489_1354576 : frontier 11 ⟨1354576, by decide⟩
    (prefixCache 10 23489) (prefixPartial 10 23489) = false := by
  decide +kernel

theorem node_context_10_23489_1354576 : EJMOriginalGlobalDAGData.nodes 11 ⟨1354576, by decide⟩ =
    .split (coordinate 10) (![⟨1354215, by decide⟩,⟨1354336, by decide⟩,⟨1354441, by decide⟩,⟨1354575, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23489_1354576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23489 ⟨1354576, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23489
    ⟨1354576, by decide⟩ (by decide) (![⟨1354215, by decide⟩,⟨1354336, by decide⟩,⟨1354441, by decide⟩,⟨1354575, by decide⟩]) unmarked_context_10_23489_1354576 node_context_10_23489_1354576
  intro a
  fin_cases a
  · exact context_11_93956_1354215
  · exact context_11_93957_1354336
  · exact context_11_93958_1354441
  · exact context_11_93959_1354575

theorem selected_cut_48297 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 375840) = some ⟨12, 1, 0, 435790, 375840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375840_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375840 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 375840 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 375840, 1, 65536⟩
    (by decide) selected_cut_48297

theorem selected_cut_48298 : selected 9 ⟨1354620, by decide⟩
    (prefixPartial 12 375841) = some ⟨12, 2, 0, 1354620, 375841, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_375841_1354620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375841 ⟨1354620, by decide⟩ :=
  accepted_of_selected 12 375841 ⟨1354620, by decide⟩ ⟨12, 2, 0, 1354620, 375841, 2425, 65536⟩
    (by decide) selected_cut_48298

theorem selected_cut_48299 : selected 9 ⟨1354667, by decide⟩
    (prefixPartial 12 375842) = some ⟨12, 2, 0, 1354667, 375842, 2529, 65536⟩ := by
  decide +kernel

theorem context_12_375842_1354667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375842 ⟨1354667, by decide⟩ :=
  accepted_of_selected 12 375842 ⟨1354667, by decide⟩ ⟨12, 2, 0, 1354667, 375842, 2529, 65536⟩
    (by decide) selected_cut_48299

theorem selected_cut_48300 : selected 9 ⟨1354707, by decide⟩
    (prefixPartial 12 375843) = some ⟨12, 2, 0, 1354707, 375843, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_375843_1354707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375843 ⟨1354707, by decide⟩ :=
  accepted_of_selected 12 375843 ⟨1354707, by decide⟩ ⟨12, 2, 0, 1354707, 375843, 2397, 65536⟩
    (by decide) selected_cut_48300

theorem unmarked_context_11_93960_1354708 : frontier 10 ⟨1354708, by decide⟩
    (prefixCache 11 93960) (prefixPartial 11 93960) = false := by
  decide +kernel

theorem node_context_11_93960_1354708 : EJMOriginalGlobalDAGData.nodes 10 ⟨1354708, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1354620, by decide⟩,⟨1354667, by decide⟩,⟨1354707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93960_1354708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93960 ⟨1354708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93960
    ⟨1354708, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1354620, by decide⟩,⟨1354667, by decide⟩,⟨1354707, by decide⟩]) unmarked_context_11_93960_1354708 node_context_11_93960_1354708
  intro a
  fin_cases a
  · exact context_12_375840_435790
  · exact context_12_375841_1354620
  · exact context_12_375842_1354667
  · exact context_12_375843_1354707

theorem selected_cut_48301 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 375844) = some ⟨12, 1, 0, 435790, 375844, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375844_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375844 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 375844 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 375844, 1, 65536⟩
    (by decide) selected_cut_48301

theorem selected_cut_48302 : selected 9 ⟨1321747, by decide⟩
    (prefixPartial 12 375845) = some ⟨12, 1, 0, 1321747, 375845, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375845_1321747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375845 ⟨1321747, by decide⟩ :=
  accepted_of_selected 12 375845 ⟨1321747, by decide⟩ ⟨12, 1, 0, 1321747, 375845, 1, 65536⟩
    (by decide) selected_cut_48302

theorem selected_cut_48303 : selected 9 ⟨1354762, by decide⟩
    (prefixPartial 12 375846) = some ⟨12, 2, 0, 1354762, 375846, 3013, 65536⟩ := by
  decide +kernel

theorem context_12_375846_1354762 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375846 ⟨1354762, by decide⟩ :=
  accepted_of_selected 12 375846 ⟨1354762, by decide⟩ ⟨12, 2, 0, 1354762, 375846, 3013, 65536⟩
    (by decide) selected_cut_48303

theorem selected_cut_48304 : selected 9 ⟨1354814, by decide⟩
    (prefixPartial 12 375847) = some ⟨12, 2, 0, 1354814, 375847, 2773, 65536⟩ := by
  decide +kernel

theorem context_12_375847_1354814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375847 ⟨1354814, by decide⟩ :=
  accepted_of_selected 12 375847 ⟨1354814, by decide⟩ ⟨12, 2, 0, 1354814, 375847, 2773, 65536⟩
    (by decide) selected_cut_48304

theorem unmarked_context_11_93961_1354815 : frontier 10 ⟨1354815, by decide⟩
    (prefixCache 11 93961) (prefixPartial 11 93961) = false := by
  decide +kernel

theorem node_context_11_93961_1354815 : EJMOriginalGlobalDAGData.nodes 10 ⟨1354815, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1321747, by decide⟩,⟨1354762, by decide⟩,⟨1354814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93961_1354815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93961 ⟨1354815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93961
    ⟨1354815, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1321747, by decide⟩,⟨1354762, by decide⟩,⟨1354814, by decide⟩]) unmarked_context_11_93961_1354815 node_context_11_93961_1354815
  intro a
  fin_cases a
  · exact context_12_375844_435790
  · exact context_12_375845_1321747
  · exact context_12_375846_1354762
  · exact context_12_375847_1354814

theorem selected_cut_48305 : selected 10 ⟨1354860, by decide⟩
    (prefixPartial 11 93962) = some ⟨11, 2, 0, 1354860, 93962, 2297, 262144⟩ := by
  decide +kernel

theorem context_11_93962_1354860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93962 ⟨1354860, by decide⟩ :=
  accepted_of_selected 11 93962 ⟨1354860, by decide⟩ ⟨11, 2, 0, 1354860, 93962, 2297, 262144⟩
    (by decide) selected_cut_48305

theorem selected_cut_48306 : selected 9 ⟨450498, by decide⟩
    (prefixPartial 12 375852) = some ⟨12, 1, 0, 450498, 375852, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375852_450498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375852 ⟨450498, by decide⟩ :=
  accepted_of_selected 12 375852 ⟨450498, by decide⟩ ⟨12, 1, 0, 450498, 375852, 1, 65536⟩
    (by decide) selected_cut_48306

theorem selected_cut_48307 : selected 9 ⟨1354902, by decide⟩
    (prefixPartial 12 375853) = some ⟨12, 2, 0, 1354902, 375853, 2461, 65536⟩ := by
  decide +kernel

theorem context_12_375853_1354902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375853 ⟨1354902, by decide⟩ :=
  accepted_of_selected 12 375853 ⟨1354902, by decide⟩ ⟨12, 2, 0, 1354902, 375853, 2461, 65536⟩
    (by decide) selected_cut_48307

theorem selected_cut_48308 : selected 9 ⟨1354948, by decide⟩
    (prefixPartial 12 375854) = some ⟨12, 2, 0, 1354948, 375854, 2489, 65536⟩ := by
  decide +kernel

theorem context_12_375854_1354948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375854 ⟨1354948, by decide⟩ :=
  accepted_of_selected 12 375854 ⟨1354948, by decide⟩ ⟨12, 2, 0, 1354948, 375854, 2489, 65536⟩
    (by decide) selected_cut_48308

theorem selected_cut_48309 : selected 9 ⟨1321995, by decide⟩
    (prefixPartial 12 375855) = some ⟨12, 1, 0, 1321995, 375855, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375855_1321995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375855 ⟨1321995, by decide⟩ :=
  accepted_of_selected 12 375855 ⟨1321995, by decide⟩ ⟨12, 1, 0, 1321995, 375855, 1, 65536⟩
    (by decide) selected_cut_48309

theorem unmarked_context_11_93963_1354949 : frontier 10 ⟨1354949, by decide⟩
    (prefixCache 11 93963) (prefixPartial 11 93963) = false := by
  decide +kernel

theorem node_context_11_93963_1354949 : EJMOriginalGlobalDAGData.nodes 10 ⟨1354949, by decide⟩ =
    .split (coordinate 11) (![⟨450498, by decide⟩,⟨1354902, by decide⟩,⟨1354948, by decide⟩,⟨1321995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93963_1354949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93963 ⟨1354949, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93963
    ⟨1354949, by decide⟩ (by decide) (![⟨450498, by decide⟩,⟨1354902, by decide⟩,⟨1354948, by decide⟩,⟨1321995, by decide⟩]) unmarked_context_11_93963_1354949 node_context_11_93963_1354949
  intro a
  fin_cases a
  · exact context_12_375852_450498
  · exact context_12_375853_1354902
  · exact context_12_375854_1354948
  · exact context_12_375855_1321995

theorem unmarked_context_10_23490_1354950 : frontier 11 ⟨1354950, by decide⟩
    (prefixCache 10 23490) (prefixPartial 10 23490) = false := by
  decide +kernel

theorem node_context_10_23490_1354950 : EJMOriginalGlobalDAGData.nodes 11 ⟨1354950, by decide⟩ =
    .split (coordinate 10) (![⟨1354708, by decide⟩,⟨1354815, by decide⟩,⟨1354860, by decide⟩,⟨1354949, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23490_1354950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23490 ⟨1354950, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23490
    ⟨1354950, by decide⟩ (by decide) (![⟨1354708, by decide⟩,⟨1354815, by decide⟩,⟨1354860, by decide⟩,⟨1354949, by decide⟩]) unmarked_context_10_23490_1354950 node_context_10_23490_1354950
  intro a
  fin_cases a
  · exact context_11_93960_1354708
  · exact context_11_93961_1354815
  · exact context_11_93962_1354860
  · exact context_11_93963_1354949

theorem selected_cut_48310 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 375856) = some ⟨12, 1, 0, 985390, 375856, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375856_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375856 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 375856 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 375856, 1, 65536⟩
    (by decide) selected_cut_48310

theorem selected_cut_48311 : selected 9 ⟨1354985, by decide⟩
    (prefixPartial 12 375857) = some ⟨12, 2, 0, 1354985, 375857, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_375857_1354985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375857 ⟨1354985, by decide⟩ :=
  accepted_of_selected 12 375857 ⟨1354985, by decide⟩ ⟨12, 2, 0, 1354985, 375857, 1841, 65536⟩
    (by decide) selected_cut_48311

theorem selected_cut_48312 : selected 9 ⟨1355018, by decide⟩
    (prefixPartial 12 375858) = some ⟨12, 2, 0, 1355018, 375858, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_375858_1355018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375858 ⟨1355018, by decide⟩ :=
  accepted_of_selected 12 375858 ⟨1355018, by decide⟩ ⟨12, 2, 0, 1355018, 375858, 1961, 65536⟩
    (by decide) selected_cut_48312

theorem selected_cut_48313 : selected 9 ⟨1355059, by decide⟩
    (prefixPartial 12 375859) = some ⟨12, 2, 0, 1355059, 375859, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_375859_1355059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375859 ⟨1355059, by decide⟩ :=
  accepted_of_selected 12 375859 ⟨1355059, by decide⟩ ⟨12, 2, 0, 1355059, 375859, 2025, 65536⟩
    (by decide) selected_cut_48313

theorem unmarked_context_11_93964_1355060 : frontier 10 ⟨1355060, by decide⟩
    (prefixCache 11 93964) (prefixPartial 11 93964) = false := by
  decide +kernel

theorem node_context_11_93964_1355060 : EJMOriginalGlobalDAGData.nodes 10 ⟨1355060, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1354985, by decide⟩,⟨1355018, by decide⟩,⟨1355059, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93964_1355060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93964 ⟨1355060, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93964
    ⟨1355060, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1354985, by decide⟩,⟨1355018, by decide⟩,⟨1355059, by decide⟩]) unmarked_context_11_93964_1355060 node_context_11_93964_1355060
  intro a
  fin_cases a
  · exact context_12_375856_985390
  · exact context_12_375857_1354985
  · exact context_12_375858_1355018
  · exact context_12_375859_1355059

theorem selected_cut_48314 : selected 9 ⟨1355109, by decide⟩
    (prefixPartial 12 375860) = some ⟨12, 2, 0, 1355109, 375860, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_375860_1355109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375860 ⟨1355109, by decide⟩ :=
  accepted_of_selected 12 375860 ⟨1355109, by decide⟩ ⟨12, 2, 0, 1355109, 375860, 2473, 65536⟩
    (by decide) selected_cut_48314

theorem selected_cut_48315 : selected 9 ⟨1355146, by decide⟩
    (prefixPartial 12 375861) = some ⟨12, 2, 0, 1355146, 375861, 1157, 65536⟩ := by
  decide +kernel

theorem context_12_375861_1355146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375861 ⟨1355146, by decide⟩ :=
  accepted_of_selected 12 375861 ⟨1355146, by decide⟩ ⟨12, 2, 0, 1355146, 375861, 1157, 65536⟩
    (by decide) selected_cut_48315

theorem selected_cut_48316 : selected 9 ⟨1355197, by decide⟩
    (prefixPartial 12 375862) = some ⟨12, 2, 0, 1355197, 375862, 2389, 65536⟩ := by
  decide +kernel

theorem context_12_375862_1355197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375862 ⟨1355197, by decide⟩ :=
  accepted_of_selected 12 375862 ⟨1355197, by decide⟩ ⟨12, 2, 0, 1355197, 375862, 2389, 65536⟩
    (by decide) selected_cut_48316

theorem selected_cut_48317 : selected 9 ⟨1355240, by decide⟩
    (prefixPartial 12 375863) = some ⟨12, 2, 0, 1355240, 375863, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_375863_1355240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375863 ⟨1355240, by decide⟩ :=
  accepted_of_selected 12 375863 ⟨1355240, by decide⟩ ⟨12, 2, 0, 1355240, 375863, 2265, 65536⟩
    (by decide) selected_cut_48317

theorem unmarked_context_11_93965_1355241 : frontier 10 ⟨1355241, by decide⟩
    (prefixCache 11 93965) (prefixPartial 11 93965) = false := by
  decide +kernel

theorem node_context_11_93965_1355241 : EJMOriginalGlobalDAGData.nodes 10 ⟨1355241, by decide⟩ =
    .split (coordinate 11) (![⟨1355109, by decide⟩,⟨1355146, by decide⟩,⟨1355197, by decide⟩,⟨1355240, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93965_1355241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93965 ⟨1355241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93965
    ⟨1355241, by decide⟩ (by decide) (![⟨1355109, by decide⟩,⟨1355146, by decide⟩,⟨1355197, by decide⟩,⟨1355240, by decide⟩]) unmarked_context_11_93965_1355241 node_context_11_93965_1355241
  intro a
  fin_cases a
  · exact context_12_375860_1355109
  · exact context_12_375861_1355146
  · exact context_12_375862_1355197
  · exact context_12_375863_1355240

theorem selected_cut_48318 : selected 10 ⟨1355311, by decide⟩
    (prefixPartial 11 93966) = some ⟨11, 2, 0, 1355311, 93966, 3653, 262144⟩ := by
  decide +kernel

theorem context_11_93966_1355311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93966 ⟨1355311, by decide⟩ :=
  accepted_of_selected 11 93966 ⟨1355311, by decide⟩ ⟨11, 2, 0, 1355311, 93966, 3653, 262144⟩
    (by decide) selected_cut_48318

theorem selected_cut_48319 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 93967) = some ⟨11, 1, 0, 977886, 93967, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93967_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93967 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 93967 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 93967, 1, 262144⟩
    (by decide) selected_cut_48319

theorem unmarked_context_10_23491_1355312 : frontier 11 ⟨1355312, by decide⟩
    (prefixCache 10 23491) (prefixPartial 10 23491) = false := by
  decide +kernel

theorem node_context_10_23491_1355312 : EJMOriginalGlobalDAGData.nodes 11 ⟨1355312, by decide⟩ =
    .split (coordinate 10) (![⟨1355060, by decide⟩,⟨1355241, by decide⟩,⟨1355311, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23491_1355312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23491 ⟨1355312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23491
    ⟨1355312, by decide⟩ (by decide) (![⟨1355060, by decide⟩,⟨1355241, by decide⟩,⟨1355311, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23491_1355312 node_context_10_23491_1355312
  intro a
  fin_cases a
  · exact context_11_93964_1355060
  · exact context_11_93965_1355241
  · exact context_11_93966_1355311
  · exact context_11_93967_977886

theorem unmarked_context_9_5872_1355313 : frontier 12 ⟨1355313, by decide⟩
    (prefixCache 9 5872) (prefixPartial 9 5872) = false := by
  decide +kernel

theorem node_context_9_5872_1355313 : EJMOriginalGlobalDAGData.nodes 12 ⟨1355313, by decide⟩ =
    .split (coordinate 9) (![⟨1354064, by decide⟩,⟨1354576, by decide⟩,⟨1354950, by decide⟩,⟨1355312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5872_1355313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5872 ⟨1355313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5872
    ⟨1355313, by decide⟩ (by decide) (![⟨1354064, by decide⟩,⟨1354576, by decide⟩,⟨1354950, by decide⟩,⟨1355312, by decide⟩]) unmarked_context_9_5872_1355313 node_context_9_5872_1355313
  intro a
  fin_cases a
  · exact context_10_23488_1354064
  · exact context_10_23489_1354576
  · exact context_10_23490_1354950
  · exact context_10_23491_1355312

theorem selected_cut_48320 : selected 10 ⟨1355391, by decide⟩
    (prefixPartial 11 93968) = some ⟨11, 2, 0, 1355391, 93968, 3533, 262144⟩ := by
  decide +kernel

theorem context_11_93968_1355391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93968 ⟨1355391, by decide⟩ :=
  accepted_of_selected 11 93968 ⟨1355391, by decide⟩ ⟨11, 2, 0, 1355391, 93968, 3533, 262144⟩
    (by decide) selected_cut_48320

theorem selected_cut_48321 : selected 9 ⟨1355428, by decide⟩
    (prefixPartial 12 375876) = some ⟨12, 2, 0, 1355428, 375876, 2161, 65536⟩ := by
  decide +kernel

theorem context_12_375876_1355428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375876 ⟨1355428, by decide⟩ :=
  accepted_of_selected 12 375876 ⟨1355428, by decide⟩ ⟨12, 2, 0, 1355428, 375876, 2161, 65536⟩
    (by decide) selected_cut_48321

theorem selected_cut_48322 : selected 9 ⟨849560, by decide⟩
    (prefixPartial 12 375877) = some ⟨12, 1, 0, 849560, 375877, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375877_849560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375877 ⟨849560, by decide⟩ :=
  accepted_of_selected 12 375877 ⟨849560, by decide⟩ ⟨12, 1, 0, 849560, 375877, 1, 65536⟩
    (by decide) selected_cut_48322

theorem selected_cut_48323 : selected 9 ⟨1355465, by decide⟩
    (prefixPartial 12 375878) = some ⟨12, 2, 0, 1355465, 375878, 2141, 65536⟩ := by
  decide +kernel

theorem context_12_375878_1355465 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375878 ⟨1355465, by decide⟩ :=
  accepted_of_selected 12 375878 ⟨1355465, by decide⟩ ⟨12, 2, 0, 1355465, 375878, 2141, 65536⟩
    (by decide) selected_cut_48323

theorem selected_cut_48324 : selected 9 ⟨1355506, by decide⟩
    (prefixPartial 12 375879) = some ⟨12, 2, 0, 1355506, 375879, 2013, 65536⟩ := by
  decide +kernel

theorem context_12_375879_1355506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375879 ⟨1355506, by decide⟩ :=
  accepted_of_selected 12 375879 ⟨1355506, by decide⟩ ⟨12, 2, 0, 1355506, 375879, 2013, 65536⟩
    (by decide) selected_cut_48324

theorem unmarked_context_11_93969_1355507 : frontier 10 ⟨1355507, by decide⟩
    (prefixCache 11 93969) (prefixPartial 11 93969) = false := by
  decide +kernel

theorem node_context_11_93969_1355507 : EJMOriginalGlobalDAGData.nodes 10 ⟨1355507, by decide⟩ =
    .split (coordinate 11) (![⟨1355428, by decide⟩,⟨849560, by decide⟩,⟨1355465, by decide⟩,⟨1355506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93969_1355507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93969 ⟨1355507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93969
    ⟨1355507, by decide⟩ (by decide) (![⟨1355428, by decide⟩,⟨849560, by decide⟩,⟨1355465, by decide⟩,⟨1355506, by decide⟩]) unmarked_context_11_93969_1355507 node_context_11_93969_1355507
  intro a
  fin_cases a
  · exact context_12_375876_1355428
  · exact context_12_375877_849560
  · exact context_12_375878_1355465
  · exact context_12_375879_1355506

theorem selected_cut_48325 : selected 10 ⟨1355580, by decide⟩
    (prefixPartial 11 93970) = some ⟨11, 2, 0, 1355580, 93970, 3313, 262144⟩ := by
  decide +kernel

theorem context_11_93970_1355580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93970 ⟨1355580, by decide⟩ :=
  accepted_of_selected 11 93970 ⟨1355580, by decide⟩ ⟨11, 2, 0, 1355580, 93970, 3313, 262144⟩
    (by decide) selected_cut_48325

theorem selected_cut_48326 : selected 9 ⟨1355616, by decide⟩
    (prefixPartial 12 375884) = some ⟨12, 2, 0, 1355616, 375884, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_375884_1355616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375884 ⟨1355616, by decide⟩ :=
  accepted_of_selected 12 375884 ⟨1355616, by decide⟩ ⟨12, 2, 0, 1355616, 375884, 1721, 65536⟩
    (by decide) selected_cut_48326

theorem selected_cut_48327 : selected 9 ⟨1355644, by decide⟩
    (prefixPartial 12 375885) = some ⟨12, 2, 0, 1355644, 375885, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_375885_1355644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375885 ⟨1355644, by decide⟩ :=
  accepted_of_selected 12 375885 ⟨1355644, by decide⟩ ⟨12, 2, 0, 1355644, 375885, 1561, 65536⟩
    (by decide) selected_cut_48327

theorem selected_cut_48328 : selected 9 ⟨1355679, by decide⟩
    (prefixPartial 12 375886) = some ⟨12, 2, 0, 1355679, 375886, 1825, 65536⟩ := by
  decide +kernel

theorem context_12_375886_1355679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375886 ⟨1355679, by decide⟩ :=
  accepted_of_selected 12 375886 ⟨1355679, by decide⟩ ⟨12, 2, 0, 1355679, 375886, 1825, 65536⟩
    (by decide) selected_cut_48328

theorem selected_cut_48329 : selected 9 ⟨760511, by decide⟩
    (prefixPartial 12 375887) = some ⟨12, 1, 0, 760511, 375887, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375887_760511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375887 ⟨760511, by decide⟩ :=
  accepted_of_selected 12 375887 ⟨760511, by decide⟩ ⟨12, 1, 0, 760511, 375887, 1, 65536⟩
    (by decide) selected_cut_48329

theorem unmarked_context_11_93971_1355680 : frontier 10 ⟨1355680, by decide⟩
    (prefixCache 11 93971) (prefixPartial 11 93971) = false := by
  decide +kernel

theorem node_context_11_93971_1355680 : EJMOriginalGlobalDAGData.nodes 10 ⟨1355680, by decide⟩ =
    .split (coordinate 11) (![⟨1355616, by decide⟩,⟨1355644, by decide⟩,⟨1355679, by decide⟩,⟨760511, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93971_1355680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93971 ⟨1355680, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93971
    ⟨1355680, by decide⟩ (by decide) (![⟨1355616, by decide⟩,⟨1355644, by decide⟩,⟨1355679, by decide⟩,⟨760511, by decide⟩]) unmarked_context_11_93971_1355680 node_context_11_93971_1355680
  intro a
  fin_cases a
  · exact context_12_375884_1355616
  · exact context_12_375885_1355644
  · exact context_12_375886_1355679
  · exact context_12_375887_760511

theorem unmarked_context_10_23492_1355681 : frontier 11 ⟨1355681, by decide⟩
    (prefixCache 10 23492) (prefixPartial 10 23492) = false := by
  decide +kernel

theorem node_context_10_23492_1355681 : EJMOriginalGlobalDAGData.nodes 11 ⟨1355681, by decide⟩ =
    .split (coordinate 10) (![⟨1355391, by decide⟩,⟨1355507, by decide⟩,⟨1355580, by decide⟩,⟨1355680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23492_1355681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23492 ⟨1355681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23492
    ⟨1355681, by decide⟩ (by decide) (![⟨1355391, by decide⟩,⟨1355507, by decide⟩,⟨1355580, by decide⟩,⟨1355680, by decide⟩]) unmarked_context_10_23492_1355681 node_context_10_23492_1355681
  intro a
  fin_cases a
  · exact context_11_93968_1355391
  · exact context_11_93969_1355507
  · exact context_11_93970_1355580
  · exact context_11_93971_1355680

theorem selected_cut_48330 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 23493) = some ⟨10, 1, 0, 893098, 23493, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_23493_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23493 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 23493 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 23493, 1, 1048576⟩
    (by decide) selected_cut_48330

theorem selected_cut_48331 : selected 10 ⟨1355738, by decide⟩
    (prefixPartial 11 93976) = some ⟨11, 2, 0, 1355738, 93976, 2865, 262144⟩ := by
  decide +kernel

theorem context_11_93976_1355738 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93976 ⟨1355738, by decide⟩ :=
  accepted_of_selected 11 93976 ⟨1355738, by decide⟩ ⟨11, 2, 0, 1355738, 93976, 2865, 262144⟩
    (by decide) selected_cut_48331

theorem selected_cut_48332 : selected 9 ⟨1355774, by decide⟩
    (prefixPartial 12 375908) = some ⟨12, 2, 0, 1355774, 375908, 1629, 65536⟩ := by
  decide +kernel

theorem context_12_375908_1355774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375908 ⟨1355774, by decide⟩ :=
  accepted_of_selected 12 375908 ⟨1355774, by decide⟩ ⟨12, 2, 0, 1355774, 375908, 1629, 65536⟩
    (by decide) selected_cut_48332

theorem selected_cut_48333 : selected 9 ⟨1256866, by decide⟩
    (prefixPartial 12 375909) = some ⟨12, 1, 0, 1256866, 375909, 1, 65536⟩ := by
  decide +kernel

theorem context_12_375909_1256866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375909 ⟨1256866, by decide⟩ :=
  accepted_of_selected 12 375909 ⟨1256866, by decide⟩ ⟨12, 1, 0, 1256866, 375909, 1, 65536⟩
    (by decide) selected_cut_48333

theorem selected_cut_48334 : selected 9 ⟨1355807, by decide⟩
    (prefixPartial 12 375910) = some ⟨12, 2, 0, 1355807, 375910, 1565, 65536⟩ := by
  decide +kernel

theorem context_12_375910_1355807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375910 ⟨1355807, by decide⟩ :=
  accepted_of_selected 12 375910 ⟨1355807, by decide⟩ ⟨12, 2, 0, 1355807, 375910, 1565, 65536⟩
    (by decide) selected_cut_48334

theorem selected_cut_48335 : selected 9 ⟨1355833, by decide⟩
    (prefixPartial 12 375911) = some ⟨12, 2, 0, 1355833, 375911, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_375911_1355833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 375911 ⟨1355833, by decide⟩ :=
  accepted_of_selected 12 375911 ⟨1355833, by decide⟩ ⟨12, 2, 0, 1355833, 375911, 1597, 65536⟩
    (by decide) selected_cut_48335

theorem unmarked_context_11_93977_1355834 : frontier 10 ⟨1355834, by decide⟩
    (prefixCache 11 93977) (prefixPartial 11 93977) = false := by
  decide +kernel

theorem node_context_11_93977_1355834 : EJMOriginalGlobalDAGData.nodes 10 ⟨1355834, by decide⟩ =
    .split (coordinate 11) (![⟨1355774, by decide⟩,⟨1256866, by decide⟩,⟨1355807, by decide⟩,⟨1355833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_93977_1355834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93977 ⟨1355834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 93977
    ⟨1355834, by decide⟩ (by decide) (![⟨1355774, by decide⟩,⟨1256866, by decide⟩,⟨1355807, by decide⟩,⟨1355833, by decide⟩]) unmarked_context_11_93977_1355834 node_context_11_93977_1355834
  intro a
  fin_cases a
  · exact context_12_375908_1355774
  · exact context_12_375909_1256866
  · exact context_12_375910_1355807
  · exact context_12_375911_1355833

theorem selected_cut_48336 : selected 10 ⟨1355886, by decide⟩
    (prefixPartial 11 93978) = some ⟨11, 2, 0, 1355886, 93978, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_93978_1355886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93978 ⟨1355886, by decide⟩ :=
  accepted_of_selected 11 93978 ⟨1355886, by decide⟩ ⟨11, 2, 0, 1355886, 93978, 1685, 262144⟩
    (by decide) selected_cut_48336

theorem selected_cut_48337 : selected 10 ⟨1355959, by decide⟩
    (prefixPartial 11 93979) = some ⟨11, 2, 0, 1355959, 93979, 3857, 262144⟩ := by
  decide +kernel

theorem context_11_93979_1355959 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93979 ⟨1355959, by decide⟩ :=
  accepted_of_selected 11 93979 ⟨1355959, by decide⟩ ⟨11, 2, 0, 1355959, 93979, 3857, 262144⟩
    (by decide) selected_cut_48337

theorem unmarked_context_10_23494_1355960 : frontier 11 ⟨1355960, by decide⟩
    (prefixCache 10 23494) (prefixPartial 10 23494) = false := by
  decide +kernel

theorem node_context_10_23494_1355960 : EJMOriginalGlobalDAGData.nodes 11 ⟨1355960, by decide⟩ =
    .split (coordinate 10) (![⟨1355738, by decide⟩,⟨1355834, by decide⟩,⟨1355886, by decide⟩,⟨1355959, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23494_1355960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23494 ⟨1355960, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23494
    ⟨1355960, by decide⟩ (by decide) (![⟨1355738, by decide⟩,⟨1355834, by decide⟩,⟨1355886, by decide⟩,⟨1355959, by decide⟩]) unmarked_context_10_23494_1355960 node_context_10_23494_1355960
  intro a
  fin_cases a
  · exact context_11_93976_1355738
  · exact context_11_93977_1355834
  · exact context_11_93978_1355886
  · exact context_11_93979_1355959

theorem selected_cut_48338 : selected 10 ⟨1356014, by decide⟩
    (prefixPartial 11 93980) = some ⟨11, 2, 0, 1356014, 93980, 2709, 262144⟩ := by
  decide +kernel

theorem context_11_93980_1356014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93980 ⟨1356014, by decide⟩ :=
  accepted_of_selected 11 93980 ⟨1356014, by decide⟩ ⟨11, 2, 0, 1356014, 93980, 2709, 262144⟩
    (by decide) selected_cut_48338

theorem selected_cut_48339 : selected 10 ⟨1356081, by decide⟩
    (prefixPartial 11 93981) = some ⟨11, 2, 0, 1356081, 93981, 3157, 262144⟩ := by
  decide +kernel

theorem context_11_93981_1356081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93981 ⟨1356081, by decide⟩ :=
  accepted_of_selected 11 93981 ⟨1356081, by decide⟩ ⟨11, 2, 0, 1356081, 93981, 3157, 262144⟩
    (by decide) selected_cut_48339

theorem selected_cut_48340 : selected 10 ⟨1356130, by decide⟩
    (prefixPartial 11 93982) = some ⟨11, 2, 0, 1356130, 93982, 2553, 262144⟩ := by
  decide +kernel

theorem context_11_93982_1356130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93982 ⟨1356130, by decide⟩ :=
  accepted_of_selected 11 93982 ⟨1356130, by decide⟩ ⟨11, 2, 0, 1356130, 93982, 2553, 262144⟩
    (by decide) selected_cut_48340

theorem selected_cut_48341 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 93983) = some ⟨11, 1, 0, 977886, 93983, 1, 262144⟩ := by
  decide +kernel

theorem context_11_93983_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93983 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 93983 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 93983, 1, 262144⟩
    (by decide) selected_cut_48341

theorem unmarked_context_10_23495_1356131 : frontier 11 ⟨1356131, by decide⟩
    (prefixCache 10 23495) (prefixPartial 10 23495) = false := by
  decide +kernel

theorem node_context_10_23495_1356131 : EJMOriginalGlobalDAGData.nodes 11 ⟨1356131, by decide⟩ =
    .split (coordinate 10) (![⟨1356014, by decide⟩,⟨1356081, by decide⟩,⟨1356130, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23495_1356131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23495 ⟨1356131, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23495
    ⟨1356131, by decide⟩ (by decide) (![⟨1356014, by decide⟩,⟨1356081, by decide⟩,⟨1356130, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_23495_1356131 node_context_10_23495_1356131
  intro a
  fin_cases a
  · exact context_11_93980_1356014
  · exact context_11_93981_1356081
  · exact context_11_93982_1356130
  · exact context_11_93983_977886

theorem unmarked_context_9_5873_1356132 : frontier 12 ⟨1356132, by decide⟩
    (prefixCache 9 5873) (prefixPartial 9 5873) = false := by
  decide +kernel

theorem node_context_9_5873_1356132 : EJMOriginalGlobalDAGData.nodes 12 ⟨1356132, by decide⟩ =
    .split (coordinate 9) (![⟨1355681, by decide⟩,⟨893098, by decide⟩,⟨1355960, by decide⟩,⟨1356131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5873_1356132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5873 ⟨1356132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5873
    ⟨1356132, by decide⟩ (by decide) (![⟨1355681, by decide⟩,⟨893098, by decide⟩,⟨1355960, by decide⟩,⟨1356131, by decide⟩]) unmarked_context_9_5873_1356132 node_context_9_5873_1356132
  intro a
  fin_cases a
  · exact context_10_23492_1355681
  · exact context_10_23493_893098
  · exact context_10_23494_1355960
  · exact context_10_23495_1356131

theorem selected_cut_48342 : selected 10 ⟨1356159, by decide⟩
    (prefixPartial 11 93984) = some ⟨11, 2, 0, 1356159, 93984, 1089, 262144⟩ := by
  decide +kernel

theorem context_11_93984_1356159 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93984 ⟨1356159, by decide⟩ :=
  accepted_of_selected 11 93984 ⟨1356159, by decide⟩ ⟨11, 2, 0, 1356159, 93984, 1089, 262144⟩
    (by decide) selected_cut_48342

theorem selected_cut_48343 : selected 10 ⟨1356251, by decide⟩
    (prefixPartial 11 93985) = some ⟨11, 2, 0, 1356251, 93985, 3141, 262144⟩ := by
  decide +kernel

theorem context_11_93985_1356251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93985 ⟨1356251, by decide⟩ :=
  accepted_of_selected 11 93985 ⟨1356251, by decide⟩ ⟨11, 2, 0, 1356251, 93985, 3141, 262144⟩
    (by decide) selected_cut_48343

theorem selected_cut_48344 : selected 10 ⟨1356310, by decide⟩
    (prefixPartial 11 93986) = some ⟨11, 2, 0, 1356310, 93986, 3333, 262144⟩ := by
  decide +kernel

theorem context_11_93986_1356310 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93986 ⟨1356310, by decide⟩ :=
  accepted_of_selected 11 93986 ⟨1356310, by decide⟩ ⟨11, 2, 0, 1356310, 93986, 3333, 262144⟩
    (by decide) selected_cut_48344

theorem selected_cut_48345 : selected 10 ⟨1356341, by decide⟩
    (prefixPartial 11 93987) = some ⟨11, 2, 0, 1356341, 93987, 1805, 262144⟩ := by
  decide +kernel

theorem context_11_93987_1356341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93987 ⟨1356341, by decide⟩ :=
  accepted_of_selected 11 93987 ⟨1356341, by decide⟩ ⟨11, 2, 0, 1356341, 93987, 1805, 262144⟩
    (by decide) selected_cut_48345

theorem unmarked_context_10_23496_1356342 : frontier 11 ⟨1356342, by decide⟩
    (prefixCache 10 23496) (prefixPartial 10 23496) = false := by
  decide +kernel

theorem node_context_10_23496_1356342 : EJMOriginalGlobalDAGData.nodes 11 ⟨1356342, by decide⟩ =
    .split (coordinate 10) (![⟨1356159, by decide⟩,⟨1356251, by decide⟩,⟨1356310, by decide⟩,⟨1356341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23496_1356342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23496 ⟨1356342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23496
    ⟨1356342, by decide⟩ (by decide) (![⟨1356159, by decide⟩,⟨1356251, by decide⟩,⟨1356310, by decide⟩,⟨1356341, by decide⟩]) unmarked_context_10_23496_1356342 node_context_10_23496_1356342
  intro a
  fin_cases a
  · exact context_11_93984_1356159
  · exact context_11_93985_1356251
  · exact context_11_93986_1356310
  · exact context_11_93987_1356341

theorem selected_cut_48346 : selected 10 ⟨1356377, by decide⟩
    (prefixPartial 11 93988) = some ⟨11, 2, 0, 1356377, 93988, 1721, 262144⟩ := by
  decide +kernel

theorem context_11_93988_1356377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93988 ⟨1356377, by decide⟩ :=
  accepted_of_selected 11 93988 ⟨1356377, by decide⟩ ⟨11, 2, 0, 1356377, 93988, 1721, 262144⟩
    (by decide) selected_cut_48346

theorem selected_cut_48347 : selected 10 ⟨1356395, by decide⟩
    (prefixPartial 11 93989) = some ⟨11, 2, 0, 1356395, 93989, 913, 262144⟩ := by
  decide +kernel

theorem context_11_93989_1356395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93989 ⟨1356395, by decide⟩ :=
  accepted_of_selected 11 93989 ⟨1356395, by decide⟩ ⟨11, 2, 0, 1356395, 93989, 913, 262144⟩
    (by decide) selected_cut_48347

theorem selected_cut_48348 : selected 10 ⟨1356435, by decide⟩
    (prefixPartial 11 93990) = some ⟨11, 2, 0, 1356435, 93990, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_93990_1356435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93990 ⟨1356435, by decide⟩ :=
  accepted_of_selected 11 93990 ⟨1356435, by decide⟩ ⟨11, 2, 0, 1356435, 93990, 2329, 262144⟩
    (by decide) selected_cut_48348

theorem selected_cut_48349 : selected 10 ⟨1356468, by decide⟩
    (prefixPartial 11 93991) = some ⟨11, 2, 0, 1356468, 93991, 1869, 262144⟩ := by
  decide +kernel

theorem context_11_93991_1356468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 93991 ⟨1356468, by decide⟩ :=
  accepted_of_selected 11 93991 ⟨1356468, by decide⟩ ⟨11, 2, 0, 1356468, 93991, 1869, 262144⟩
    (by decide) selected_cut_48349

theorem unmarked_context_10_23497_1356469 : frontier 11 ⟨1356469, by decide⟩
    (prefixCache 10 23497) (prefixPartial 10 23497) = false := by
  decide +kernel

theorem node_context_10_23497_1356469 : EJMOriginalGlobalDAGData.nodes 11 ⟨1356469, by decide⟩ =
    .split (coordinate 10) (![⟨1356377, by decide⟩,⟨1356395, by decide⟩,⟨1356435, by decide⟩,⟨1356468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23497_1356469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23497 ⟨1356469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23497
    ⟨1356469, by decide⟩ (by decide) (![⟨1356377, by decide⟩,⟨1356395, by decide⟩,⟨1356435, by decide⟩,⟨1356468, by decide⟩]) unmarked_context_10_23497_1356469 node_context_10_23497_1356469
  intro a
  fin_cases a
  · exact context_11_93988_1356377
  · exact context_11_93989_1356395
  · exact context_11_93990_1356435
  · exact context_11_93991_1356468

theorem selected_cut_48350 : selected 11 ⟨1356508, by decide⟩
    (prefixPartial 10 23498) = some ⟨10, 2, 0, 1356508, 23498, 1725, 1048576⟩ := by
  decide +kernel

theorem context_10_23498_1356508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23498 ⟨1356508, by decide⟩ :=
  accepted_of_selected 10 23498 ⟨1356508, by decide⟩ ⟨10, 2, 0, 1356508, 23498, 1725, 1048576⟩
    (by decide) selected_cut_48350

theorem selected_cut_48351 : selected 11 ⟨1356591, by decide⟩
    (prefixPartial 10 23499) = some ⟨10, 2, 0, 1356591, 23499, 3537, 1048576⟩ := by
  decide +kernel

theorem context_10_23499_1356591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23499 ⟨1356591, by decide⟩ :=
  accepted_of_selected 10 23499 ⟨1356591, by decide⟩ ⟨10, 2, 0, 1356591, 23499, 3537, 1048576⟩
    (by decide) selected_cut_48351

theorem unmarked_context_9_5874_1356592 : frontier 12 ⟨1356592, by decide⟩
    (prefixCache 9 5874) (prefixPartial 9 5874) = false := by
  decide +kernel

theorem node_context_9_5874_1356592 : EJMOriginalGlobalDAGData.nodes 12 ⟨1356592, by decide⟩ =
    .split (coordinate 9) (![⟨1356342, by decide⟩,⟨1356469, by decide⟩,⟨1356508, by decide⟩,⟨1356591, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5874_1356592 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5874 ⟨1356592, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5874
    ⟨1356592, by decide⟩ (by decide) (![⟨1356342, by decide⟩,⟨1356469, by decide⟩,⟨1356508, by decide⟩,⟨1356591, by decide⟩]) unmarked_context_9_5874_1356592 node_context_9_5874_1356592
  intro a
  fin_cases a
  · exact context_10_23496_1356342
  · exact context_10_23497_1356469
  · exact context_10_23498_1356508
  · exact context_10_23499_1356591

theorem selected_cut_48352 : selected 11 ⟨1356641, by decide⟩
    (prefixPartial 10 23500) = some ⟨10, 2, 0, 1356641, 23500, 2349, 1048576⟩ := by
  decide +kernel

theorem context_10_23500_1356641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23500 ⟨1356641, by decide⟩ :=
  accepted_of_selected 10 23500 ⟨1356641, by decide⟩ ⟨10, 2, 0, 1356641, 23500, 2349, 1048576⟩
    (by decide) selected_cut_48352

theorem selected_cut_48353 : selected 11 ⟨1356687, by decide⟩
    (prefixPartial 10 23501) = some ⟨10, 2, 0, 1356687, 23501, 1697, 1048576⟩ := by
  decide +kernel

theorem context_10_23501_1356687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23501 ⟨1356687, by decide⟩ :=
  accepted_of_selected 10 23501 ⟨1356687, by decide⟩ ⟨10, 2, 0, 1356687, 23501, 1697, 1048576⟩
    (by decide) selected_cut_48353

theorem selected_cut_48354 : selected 11 ⟨1356714, by decide⟩
    (prefixPartial 10 23502) = some ⟨10, 2, 0, 1356714, 23502, 773, 1048576⟩ := by
  decide +kernel

theorem context_10_23502_1356714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23502 ⟨1356714, by decide⟩ :=
  accepted_of_selected 10 23502 ⟨1356714, by decide⟩ ⟨10, 2, 0, 1356714, 23502, 773, 1048576⟩
    (by decide) selected_cut_48354

theorem selected_cut_48355 : selected 11 ⟨1356723, by decide⟩
    (prefixPartial 10 23503) = some ⟨10, 2, 0, 1356723, 23503, 97, 1048576⟩ := by
  decide +kernel

theorem context_10_23503_1356723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23503 ⟨1356723, by decide⟩ :=
  accepted_of_selected 10 23503 ⟨1356723, by decide⟩ ⟨10, 2, 0, 1356723, 23503, 97, 1048576⟩
    (by decide) selected_cut_48355

theorem unmarked_context_9_5875_1356724 : frontier 12 ⟨1356724, by decide⟩
    (prefixCache 9 5875) (prefixPartial 9 5875) = false := by
  decide +kernel

theorem node_context_9_5875_1356724 : EJMOriginalGlobalDAGData.nodes 12 ⟨1356724, by decide⟩ =
    .split (coordinate 9) (![⟨1356641, by decide⟩,⟨1356687, by decide⟩,⟨1356714, by decide⟩,⟨1356723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5875_1356724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5875 ⟨1356724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5875
    ⟨1356724, by decide⟩ (by decide) (![⟨1356641, by decide⟩,⟨1356687, by decide⟩,⟨1356714, by decide⟩,⟨1356723, by decide⟩]) unmarked_context_9_5875_1356724 node_context_9_5875_1356724
  intro a
  fin_cases a
  · exact context_10_23500_1356641
  · exact context_10_23501_1356687
  · exact context_10_23502_1356714
  · exact context_10_23503_1356723

theorem unmarked_context_8_1468_1356725 : frontier 13 ⟨1356725, by decide⟩
    (prefixCache 8 1468) (prefixPartial 8 1468) = false := by
  decide +kernel

theorem node_context_8_1468_1356725 : EJMOriginalGlobalDAGData.nodes 13 ⟨1356725, by decide⟩ =
    .split (coordinate 8) (![⟨1355313, by decide⟩,⟨1356132, by decide⟩,⟨1356592, by decide⟩,⟨1356724, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1468_1356725 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1468 ⟨1356725, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1468
    ⟨1356725, by decide⟩ (by decide) (![⟨1355313, by decide⟩,⟨1356132, by decide⟩,⟨1356592, by decide⟩,⟨1356724, by decide⟩]) unmarked_context_8_1468_1356725 node_context_8_1468_1356725
  intro a
  fin_cases a
  · exact context_9_5872_1355313
  · exact context_9_5873_1356132
  · exact context_9_5874_1356592
  · exact context_9_5875_1356724

theorem selected_cut_48356 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 94016) = some ⟨11, 1, 0, 434745, 94016, 1, 262144⟩ := by
  decide +kernel

theorem context_11_94016_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94016 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 94016 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 94016, 1, 262144⟩
    (by decide) selected_cut_48356

theorem selected_cut_48357 : selected 10 ⟨1356779, by decide⟩
    (prefixPartial 11 94017) = some ⟨11, 2, 0, 1356779, 94017, 1701, 262144⟩ := by
  decide +kernel

theorem context_11_94017_1356779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94017 ⟨1356779, by decide⟩ :=
  accepted_of_selected 11 94017 ⟨1356779, by decide⟩ ⟨11, 2, 0, 1356779, 94017, 1701, 262144⟩
    (by decide) selected_cut_48357

theorem selected_cut_48358 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 376072) = some ⟨12, 1, 0, 448748, 376072, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376072_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376072 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 376072 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 376072, 1, 65536⟩
    (by decide) selected_cut_48358

theorem selected_cut_48359 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 376073) = some ⟨12, 1, 0, 34034, 376073, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376073_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376073 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 376073 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 376073, 1, 65536⟩
    (by decide) selected_cut_48359

theorem selected_cut_48360 : selected 9 ⟨1356838, by decide⟩
    (prefixPartial 12 376074) = some ⟨12, 2, 0, 1356838, 376074, 2665, 65536⟩ := by
  decide +kernel

theorem context_12_376074_1356838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376074 ⟨1356838, by decide⟩ :=
  accepted_of_selected 12 376074 ⟨1356838, by decide⟩ ⟨12, 2, 0, 1356838, 376074, 2665, 65536⟩
    (by decide) selected_cut_48360

theorem selected_cut_48361 : selected 9 ⟨1356888, by decide⟩
    (prefixPartial 12 376075) = some ⟨12, 2, 0, 1356888, 376075, 2457, 65536⟩ := by
  decide +kernel

theorem context_12_376075_1356888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376075 ⟨1356888, by decide⟩ :=
  accepted_of_selected 12 376075 ⟨1356888, by decide⟩ ⟨12, 2, 0, 1356888, 376075, 2457, 65536⟩
    (by decide) selected_cut_48361

theorem unmarked_context_11_94018_1356889 : frontier 10 ⟨1356889, by decide⟩
    (prefixCache 11 94018) (prefixPartial 11 94018) = false := by
  decide +kernel

theorem node_context_11_94018_1356889 : EJMOriginalGlobalDAGData.nodes 10 ⟨1356889, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1356838, by decide⟩,⟨1356888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94018_1356889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94018 ⟨1356889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94018
    ⟨1356889, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨34034, by decide⟩,⟨1356838, by decide⟩,⟨1356888, by decide⟩]) unmarked_context_11_94018_1356889 node_context_11_94018_1356889
  intro a
  fin_cases a
  · exact context_12_376072_448748
  · exact context_12_376073_34034
  · exact context_12_376074_1356838
  · exact context_12_376075_1356888

theorem selected_cut_48362 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 376076) = some ⟨12, 1, 0, 448748, 376076, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376076_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376076 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 376076 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 376076, 1, 65536⟩
    (by decide) selected_cut_48362

theorem selected_cut_48363 : selected 9 ⟨1356954, by decide⟩
    (prefixPartial 12 376077) = some ⟨12, 2, 0, 1356954, 376077, 2801, 65536⟩ := by
  decide +kernel

theorem context_12_376077_1356954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376077 ⟨1356954, by decide⟩ :=
  accepted_of_selected 12 376077 ⟨1356954, by decide⟩ ⟨12, 2, 0, 1356954, 376077, 2801, 65536⟩
    (by decide) selected_cut_48363

theorem selected_cut_48364 : selected 9 ⟨1357008, by decide⟩
    (prefixPartial 12 376078) = some ⟨12, 2, 0, 1357008, 376078, 2473, 65536⟩ := by
  decide +kernel

theorem context_12_376078_1357008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376078 ⟨1357008, by decide⟩ :=
  accepted_of_selected 12 376078 ⟨1357008, by decide⟩ ⟨12, 2, 0, 1357008, 376078, 2473, 65536⟩
    (by decide) selected_cut_48364

theorem selected_cut_48365 : selected 9 ⟨1357062, by decide⟩
    (prefixPartial 12 376079) = some ⟨12, 2, 0, 1357062, 376079, 2449, 65536⟩ := by
  decide +kernel

theorem context_12_376079_1357062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376079 ⟨1357062, by decide⟩ :=
  accepted_of_selected 12 376079 ⟨1357062, by decide⟩ ⟨12, 2, 0, 1357062, 376079, 2449, 65536⟩
    (by decide) selected_cut_48365

theorem unmarked_context_11_94019_1357063 : frontier 10 ⟨1357063, by decide⟩
    (prefixCache 11 94019) (prefixPartial 11 94019) = false := by
  decide +kernel

theorem node_context_11_94019_1357063 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357063, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1356954, by decide⟩,⟨1357008, by decide⟩,⟨1357062, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94019_1357063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94019 ⟨1357063, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94019
    ⟨1357063, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1356954, by decide⟩,⟨1357008, by decide⟩,⟨1357062, by decide⟩]) unmarked_context_11_94019_1357063 node_context_11_94019_1357063
  intro a
  fin_cases a
  · exact context_12_376076_448748
  · exact context_12_376077_1356954
  · exact context_12_376078_1357008
  · exact context_12_376079_1357062

theorem unmarked_context_10_23504_1357064 : frontier 11 ⟨1357064, by decide⟩
    (prefixCache 10 23504) (prefixPartial 10 23504) = false := by
  decide +kernel

theorem node_context_10_23504_1357064 : EJMOriginalGlobalDAGData.nodes 11 ⟨1357064, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1356779, by decide⟩,⟨1356889, by decide⟩,⟨1357063, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23504_1357064 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23504 ⟨1357064, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23504
    ⟨1357064, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1356779, by decide⟩,⟨1356889, by decide⟩,⟨1357063, by decide⟩]) unmarked_context_10_23504_1357064 node_context_10_23504_1357064
  intro a
  fin_cases a
  · exact context_11_94016_434745
  · exact context_11_94017_1356779
  · exact context_11_94018_1356889
  · exact context_11_94019_1357063

theorem selected_cut_48366 : selected 9 ⟨789343, by decide⟩
    (prefixPartial 12 376080) = some ⟨12, 1, 0, 789343, 376080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376080_789343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376080 ⟨789343, by decide⟩ :=
  accepted_of_selected 12 376080 ⟨789343, by decide⟩ ⟨12, 1, 0, 789343, 376080, 1, 65536⟩
    (by decide) selected_cut_48366

theorem selected_cut_48367 : selected 9 ⟨1357114, by decide⟩
    (prefixPartial 12 376081) = some ⟨12, 2, 0, 1357114, 376081, 2521, 65536⟩ := by
  decide +kernel

theorem context_12_376081_1357114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376081 ⟨1357114, by decide⟩ :=
  accepted_of_selected 12 376081 ⟨1357114, by decide⟩ ⟨12, 2, 0, 1357114, 376081, 2521, 65536⟩
    (by decide) selected_cut_48367

theorem selected_cut_48368 : selected 9 ⟨1357154, by decide⟩
    (prefixPartial 12 376082) = some ⟨12, 2, 0, 1357154, 376082, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_376082_1357154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376082 ⟨1357154, by decide⟩ :=
  accepted_of_selected 12 376082 ⟨1357154, by decide⟩ ⟨12, 2, 0, 1357154, 376082, 2241, 65536⟩
    (by decide) selected_cut_48368

theorem selected_cut_48369 : selected 9 ⟨1357203, by decide⟩
    (prefixPartial 12 376083) = some ⟨12, 2, 0, 1357203, 376083, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_376083_1357203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376083 ⟨1357203, by decide⟩ :=
  accepted_of_selected 12 376083 ⟨1357203, by decide⟩ ⟨12, 2, 0, 1357203, 376083, 2369, 65536⟩
    (by decide) selected_cut_48369

theorem unmarked_context_11_94020_1357204 : frontier 10 ⟨1357204, by decide⟩
    (prefixCache 11 94020) (prefixPartial 11 94020) = false := by
  decide +kernel

theorem node_context_11_94020_1357204 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357204, by decide⟩ =
    .split (coordinate 11) (![⟨789343, by decide⟩,⟨1357114, by decide⟩,⟨1357154, by decide⟩,⟨1357203, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94020_1357204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94020 ⟨1357204, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94020
    ⟨1357204, by decide⟩ (by decide) (![⟨789343, by decide⟩,⟨1357114, by decide⟩,⟨1357154, by decide⟩,⟨1357203, by decide⟩]) unmarked_context_11_94020_1357204 node_context_11_94020_1357204
  intro a
  fin_cases a
  · exact context_12_376080_789343
  · exact context_12_376081_1357114
  · exact context_12_376082_1357154
  · exact context_12_376083_1357203

theorem selected_cut_48370 : selected 9 ⟨1357245, by decide⟩
    (prefixPartial 12 376084) = some ⟨12, 2, 0, 1357245, 376084, 2301, 65536⟩ := by
  decide +kernel

theorem context_12_376084_1357245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376084 ⟨1357245, by decide⟩ :=
  accepted_of_selected 12 376084 ⟨1357245, by decide⟩ ⟨12, 2, 0, 1357245, 376084, 2301, 65536⟩
    (by decide) selected_cut_48370

theorem selected_cut_48371 : selected 9 ⟨1172003, by decide⟩
    (prefixPartial 12 376085) = some ⟨12, 1, 0, 1172003, 376085, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376085_1172003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376085 ⟨1172003, by decide⟩ :=
  accepted_of_selected 12 376085 ⟨1172003, by decide⟩ ⟨12, 1, 0, 1172003, 376085, 1, 65536⟩
    (by decide) selected_cut_48371

theorem selected_cut_48372 : selected 9 ⟨1357284, by decide⟩
    (prefixPartial 12 376086) = some ⟨12, 2, 0, 1357284, 376086, 2281, 65536⟩ := by
  decide +kernel

theorem context_12_376086_1357284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376086 ⟨1357284, by decide⟩ :=
  accepted_of_selected 12 376086 ⟨1357284, by decide⟩ ⟨12, 2, 0, 1357284, 376086, 2281, 65536⟩
    (by decide) selected_cut_48372

theorem selected_cut_48373 : selected 9 ⟨692794, by decide⟩
    (prefixPartial 12 376087) = some ⟨12, 1, 0, 692794, 376087, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376087_692794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376087 ⟨692794, by decide⟩ :=
  accepted_of_selected 12 376087 ⟨692794, by decide⟩ ⟨12, 1, 0, 692794, 376087, 1, 65536⟩
    (by decide) selected_cut_48373

theorem unmarked_context_11_94021_1357285 : frontier 10 ⟨1357285, by decide⟩
    (prefixCache 11 94021) (prefixPartial 11 94021) = false := by
  decide +kernel

theorem node_context_11_94021_1357285 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357285, by decide⟩ =
    .split (coordinate 11) (![⟨1357245, by decide⟩,⟨1172003, by decide⟩,⟨1357284, by decide⟩,⟨692794, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94021_1357285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94021 ⟨1357285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94021
    ⟨1357285, by decide⟩ (by decide) (![⟨1357245, by decide⟩,⟨1172003, by decide⟩,⟨1357284, by decide⟩,⟨692794, by decide⟩]) unmarked_context_11_94021_1357285 node_context_11_94021_1357285
  intro a
  fin_cases a
  · exact context_12_376084_1357245
  · exact context_12_376085_1172003
  · exact context_12_376086_1357284
  · exact context_12_376087_692794

theorem selected_cut_48374 : selected 9 ⟨1072955, by decide⟩
    (prefixPartial 12 376088) = some ⟨12, 1, 0, 1072955, 376088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376088_1072955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376088 ⟨1072955, by decide⟩ :=
  accepted_of_selected 12 376088 ⟨1072955, by decide⟩ ⟨12, 1, 0, 1072955, 376088, 1, 65536⟩
    (by decide) selected_cut_48374

theorem selected_cut_48375 : selected 9 ⟨1357322, by decide⟩
    (prefixPartial 12 376089) = some ⟨12, 2, 0, 1357322, 376089, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_376089_1357322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376089 ⟨1357322, by decide⟩ :=
  accepted_of_selected 12 376089 ⟨1357322, by decide⟩ ⟨12, 2, 0, 1357322, 376089, 2249, 65536⟩
    (by decide) selected_cut_48375

theorem selected_cut_48376 : selected 9 ⟨811630, by decide⟩
    (prefixPartial 12 376090) = some ⟨12, 1, 0, 811630, 376090, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376090_811630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376090 ⟨811630, by decide⟩ :=
  accepted_of_selected 12 376090 ⟨811630, by decide⟩ ⟨12, 1, 0, 811630, 376090, 1, 65536⟩
    (by decide) selected_cut_48376

theorem selected_cut_48377 : selected 9 ⟨1357361, by decide⟩
    (prefixPartial 12 376091) = some ⟨12, 2, 0, 1357361, 376091, 2277, 65536⟩ := by
  decide +kernel

theorem context_12_376091_1357361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376091 ⟨1357361, by decide⟩ :=
  accepted_of_selected 12 376091 ⟨1357361, by decide⟩ ⟨12, 2, 0, 1357361, 376091, 2277, 65536⟩
    (by decide) selected_cut_48377

theorem unmarked_context_11_94022_1357362 : frontier 10 ⟨1357362, by decide⟩
    (prefixCache 11 94022) (prefixPartial 11 94022) = false := by
  decide +kernel

theorem node_context_11_94022_1357362 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357362, by decide⟩ =
    .split (coordinate 11) (![⟨1072955, by decide⟩,⟨1357322, by decide⟩,⟨811630, by decide⟩,⟨1357361, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94022_1357362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94022 ⟨1357362, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94022
    ⟨1357362, by decide⟩ (by decide) (![⟨1072955, by decide⟩,⟨1357322, by decide⟩,⟨811630, by decide⟩,⟨1357361, by decide⟩]) unmarked_context_11_94022_1357362 node_context_11_94022_1357362
  intro a
  fin_cases a
  · exact context_12_376088_1072955
  · exact context_12_376089_1357322
  · exact context_12_376090_811630
  · exact context_12_376091_1357361

theorem selected_cut_48378 : selected 9 ⟨1357395, by decide⟩
    (prefixPartial 12 376092) = some ⟨12, 2, 0, 1357395, 376092, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_376092_1357395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376092 ⟨1357395, by decide⟩ :=
  accepted_of_selected 12 376092 ⟨1357395, by decide⟩ ⟨12, 2, 0, 1357395, 376092, 1977, 65536⟩
    (by decide) selected_cut_48378

theorem selected_cut_48379 : selected 9 ⟨1357431, by decide⟩
    (prefixPartial 12 376093) = some ⟨12, 2, 0, 1357431, 376093, 2185, 65536⟩ := by
  decide +kernel

theorem context_12_376093_1357431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376093 ⟨1357431, by decide⟩ :=
  accepted_of_selected 12 376093 ⟨1357431, by decide⟩ ⟨12, 2, 0, 1357431, 376093, 2185, 65536⟩
    (by decide) selected_cut_48379

theorem selected_cut_48380 : selected 9 ⟨1357467, by decide⟩
    (prefixPartial 12 376094) = some ⟨12, 2, 0, 1357467, 376094, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_376094_1357467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376094 ⟨1357467, by decide⟩ :=
  accepted_of_selected 12 376094 ⟨1357467, by decide⟩ ⟨12, 2, 0, 1357467, 376094, 1961, 65536⟩
    (by decide) selected_cut_48380

theorem selected_cut_48381 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 376095) = some ⟨12, 1, 0, 757807, 376095, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376095_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376095 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 376095 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 376095, 1, 65536⟩
    (by decide) selected_cut_48381

theorem unmarked_context_11_94023_1357468 : frontier 10 ⟨1357468, by decide⟩
    (prefixCache 11 94023) (prefixPartial 11 94023) = false := by
  decide +kernel

theorem node_context_11_94023_1357468 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357468, by decide⟩ =
    .split (coordinate 11) (![⟨1357395, by decide⟩,⟨1357431, by decide⟩,⟨1357467, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94023_1357468 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94023 ⟨1357468, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94023
    ⟨1357468, by decide⟩ (by decide) (![⟨1357395, by decide⟩,⟨1357431, by decide⟩,⟨1357467, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_94023_1357468 node_context_11_94023_1357468
  intro a
  fin_cases a
  · exact context_12_376092_1357395
  · exact context_12_376093_1357431
  · exact context_12_376094_1357467
  · exact context_12_376095_757807

theorem unmarked_context_10_23505_1357469 : frontier 11 ⟨1357469, by decide⟩
    (prefixCache 10 23505) (prefixPartial 10 23505) = false := by
  decide +kernel

theorem node_context_10_23505_1357469 : EJMOriginalGlobalDAGData.nodes 11 ⟨1357469, by decide⟩ =
    .split (coordinate 10) (![⟨1357204, by decide⟩,⟨1357285, by decide⟩,⟨1357362, by decide⟩,⟨1357468, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_23505_1357469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 23505 ⟨1357469, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 23505
    ⟨1357469, by decide⟩ (by decide) (![⟨1357204, by decide⟩,⟨1357285, by decide⟩,⟨1357362, by decide⟩,⟨1357468, by decide⟩]) unmarked_context_10_23505_1357469 node_context_10_23505_1357469
  intro a
  fin_cases a
  · exact context_11_94020_1357204
  · exact context_11_94021_1357285
  · exact context_11_94022_1357362
  · exact context_11_94023_1357468

theorem selected_cut_48382 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 376096) = some ⟨12, 1, 0, 435790, 376096, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376096_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376096 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 376096 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 376096, 1, 65536⟩
    (by decide) selected_cut_48382

theorem selected_cut_48383 : selected 9 ⟨1357511, by decide⟩
    (prefixPartial 12 376097) = some ⟨12, 2, 0, 1357511, 376097, 2321, 65536⟩ := by
  decide +kernel

theorem context_12_376097_1357511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376097 ⟨1357511, by decide⟩ :=
  accepted_of_selected 12 376097 ⟨1357511, by decide⟩ ⟨12, 2, 0, 1357511, 376097, 2321, 65536⟩
    (by decide) selected_cut_48383

theorem selected_cut_48384 : selected 9 ⟨1357550, by decide⟩
    (prefixPartial 12 376098) = some ⟨12, 2, 0, 1357550, 376098, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_376098_1357550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376098 ⟨1357550, by decide⟩ :=
  accepted_of_selected 12 376098 ⟨1357550, by decide⟩ ⟨12, 2, 0, 1357550, 376098, 2221, 65536⟩
    (by decide) selected_cut_48384

theorem selected_cut_48385 : selected 9 ⟨1357590, by decide⟩
    (prefixPartial 12 376099) = some ⟨12, 2, 0, 1357590, 376099, 2081, 65536⟩ := by
  decide +kernel

theorem context_12_376099_1357590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376099 ⟨1357590, by decide⟩ :=
  accepted_of_selected 12 376099 ⟨1357590, by decide⟩ ⟨12, 2, 0, 1357590, 376099, 2081, 65536⟩
    (by decide) selected_cut_48385

theorem unmarked_context_11_94024_1357591 : frontier 10 ⟨1357591, by decide⟩
    (prefixCache 11 94024) (prefixPartial 11 94024) = false := by
  decide +kernel

theorem node_context_11_94024_1357591 : EJMOriginalGlobalDAGData.nodes 10 ⟨1357591, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨1357511, by decide⟩,⟨1357550, by decide⟩,⟨1357590, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_94024_1357591 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 94024 ⟨1357591, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 94024
    ⟨1357591, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨1357511, by decide⟩,⟨1357550, by decide⟩,⟨1357590, by decide⟩]) unmarked_context_11_94024_1357591 node_context_11_94024_1357591
  intro a
  fin_cases a
  · exact context_12_376096_435790
  · exact context_12_376097_1357511
  · exact context_12_376098_1357550
  · exact context_12_376099_1357590

theorem selected_cut_48386 : selected 9 ⟨435790, by decide⟩
    (prefixPartial 12 376100) = some ⟨12, 1, 0, 435790, 376100, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376100_435790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376100 ⟨435790, by decide⟩ :=
  accepted_of_selected 12 376100 ⟨435790, by decide⟩ ⟨12, 1, 0, 435790, 376100, 1, 65536⟩
    (by decide) selected_cut_48386

theorem selected_cut_48387 : selected 9 ⟨891951, by decide⟩
    (prefixPartial 12 376101) = some ⟨12, 1, 0, 891951, 376101, 1, 65536⟩ := by
  decide +kernel

theorem context_12_376101_891951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 376101 ⟨891951, by decide⟩ :=
  accepted_of_selected 12 376101 ⟨891951, by decide⟩ ⟨12, 1, 0, 891951, 376101, 1, 65536⟩
    (by decide) selected_cut_48387

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
