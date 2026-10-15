/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover343
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33027 : selected 9 ⟨850237, by decide⟩
    (prefixPartial 12 109905) = some ⟨12, 2, 0, 850237, 109905, 3605, 65536⟩ := by
  decide +kernel

theorem context_12_109905_850237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109905 ⟨850237, by decide⟩ :=
  accepted_of_selected 12 109905 ⟨850237, by decide⟩ ⟨12, 2, 0, 850237, 109905, 3605, 65536⟩
    (by decide) selected_cut_33027

theorem selected_cut_33028 : selected 9 ⟨850298, by decide⟩
    (prefixPartial 12 109906) = some ⟨12, 2, 0, 850298, 109906, 3821, 65536⟩ := by
  decide +kernel

theorem context_12_109906_850298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109906 ⟨850298, by decide⟩ :=
  accepted_of_selected 12 109906 ⟨850298, by decide⟩ ⟨12, 2, 0, 850298, 109906, 3821, 65536⟩
    (by decide) selected_cut_33028

theorem selected_cut_33029 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 439628) = some ⟨13, 1, 0, 3444, 439628, 1, 16384⟩ := by
  decide +kernel

theorem context_13_439628_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439628 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 439628 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 439628, 1, 16384⟩
    (by decide) selected_cut_33029

theorem selected_cut_33030 : selected 8 ⟨850323, by decide⟩
    (prefixPartial 13 439629) = some ⟨13, 2, 0, 850323, 439629, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_439629_850323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439629 ⟨850323, by decide⟩ :=
  accepted_of_selected 13 439629 ⟨850323, by decide⟩ ⟨13, 2, 0, 850323, 439629, 1813, 16384⟩
    (by decide) selected_cut_33030

theorem selected_cut_33031 : selected 8 ⟨850364, by decide⟩
    (prefixPartial 13 439630) = some ⟨13, 2, 0, 850364, 439630, 1589, 16384⟩ := by
  decide +kernel

theorem context_13_439630_850364 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439630 ⟨850364, by decide⟩ :=
  accepted_of_selected 13 439630 ⟨850364, by decide⟩ ⟨13, 2, 0, 850364, 439630, 1589, 16384⟩
    (by decide) selected_cut_33031

theorem selected_cut_33032 : selected 8 ⟨850373, by decide⟩
    (prefixPartial 13 439631) = some ⟨13, 2, 0, 850373, 439631, 873, 16384⟩ := by
  decide +kernel

theorem context_13_439631_850373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 439631 ⟨850373, by decide⟩ :=
  accepted_of_selected 13 439631 ⟨850373, by decide⟩ ⟨13, 2, 0, 850373, 439631, 873, 16384⟩
    (by decide) selected_cut_33032

theorem unmarked_context_12_109907_850374 : frontier 9 ⟨850374, by decide⟩
    (prefixCache 12 109907) (prefixPartial 12 109907) = false := by
  decide +kernel

theorem node_context_12_109907_850374 : EJMOriginalGlobalDAGData.nodes 9 ⟨850374, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨850323, by decide⟩,⟨850364, by decide⟩,⟨850373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_109907_850374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109907 ⟨850374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 109907
    ⟨850374, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨850323, by decide⟩,⟨850364, by decide⟩,⟨850373, by decide⟩]) unmarked_context_12_109907_850374 node_context_12_109907_850374
  intro a
  fin_cases a
  · exact context_13_439628_3444
  · exact context_13_439629_850323
  · exact context_13_439630_850364
  · exact context_13_439631_850373

theorem unmarked_context_11_27476_850375 : frontier 10 ⟨850375, by decide⟩
    (prefixCache 11 27476) (prefixPartial 11 27476) = false := by
  decide +kernel

theorem node_context_11_27476_850375 : EJMOriginalGlobalDAGData.nodes 10 ⟨850375, by decide⟩ =
    .split (coordinate 11) (![⟨850189, by decide⟩,⟨850237, by decide⟩,⟨850298, by decide⟩,⟨850374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27476_850375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27476 ⟨850375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27476
    ⟨850375, by decide⟩ (by decide) (![⟨850189, by decide⟩,⟨850237, by decide⟩,⟨850298, by decide⟩,⟨850374, by decide⟩]) unmarked_context_11_27476_850375 node_context_11_27476_850375
  intro a
  fin_cases a
  · exact context_12_109904_850189
  · exact context_12_109905_850237
  · exact context_12_109906_850298
  · exact context_12_109907_850374

theorem selected_cut_33033 : selected 9 ⟨850422, by decide⟩
    (prefixPartial 12 109908) = some ⟨12, 2, 0, 850422, 109908, 3341, 65536⟩ := by
  decide +kernel

theorem context_12_109908_850422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109908 ⟨850422, by decide⟩ :=
  accepted_of_selected 12 109908 ⟨850422, by decide⟩ ⟨12, 2, 0, 850422, 109908, 3341, 65536⟩
    (by decide) selected_cut_33033

theorem selected_cut_33034 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 109909) = some ⟨12, 1, 0, 439069, 109909, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109909_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109909 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 109909 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 109909, 1, 65536⟩
    (by decide) selected_cut_33034

theorem selected_cut_33035 : selected 9 ⟨850467, by decide⟩
    (prefixPartial 12 109910) = some ⟨12, 2, 0, 850467, 109910, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_109910_850467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109910 ⟨850467, by decide⟩ :=
  accepted_of_selected 12 109910 ⟨850467, by decide⟩ ⟨12, 2, 0, 850467, 109910, 3229, 65536⟩
    (by decide) selected_cut_33035

theorem selected_cut_33036 : selected 9 ⟨850535, by decide⟩
    (prefixPartial 12 109911) = some ⟨12, 2, 0, 850535, 109911, 3781, 65536⟩ := by
  decide +kernel

theorem context_12_109911_850535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109911 ⟨850535, by decide⟩ :=
  accepted_of_selected 12 109911 ⟨850535, by decide⟩ ⟨12, 2, 0, 850535, 109911, 3781, 65536⟩
    (by decide) selected_cut_33036

theorem unmarked_context_11_27477_850536 : frontier 10 ⟨850536, by decide⟩
    (prefixCache 11 27477) (prefixPartial 11 27477) = false := by
  decide +kernel

theorem node_context_11_27477_850536 : EJMOriginalGlobalDAGData.nodes 10 ⟨850536, by decide⟩ =
    .split (coordinate 11) (![⟨850422, by decide⟩,⟨439069, by decide⟩,⟨850467, by decide⟩,⟨850535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27477_850536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27477 ⟨850536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27477
    ⟨850536, by decide⟩ (by decide) (![⟨850422, by decide⟩,⟨439069, by decide⟩,⟨850467, by decide⟩,⟨850535, by decide⟩]) unmarked_context_11_27477_850536 node_context_11_27477_850536
  intro a
  fin_cases a
  · exact context_12_109908_850422
  · exact context_12_109909_439069
  · exact context_12_109910_850467
  · exact context_12_109911_850535

theorem selected_cut_33037 : selected 9 ⟨850583, by decide⟩
    (prefixPartial 12 109912) = some ⟨12, 2, 0, 850583, 109912, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_109912_850583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109912 ⟨850583, by decide⟩ :=
  accepted_of_selected 12 109912 ⟨850583, by decide⟩ ⟨12, 2, 0, 850583, 109912, 3493, 65536⟩
    (by decide) selected_cut_33037

theorem selected_cut_33038 : selected 9 ⟨850627, by decide⟩
    (prefixPartial 12 109913) = some ⟨12, 2, 0, 850627, 109913, 3129, 65536⟩ := by
  decide +kernel

theorem context_12_109913_850627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109913 ⟨850627, by decide⟩ :=
  accepted_of_selected 12 109913 ⟨850627, by decide⟩ ⟨12, 2, 0, 850627, 109913, 3129, 65536⟩
    (by decide) selected_cut_33038

theorem selected_cut_33039 : selected 9 ⟨850667, by decide⟩
    (prefixPartial 12 109914) = some ⟨12, 2, 0, 850667, 109914, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_109914_850667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109914 ⟨850667, by decide⟩ :=
  accepted_of_selected 12 109914 ⟨850667, by decide⟩ ⟨12, 2, 0, 850667, 109914, 3037, 65536⟩
    (by decide) selected_cut_33039

theorem selected_cut_33040 : selected 9 ⟨850722, by decide⟩
    (prefixPartial 12 109915) = some ⟨12, 2, 0, 850722, 109915, 3665, 65536⟩ := by
  decide +kernel

theorem context_12_109915_850722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109915 ⟨850722, by decide⟩ :=
  accepted_of_selected 12 109915 ⟨850722, by decide⟩ ⟨12, 2, 0, 850722, 109915, 3665, 65536⟩
    (by decide) selected_cut_33040

theorem unmarked_context_11_27478_850723 : frontier 10 ⟨850723, by decide⟩
    (prefixCache 11 27478) (prefixPartial 11 27478) = false := by
  decide +kernel

theorem node_context_11_27478_850723 : EJMOriginalGlobalDAGData.nodes 10 ⟨850723, by decide⟩ =
    .split (coordinate 11) (![⟨850583, by decide⟩,⟨850627, by decide⟩,⟨850667, by decide⟩,⟨850722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27478_850723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27478 ⟨850723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27478
    ⟨850723, by decide⟩ (by decide) (![⟨850583, by decide⟩,⟨850627, by decide⟩,⟨850667, by decide⟩,⟨850722, by decide⟩]) unmarked_context_11_27478_850723 node_context_11_27478_850723
  intro a
  fin_cases a
  · exact context_12_109912_850583
  · exact context_12_109913_850627
  · exact context_12_109914_850667
  · exact context_12_109915_850722

theorem selected_cut_33041 : selected 9 ⟨850759, by decide⟩
    (prefixPartial 12 109916) = some ⟨12, 2, 0, 850759, 109916, 3605, 65536⟩ := by
  decide +kernel

theorem context_12_109916_850759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109916 ⟨850759, by decide⟩ :=
  accepted_of_selected 12 109916 ⟨850759, by decide⟩ ⟨12, 2, 0, 850759, 109916, 3605, 65536⟩
    (by decide) selected_cut_33041

theorem selected_cut_33042 : selected 9 ⟨850803, by decide⟩
    (prefixPartial 12 109917) = some ⟨12, 2, 0, 850803, 109917, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_109917_850803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109917 ⟨850803, by decide⟩ :=
  accepted_of_selected 12 109917 ⟨850803, by decide⟩ ⟨12, 2, 0, 850803, 109917, 3261, 65536⟩
    (by decide) selected_cut_33042

theorem selected_cut_33043 : selected 9 ⟨850850, by decide⟩
    (prefixPartial 12 109918) = some ⟨12, 2, 0, 850850, 109918, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_109918_850850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109918 ⟨850850, by decide⟩ :=
  accepted_of_selected 12 109918 ⟨850850, by decide⟩ ⟨12, 2, 0, 850850, 109918, 3425, 65536⟩
    (by decide) selected_cut_33043

theorem selected_cut_33044 : selected 9 ⟨850906, by decide⟩
    (prefixPartial 12 109919) = some ⟨12, 2, 0, 850906, 109919, 3705, 65536⟩ := by
  decide +kernel

theorem context_12_109919_850906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109919 ⟨850906, by decide⟩ :=
  accepted_of_selected 12 109919 ⟨850906, by decide⟩ ⟨12, 2, 0, 850906, 109919, 3705, 65536⟩
    (by decide) selected_cut_33044

theorem unmarked_context_11_27479_850907 : frontier 10 ⟨850907, by decide⟩
    (prefixCache 11 27479) (prefixPartial 11 27479) = false := by
  decide +kernel

theorem node_context_11_27479_850907 : EJMOriginalGlobalDAGData.nodes 10 ⟨850907, by decide⟩ =
    .split (coordinate 11) (![⟨850759, by decide⟩,⟨850803, by decide⟩,⟨850850, by decide⟩,⟨850906, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27479_850907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27479 ⟨850907, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27479
    ⟨850907, by decide⟩ (by decide) (![⟨850759, by decide⟩,⟨850803, by decide⟩,⟨850850, by decide⟩,⟨850906, by decide⟩]) unmarked_context_11_27479_850907 node_context_11_27479_850907
  intro a
  fin_cases a
  · exact context_12_109916_850759
  · exact context_12_109917_850803
  · exact context_12_109918_850850
  · exact context_12_109919_850906

theorem unmarked_context_10_6869_850908 : frontier 11 ⟨850908, by decide⟩
    (prefixCache 10 6869) (prefixPartial 10 6869) = false := by
  decide +kernel

theorem node_context_10_6869_850908 : EJMOriginalGlobalDAGData.nodes 11 ⟨850908, by decide⟩ =
    .split (coordinate 10) (![⟨850375, by decide⟩,⟨850536, by decide⟩,⟨850723, by decide⟩,⟨850907, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6869_850908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6869 ⟨850908, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6869
    ⟨850908, by decide⟩ (by decide) (![⟨850375, by decide⟩,⟨850536, by decide⟩,⟨850723, by decide⟩,⟨850907, by decide⟩]) unmarked_context_10_6869_850908 node_context_10_6869_850908
  intro a
  fin_cases a
  · exact context_11_27476_850375
  · exact context_11_27477_850536
  · exact context_11_27478_850723
  · exact context_11_27479_850907

theorem selected_cut_33045 : selected 9 ⟨850958, by decide⟩
    (prefixPartial 12 109920) = some ⟨12, 2, 0, 850958, 109920, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_109920_850958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109920 ⟨850958, by decide⟩ :=
  accepted_of_selected 12 109920 ⟨850958, by decide⟩ ⟨12, 2, 0, 850958, 109920, 3481, 65536⟩
    (by decide) selected_cut_33045

theorem selected_cut_33046 : selected 9 ⟨851010, by decide⟩
    (prefixPartial 12 109921) = some ⟨12, 2, 0, 851010, 109921, 3225, 65536⟩ := by
  decide +kernel

theorem context_12_109921_851010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109921 ⟨851010, by decide⟩ :=
  accepted_of_selected 12 109921 ⟨851010, by decide⟩ ⟨12, 2, 0, 851010, 109921, 3225, 65536⟩
    (by decide) selected_cut_33046

theorem selected_cut_33047 : selected 9 ⟨851060, by decide⟩
    (prefixPartial 12 109922) = some ⟨12, 2, 0, 851060, 109922, 3397, 65536⟩ := by
  decide +kernel

theorem context_12_109922_851060 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109922 ⟨851060, by decide⟩ :=
  accepted_of_selected 12 109922 ⟨851060, by decide⟩ ⟨12, 2, 0, 851060, 109922, 3397, 65536⟩
    (by decide) selected_cut_33047

theorem selected_cut_33048 : selected 9 ⟨851153, by decide⟩
    (prefixPartial 12 109923) = some ⟨12, 2, 0, 851153, 109923, 3637, 65536⟩ := by
  decide +kernel

theorem context_12_109923_851153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109923 ⟨851153, by decide⟩ :=
  accepted_of_selected 12 109923 ⟨851153, by decide⟩ ⟨12, 2, 0, 851153, 109923, 3637, 65536⟩
    (by decide) selected_cut_33048

theorem unmarked_context_11_27480_851154 : frontier 10 ⟨851154, by decide⟩
    (prefixCache 11 27480) (prefixPartial 11 27480) = false := by
  decide +kernel

theorem node_context_11_27480_851154 : EJMOriginalGlobalDAGData.nodes 10 ⟨851154, by decide⟩ =
    .split (coordinate 11) (![⟨850958, by decide⟩,⟨851010, by decide⟩,⟨851060, by decide⟩,⟨851153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27480_851154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27480 ⟨851154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27480
    ⟨851154, by decide⟩ (by decide) (![⟨850958, by decide⟩,⟨851010, by decide⟩,⟨851060, by decide⟩,⟨851153, by decide⟩]) unmarked_context_11_27480_851154 node_context_11_27480_851154
  intro a
  fin_cases a
  · exact context_12_109920_850958
  · exact context_12_109921_851010
  · exact context_12_109922_851060
  · exact context_12_109923_851153

theorem selected_cut_33049 : selected 9 ⟨851194, by decide⟩
    (prefixPartial 12 109924) = some ⟨12, 2, 0, 851194, 109924, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_109924_851194 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109924 ⟨851194, by decide⟩ :=
  accepted_of_selected 12 109924 ⟨851194, by decide⟩ ⟨12, 2, 0, 851194, 109924, 3229, 65536⟩
    (by decide) selected_cut_33049

theorem selected_cut_33050 : selected 9 ⟨851195, by decide⟩
    (prefixPartial 12 109925) = some ⟨12, 1, 0, 851195, 109925, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109925_851195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109925 ⟨851195, by decide⟩ :=
  accepted_of_selected 12 109925 ⟨851195, by decide⟩ ⟨12, 1, 0, 851195, 109925, 1, 65536⟩
    (by decide) selected_cut_33050

theorem selected_cut_33051 : selected 9 ⟨851240, by decide⟩
    (prefixPartial 12 109926) = some ⟨12, 2, 0, 851240, 109926, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_109926_851240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109926 ⟨851240, by decide⟩ :=
  accepted_of_selected 12 109926 ⟨851240, by decide⟩ ⟨12, 2, 0, 851240, 109926, 3037, 65536⟩
    (by decide) selected_cut_33051

theorem selected_cut_33052 : selected 9 ⟨851318, by decide⟩
    (prefixPartial 12 109927) = some ⟨12, 2, 0, 851318, 109927, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_109927_851318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109927 ⟨851318, by decide⟩ :=
  accepted_of_selected 12 109927 ⟨851318, by decide⟩ ⟨12, 2, 0, 851318, 109927, 3481, 65536⟩
    (by decide) selected_cut_33052

theorem unmarked_context_11_27481_851319 : frontier 10 ⟨851319, by decide⟩
    (prefixCache 11 27481) (prefixPartial 11 27481) = false := by
  decide +kernel

theorem node_context_11_27481_851319 : EJMOriginalGlobalDAGData.nodes 10 ⟨851319, by decide⟩ =
    .split (coordinate 11) (![⟨851194, by decide⟩,⟨851195, by decide⟩,⟨851240, by decide⟩,⟨851318, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27481_851319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27481 ⟨851319, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27481
    ⟨851319, by decide⟩ (by decide) (![⟨851194, by decide⟩,⟨851195, by decide⟩,⟨851240, by decide⟩,⟨851318, by decide⟩]) unmarked_context_11_27481_851319 node_context_11_27481_851319
  intro a
  fin_cases a
  · exact context_12_109924_851194
  · exact context_12_109925_851195
  · exact context_12_109926_851240
  · exact context_12_109927_851318

theorem selected_cut_33053 : selected 9 ⟨851363, by decide⟩
    (prefixPartial 12 109928) = some ⟨12, 2, 0, 851363, 109928, 3141, 65536⟩ := by
  decide +kernel

theorem context_12_109928_851363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109928 ⟨851363, by decide⟩ :=
  accepted_of_selected 12 109928 ⟨851363, by decide⟩ ⟨12, 2, 0, 851363, 109928, 3141, 65536⟩
    (by decide) selected_cut_33053

theorem selected_cut_33054 : selected 9 ⟨851399, by decide⟩
    (prefixPartial 12 109929) = some ⟨12, 2, 0, 851399, 109929, 2793, 65536⟩ := by
  decide +kernel

theorem context_12_109929_851399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109929 ⟨851399, by decide⟩ :=
  accepted_of_selected 12 109929 ⟨851399, by decide⟩ ⟨12, 2, 0, 851399, 109929, 2793, 65536⟩
    (by decide) selected_cut_33054

theorem selected_cut_33055 : selected 9 ⟨851435, by decide⟩
    (prefixPartial 12 109930) = some ⟨12, 2, 0, 851435, 109930, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_109930_851435 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109930 ⟨851435, by decide⟩ :=
  accepted_of_selected 12 109930 ⟨851435, by decide⟩ ⟨12, 2, 0, 851435, 109930, 2717, 65536⟩
    (by decide) selected_cut_33055

theorem selected_cut_33056 : selected 9 ⟨851503, by decide⟩
    (prefixPartial 12 109931) = some ⟨12, 2, 0, 851503, 109931, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_109931_851503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109931 ⟨851503, by decide⟩ :=
  accepted_of_selected 12 109931 ⟨851503, by decide⟩ ⟨12, 2, 0, 851503, 109931, 3037, 65536⟩
    (by decide) selected_cut_33056

theorem unmarked_context_11_27482_851504 : frontier 10 ⟨851504, by decide⟩
    (prefixCache 11 27482) (prefixPartial 11 27482) = false := by
  decide +kernel

theorem node_context_11_27482_851504 : EJMOriginalGlobalDAGData.nodes 10 ⟨851504, by decide⟩ =
    .split (coordinate 11) (![⟨851363, by decide⟩,⟨851399, by decide⟩,⟨851435, by decide⟩,⟨851503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27482_851504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27482 ⟨851504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27482
    ⟨851504, by decide⟩ (by decide) (![⟨851363, by decide⟩,⟨851399, by decide⟩,⟨851435, by decide⟩,⟨851503, by decide⟩]) unmarked_context_11_27482_851504 node_context_11_27482_851504
  intro a
  fin_cases a
  · exact context_12_109928_851363
  · exact context_12_109929_851399
  · exact context_12_109930_851435
  · exact context_12_109931_851503

theorem selected_cut_33057 : selected 9 ⟨851547, by decide⟩
    (prefixPartial 12 109932) = some ⟨12, 2, 0, 851547, 109932, 3405, 65536⟩ := by
  decide +kernel

theorem context_12_109932_851547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109932 ⟨851547, by decide⟩ :=
  accepted_of_selected 12 109932 ⟨851547, by decide⟩ ⟨12, 2, 0, 851547, 109932, 3405, 65536⟩
    (by decide) selected_cut_33057

theorem selected_cut_33058 : selected 9 ⟨851587, by decide⟩
    (prefixPartial 12 109933) = some ⟨12, 2, 0, 851587, 109933, 3045, 65536⟩ := by
  decide +kernel

theorem context_12_109933_851587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109933 ⟨851587, by decide⟩ :=
  accepted_of_selected 12 109933 ⟨851587, by decide⟩ ⟨12, 2, 0, 851587, 109933, 3045, 65536⟩
    (by decide) selected_cut_33058

theorem selected_cut_33059 : selected 9 ⟨851624, by decide⟩
    (prefixPartial 12 109934) = some ⟨12, 2, 0, 851624, 109934, 2989, 65536⟩ := by
  decide +kernel

theorem context_12_109934_851624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109934 ⟨851624, by decide⟩ :=
  accepted_of_selected 12 109934 ⟨851624, by decide⟩ ⟨12, 2, 0, 851624, 109934, 2989, 65536⟩
    (by decide) selected_cut_33059

theorem selected_cut_33060 : selected 9 ⟨851675, by decide⟩
    (prefixPartial 12 109935) = some ⟨12, 2, 0, 851675, 109935, 3293, 65536⟩ := by
  decide +kernel

theorem context_12_109935_851675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109935 ⟨851675, by decide⟩ :=
  accepted_of_selected 12 109935 ⟨851675, by decide⟩ ⟨12, 2, 0, 851675, 109935, 3293, 65536⟩
    (by decide) selected_cut_33060

theorem unmarked_context_11_27483_851676 : frontier 10 ⟨851676, by decide⟩
    (prefixCache 11 27483) (prefixPartial 11 27483) = false := by
  decide +kernel

theorem node_context_11_27483_851676 : EJMOriginalGlobalDAGData.nodes 10 ⟨851676, by decide⟩ =
    .split (coordinate 11) (![⟨851547, by decide⟩,⟨851587, by decide⟩,⟨851624, by decide⟩,⟨851675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27483_851676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27483 ⟨851676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27483
    ⟨851676, by decide⟩ (by decide) (![⟨851547, by decide⟩,⟨851587, by decide⟩,⟨851624, by decide⟩,⟨851675, by decide⟩]) unmarked_context_11_27483_851676 node_context_11_27483_851676
  intro a
  fin_cases a
  · exact context_12_109932_851547
  · exact context_12_109933_851587
  · exact context_12_109934_851624
  · exact context_12_109935_851675

theorem unmarked_context_10_6870_851677 : frontier 11 ⟨851677, by decide⟩
    (prefixCache 10 6870) (prefixPartial 10 6870) = false := by
  decide +kernel

theorem node_context_10_6870_851677 : EJMOriginalGlobalDAGData.nodes 11 ⟨851677, by decide⟩ =
    .split (coordinate 10) (![⟨851154, by decide⟩,⟨851319, by decide⟩,⟨851504, by decide⟩,⟨851676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6870_851677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6870 ⟨851677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6870
    ⟨851677, by decide⟩ (by decide) (![⟨851154, by decide⟩,⟨851319, by decide⟩,⟨851504, by decide⟩,⟨851676, by decide⟩]) unmarked_context_10_6870_851677 node_context_10_6870_851677
  intro a
  fin_cases a
  · exact context_11_27480_851154
  · exact context_11_27481_851319
  · exact context_11_27482_851504
  · exact context_11_27483_851676

theorem selected_cut_33061 : selected 9 ⟨851735, by decide⟩
    (prefixPartial 12 109936) = some ⟨12, 2, 0, 851735, 109936, 2509, 65536⟩ := by
  decide +kernel

theorem context_12_109936_851735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109936 ⟨851735, by decide⟩ :=
  accepted_of_selected 12 109936 ⟨851735, by decide⟩ ⟨12, 2, 0, 851735, 109936, 2509, 65536⟩
    (by decide) selected_cut_33061

theorem selected_cut_33062 : selected 9 ⟨851774, by decide⟩
    (prefixPartial 12 109937) = some ⟨12, 2, 0, 851774, 109937, 2385, 65536⟩ := by
  decide +kernel

theorem context_12_109937_851774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109937 ⟨851774, by decide⟩ :=
  accepted_of_selected 12 109937 ⟨851774, by decide⟩ ⟨12, 2, 0, 851774, 109937, 2385, 65536⟩
    (by decide) selected_cut_33062

theorem selected_cut_33063 : selected 9 ⟨851817, by decide⟩
    (prefixPartial 12 109938) = some ⟨12, 2, 0, 851817, 109938, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_109938_851817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109938 ⟨851817, by decide⟩ :=
  accepted_of_selected 12 109938 ⟨851817, by decide⟩ ⟨12, 2, 0, 851817, 109938, 2433, 65536⟩
    (by decide) selected_cut_33063

theorem selected_cut_33064 : selected 9 ⟨851870, by decide⟩
    (prefixPartial 12 109939) = some ⟨12, 2, 0, 851870, 109939, 2581, 65536⟩ := by
  decide +kernel

theorem context_12_109939_851870 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109939 ⟨851870, by decide⟩ :=
  accepted_of_selected 12 109939 ⟨851870, by decide⟩ ⟨12, 2, 0, 851870, 109939, 2581, 65536⟩
    (by decide) selected_cut_33064

theorem unmarked_context_11_27484_851871 : frontier 10 ⟨851871, by decide⟩
    (prefixCache 11 27484) (prefixPartial 11 27484) = false := by
  decide +kernel

theorem node_context_11_27484_851871 : EJMOriginalGlobalDAGData.nodes 10 ⟨851871, by decide⟩ =
    .split (coordinate 11) (![⟨851735, by decide⟩,⟨851774, by decide⟩,⟨851817, by decide⟩,⟨851870, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27484_851871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27484 ⟨851871, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27484
    ⟨851871, by decide⟩ (by decide) (![⟨851735, by decide⟩,⟨851774, by decide⟩,⟨851817, by decide⟩,⟨851870, by decide⟩]) unmarked_context_11_27484_851871 node_context_11_27484_851871
  intro a
  fin_cases a
  · exact context_12_109936_851735
  · exact context_12_109937_851774
  · exact context_12_109938_851817
  · exact context_12_109939_851870

theorem selected_cut_33065 : selected 9 ⟨851907, by decide⟩
    (prefixPartial 12 109940) = some ⟨12, 2, 0, 851907, 109940, 2205, 65536⟩ := by
  decide +kernel

theorem context_12_109940_851907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109940 ⟨851907, by decide⟩ :=
  accepted_of_selected 12 109940 ⟨851907, by decide⟩ ⟨12, 2, 0, 851907, 109940, 2205, 65536⟩
    (by decide) selected_cut_33065

theorem selected_cut_33066 : selected 9 ⟨689956, by decide⟩
    (prefixPartial 12 109941) = some ⟨12, 1, 0, 689956, 109941, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109941_689956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109941 ⟨689956, by decide⟩ :=
  accepted_of_selected 12 109941 ⟨689956, by decide⟩ ⟨12, 1, 0, 689956, 109941, 1, 65536⟩
    (by decide) selected_cut_33066

theorem selected_cut_33067 : selected 9 ⟨851940, by decide⟩
    (prefixPartial 12 109942) = some ⟨12, 2, 0, 851940, 109942, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_109942_851940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109942 ⟨851940, by decide⟩ :=
  accepted_of_selected 12 109942 ⟨851940, by decide⟩ ⟨12, 2, 0, 851940, 109942, 1997, 65536⟩
    (by decide) selected_cut_33067

theorem selected_cut_33068 : selected 9 ⟨852002, by decide⟩
    (prefixPartial 12 109943) = some ⟨12, 2, 0, 852002, 109943, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_109943_852002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109943 ⟨852002, by decide⟩ :=
  accepted_of_selected 12 109943 ⟨852002, by decide⟩ ⟨12, 2, 0, 852002, 109943, 2381, 65536⟩
    (by decide) selected_cut_33068

theorem unmarked_context_11_27485_852003 : frontier 10 ⟨852003, by decide⟩
    (prefixCache 11 27485) (prefixPartial 11 27485) = false := by
  decide +kernel

theorem node_context_11_27485_852003 : EJMOriginalGlobalDAGData.nodes 10 ⟨852003, by decide⟩ =
    .split (coordinate 11) (![⟨851907, by decide⟩,⟨689956, by decide⟩,⟨851940, by decide⟩,⟨852002, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27485_852003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27485 ⟨852003, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27485
    ⟨852003, by decide⟩ (by decide) (![⟨851907, by decide⟩,⟨689956, by decide⟩,⟨851940, by decide⟩,⟨852002, by decide⟩]) unmarked_context_11_27485_852003 node_context_11_27485_852003
  intro a
  fin_cases a
  · exact context_12_109940_851907
  · exact context_12_109941_689956
  · exact context_12_109942_851940
  · exact context_12_109943_852002

theorem selected_cut_33069 : selected 9 ⟨852032, by decide⟩
    (prefixPartial 12 109944) = some ⟨12, 2, 0, 852032, 109944, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_109944_852032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109944 ⟨852032, by decide⟩ :=
  accepted_of_selected 12 109944 ⟨852032, by decide⟩ ⟨12, 2, 0, 852032, 109944, 2221, 65536⟩
    (by decide) selected_cut_33069

theorem selected_cut_33070 : selected 9 ⟨852056, by decide⟩
    (prefixPartial 12 109945) = some ⟨12, 2, 0, 852056, 109945, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_109945_852056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109945 ⟨852056, by decide⟩ :=
  accepted_of_selected 12 109945 ⟨852056, by decide⟩ ⟨12, 2, 0, 852056, 109945, 2061, 65536⟩
    (by decide) selected_cut_33070

theorem selected_cut_33071 : selected 9 ⟨852077, by decide⟩
    (prefixPartial 12 109946) = some ⟨12, 2, 0, 852077, 109946, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_109946_852077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109946 ⟨852077, by decide⟩ :=
  accepted_of_selected 12 109946 ⟨852077, by decide⟩ ⟨12, 2, 0, 852077, 109946, 1821, 65536⟩
    (by decide) selected_cut_33071

theorem selected_cut_33072 : selected 9 ⟨852116, by decide⟩
    (prefixPartial 12 109947) = some ⟨12, 2, 0, 852116, 109947, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_109947_852116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109947 ⟨852116, by decide⟩ :=
  accepted_of_selected 12 109947 ⟨852116, by decide⟩ ⟨12, 2, 0, 852116, 109947, 2137, 65536⟩
    (by decide) selected_cut_33072

theorem unmarked_context_11_27486_852117 : frontier 10 ⟨852117, by decide⟩
    (prefixCache 11 27486) (prefixPartial 11 27486) = false := by
  decide +kernel

theorem node_context_11_27486_852117 : EJMOriginalGlobalDAGData.nodes 10 ⟨852117, by decide⟩ =
    .split (coordinate 11) (![⟨852032, by decide⟩,⟨852056, by decide⟩,⟨852077, by decide⟩,⟨852116, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27486_852117 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27486 ⟨852117, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27486
    ⟨852117, by decide⟩ (by decide) (![⟨852032, by decide⟩,⟨852056, by decide⟩,⟨852077, by decide⟩,⟨852116, by decide⟩]) unmarked_context_11_27486_852117 node_context_11_27486_852117
  intro a
  fin_cases a
  · exact context_12_109944_852032
  · exact context_12_109945_852056
  · exact context_12_109946_852077
  · exact context_12_109947_852116

theorem selected_cut_33073 : selected 10 ⟨852168, by decide⟩
    (prefixPartial 11 27487) = some ⟨11, 2, 0, 852168, 27487, 881, 262144⟩ := by
  decide +kernel

theorem context_11_27487_852168 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27487 ⟨852168, by decide⟩ :=
  accepted_of_selected 11 27487 ⟨852168, by decide⟩ ⟨11, 2, 0, 852168, 27487, 881, 262144⟩
    (by decide) selected_cut_33073

theorem unmarked_context_10_6871_852169 : frontier 11 ⟨852169, by decide⟩
    (prefixCache 10 6871) (prefixPartial 10 6871) = false := by
  decide +kernel

theorem node_context_10_6871_852169 : EJMOriginalGlobalDAGData.nodes 11 ⟨852169, by decide⟩ =
    .split (coordinate 10) (![⟨851871, by decide⟩,⟨852003, by decide⟩,⟨852117, by decide⟩,⟨852168, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6871_852169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6871 ⟨852169, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6871
    ⟨852169, by decide⟩ (by decide) (![⟨851871, by decide⟩,⟨852003, by decide⟩,⟨852117, by decide⟩,⟨852168, by decide⟩]) unmarked_context_10_6871_852169 node_context_10_6871_852169
  intro a
  fin_cases a
  · exact context_11_27484_851871
  · exact context_11_27485_852003
  · exact context_11_27486_852117
  · exact context_11_27487_852168

theorem unmarked_context_9_1717_852170 : frontier 12 ⟨852170, by decide⟩
    (prefixCache 9 1717) (prefixPartial 9 1717) = false := by
  decide +kernel

theorem node_context_9_1717_852170 : EJMOriginalGlobalDAGData.nodes 12 ⟨852170, by decide⟩ =
    .split (coordinate 9) (![⟨850138, by decide⟩,⟨850908, by decide⟩,⟨851677, by decide⟩,⟨852169, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1717_852170 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1717 ⟨852170, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1717
    ⟨852170, by decide⟩ (by decide) (![⟨850138, by decide⟩,⟨850908, by decide⟩,⟨851677, by decide⟩,⟨852169, by decide⟩]) unmarked_context_9_1717_852170 node_context_9_1717_852170
  intro a
  fin_cases a
  · exact context_10_6868_850138
  · exact context_10_6869_850908
  · exact context_10_6870_851677
  · exact context_10_6871_852169

theorem selected_cut_33074 : selected 9 ⟨852202, by decide⟩
    (prefixPartial 12 109952) = some ⟨12, 2, 0, 852202, 109952, 2273, 65536⟩ := by
  decide +kernel

theorem context_12_109952_852202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109952 ⟨852202, by decide⟩ :=
  accepted_of_selected 12 109952 ⟨852202, by decide⟩ ⟨12, 2, 0, 852202, 109952, 2273, 65536⟩
    (by decide) selected_cut_33074

theorem selected_cut_33075 : selected 9 ⟨852227, by decide⟩
    (prefixPartial 12 109953) = some ⟨12, 2, 0, 852227, 109953, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_109953_852227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109953 ⟨852227, by decide⟩ :=
  accepted_of_selected 12 109953 ⟨852227, by decide⟩ ⟨12, 2, 0, 852227, 109953, 2229, 65536⟩
    (by decide) selected_cut_33075

theorem selected_cut_33076 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 109954) = some ⟨12, 1, 0, 813440, 109954, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109954_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109954 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 109954 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 109954, 1, 65536⟩
    (by decide) selected_cut_33076

theorem selected_cut_33077 : selected 9 ⟨852256, by decide⟩
    (prefixPartial 12 109955) = some ⟨12, 2, 0, 852256, 109955, 2433, 65536⟩ := by
  decide +kernel

theorem context_12_109955_852256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109955 ⟨852256, by decide⟩ :=
  accepted_of_selected 12 109955 ⟨852256, by decide⟩ ⟨12, 2, 0, 852256, 109955, 2433, 65536⟩
    (by decide) selected_cut_33077

theorem unmarked_context_11_27488_852257 : frontier 10 ⟨852257, by decide⟩
    (prefixCache 11 27488) (prefixPartial 11 27488) = false := by
  decide +kernel

theorem node_context_11_27488_852257 : EJMOriginalGlobalDAGData.nodes 10 ⟨852257, by decide⟩ =
    .split (coordinate 11) (![⟨852202, by decide⟩,⟨852227, by decide⟩,⟨813440, by decide⟩,⟨852256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27488_852257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27488 ⟨852257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27488
    ⟨852257, by decide⟩ (by decide) (![⟨852202, by decide⟩,⟨852227, by decide⟩,⟨813440, by decide⟩,⟨852256, by decide⟩]) unmarked_context_11_27488_852257 node_context_11_27488_852257
  intro a
  fin_cases a
  · exact context_12_109952_852202
  · exact context_12_109953_852227
  · exact context_12_109954_813440
  · exact context_12_109955_852256

theorem selected_cut_33078 : selected 9 ⟨852299, by decide⟩
    (prefixPartial 12 109956) = some ⟨12, 2, 0, 852299, 109956, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_109956_852299 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109956 ⟨852299, by decide⟩ :=
  accepted_of_selected 12 109956 ⟨852299, by decide⟩ ⟨12, 2, 0, 852299, 109956, 2057, 65536⟩
    (by decide) selected_cut_33078

theorem selected_cut_33079 : selected 9 ⟨721771, by decide⟩
    (prefixPartial 12 109957) = some ⟨12, 1, 0, 721771, 109957, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109957_721771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109957 ⟨721771, by decide⟩ :=
  accepted_of_selected 12 109957 ⟨721771, by decide⟩ ⟨12, 1, 0, 721771, 109957, 1, 65536⟩
    (by decide) selected_cut_33079

theorem selected_cut_33080 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 109958) = some ⟨12, 1, 0, 813440, 109958, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109958_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109958 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 109958 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 109958, 1, 65536⟩
    (by decide) selected_cut_33080

theorem selected_cut_33081 : selected 9 ⟨852344, by decide⟩
    (prefixPartial 12 109959) = some ⟨12, 2, 0, 852344, 109959, 2261, 65536⟩ := by
  decide +kernel

theorem context_12_109959_852344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109959 ⟨852344, by decide⟩ :=
  accepted_of_selected 12 109959 ⟨852344, by decide⟩ ⟨12, 2, 0, 852344, 109959, 2261, 65536⟩
    (by decide) selected_cut_33081

theorem unmarked_context_11_27489_852345 : frontier 10 ⟨852345, by decide⟩
    (prefixCache 11 27489) (prefixPartial 11 27489) = false := by
  decide +kernel

theorem node_context_11_27489_852345 : EJMOriginalGlobalDAGData.nodes 10 ⟨852345, by decide⟩ =
    .split (coordinate 11) (![⟨852299, by decide⟩,⟨721771, by decide⟩,⟨813440, by decide⟩,⟨852344, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27489_852345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27489 ⟨852345, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27489
    ⟨852345, by decide⟩ (by decide) (![⟨852299, by decide⟩,⟨721771, by decide⟩,⟨813440, by decide⟩,⟨852344, by decide⟩]) unmarked_context_11_27489_852345 node_context_11_27489_852345
  intro a
  fin_cases a
  · exact context_12_109956_852299
  · exact context_12_109957_721771
  · exact context_12_109958_813440
  · exact context_12_109959_852344

theorem selected_cut_33082 : selected 9 ⟨852395, by decide⟩
    (prefixPartial 12 109960) = some ⟨12, 2, 0, 852395, 109960, 2241, 65536⟩ := by
  decide +kernel

theorem context_12_109960_852395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109960 ⟨852395, by decide⟩ :=
  accepted_of_selected 12 109960 ⟨852395, by decide⟩ ⟨12, 2, 0, 852395, 109960, 2241, 65536⟩
    (by decide) selected_cut_33082

theorem selected_cut_33083 : selected 9 ⟨852429, by decide⟩
    (prefixPartial 12 109961) = some ⟨12, 2, 0, 852429, 109961, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_109961_852429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109961 ⟨852429, by decide⟩ :=
  accepted_of_selected 12 109961 ⟨852429, by decide⟩ ⟨12, 2, 0, 852429, 109961, 2125, 65536⟩
    (by decide) selected_cut_33083

theorem selected_cut_33084 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 109962) = some ⟨12, 1, 0, 813440, 109962, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109962_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109962 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 109962 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 109962, 1, 65536⟩
    (by decide) selected_cut_33084

theorem selected_cut_33085 : selected 9 ⟨852475, by decide⟩
    (prefixPartial 12 109963) = some ⟨12, 2, 0, 852475, 109963, 2249, 65536⟩ := by
  decide +kernel

theorem context_12_109963_852475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109963 ⟨852475, by decide⟩ :=
  accepted_of_selected 12 109963 ⟨852475, by decide⟩ ⟨12, 2, 0, 852475, 109963, 2249, 65536⟩
    (by decide) selected_cut_33085

theorem unmarked_context_11_27490_852476 : frontier 10 ⟨852476, by decide⟩
    (prefixCache 11 27490) (prefixPartial 11 27490) = false := by
  decide +kernel

theorem node_context_11_27490_852476 : EJMOriginalGlobalDAGData.nodes 10 ⟨852476, by decide⟩ =
    .split (coordinate 11) (![⟨852395, by decide⟩,⟨852429, by decide⟩,⟨813440, by decide⟩,⟨852475, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27490_852476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27490 ⟨852476, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27490
    ⟨852476, by decide⟩ (by decide) (![⟨852395, by decide⟩,⟨852429, by decide⟩,⟨813440, by decide⟩,⟨852475, by decide⟩]) unmarked_context_11_27490_852476 node_context_11_27490_852476
  intro a
  fin_cases a
  · exact context_12_109960_852395
  · exact context_12_109961_852429
  · exact context_12_109962_813440
  · exact context_12_109963_852475

theorem selected_cut_33086 : selected 9 ⟨852502, by decide⟩
    (prefixPartial 12 109964) = some ⟨12, 2, 0, 852502, 109964, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_109964_852502 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109964 ⟨852502, by decide⟩ :=
  accepted_of_selected 12 109964 ⟨852502, by decide⟩ ⟨12, 2, 0, 852502, 109964, 2105, 65536⟩
    (by decide) selected_cut_33086

theorem selected_cut_33087 : selected 9 ⟨852527, by decide⟩
    (prefixPartial 12 109965) = some ⟨12, 2, 0, 852527, 109965, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_109965_852527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109965 ⟨852527, by decide⟩ :=
  accepted_of_selected 12 109965 ⟨852527, by decide⟩ ⟨12, 2, 0, 852527, 109965, 2033, 65536⟩
    (by decide) selected_cut_33087

theorem selected_cut_33088 : selected 9 ⟨813440, by decide⟩
    (prefixPartial 12 109966) = some ⟨12, 1, 0, 813440, 109966, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109966_813440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109966 ⟨813440, by decide⟩ :=
  accepted_of_selected 12 109966 ⟨813440, by decide⟩ ⟨12, 1, 0, 813440, 109966, 1, 65536⟩
    (by decide) selected_cut_33088

theorem selected_cut_33089 : selected 9 ⟨852553, by decide⟩
    (prefixPartial 12 109967) = some ⟨12, 2, 0, 852553, 109967, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_109967_852553 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109967 ⟨852553, by decide⟩ :=
  accepted_of_selected 12 109967 ⟨852553, by decide⟩ ⟨12, 2, 0, 852553, 109967, 2149, 65536⟩
    (by decide) selected_cut_33089

theorem unmarked_context_11_27491_852554 : frontier 10 ⟨852554, by decide⟩
    (prefixCache 11 27491) (prefixPartial 11 27491) = false := by
  decide +kernel

theorem node_context_11_27491_852554 : EJMOriginalGlobalDAGData.nodes 10 ⟨852554, by decide⟩ =
    .split (coordinate 11) (![⟨852502, by decide⟩,⟨852527, by decide⟩,⟨813440, by decide⟩,⟨852553, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27491_852554 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27491 ⟨852554, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27491
    ⟨852554, by decide⟩ (by decide) (![⟨852502, by decide⟩,⟨852527, by decide⟩,⟨813440, by decide⟩,⟨852553, by decide⟩]) unmarked_context_11_27491_852554 node_context_11_27491_852554
  intro a
  fin_cases a
  · exact context_12_109964_852502
  · exact context_12_109965_852527
  · exact context_12_109966_813440
  · exact context_12_109967_852553

theorem unmarked_context_10_6872_852555 : frontier 11 ⟨852555, by decide⟩
    (prefixCache 10 6872) (prefixPartial 10 6872) = false := by
  decide +kernel

theorem node_context_10_6872_852555 : EJMOriginalGlobalDAGData.nodes 11 ⟨852555, by decide⟩ =
    .split (coordinate 10) (![⟨852257, by decide⟩,⟨852345, by decide⟩,⟨852476, by decide⟩,⟨852554, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6872_852555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6872 ⟨852555, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6872
    ⟨852555, by decide⟩ (by decide) (![⟨852257, by decide⟩,⟨852345, by decide⟩,⟨852476, by decide⟩,⟨852554, by decide⟩]) unmarked_context_10_6872_852555 node_context_10_6872_852555
  intro a
  fin_cases a
  · exact context_11_27488_852257
  · exact context_11_27489_852345
  · exact context_11_27490_852476
  · exact context_11_27491_852554

theorem selected_cut_33090 : selected 9 ⟨852581, by decide⟩
    (prefixPartial 12 109968) = some ⟨12, 2, 0, 852581, 109968, 1893, 65536⟩ := by
  decide +kernel

theorem context_12_109968_852581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109968 ⟨852581, by decide⟩ :=
  accepted_of_selected 12 109968 ⟨852581, by decide⟩ ⟨12, 2, 0, 852581, 109968, 1893, 65536⟩
    (by decide) selected_cut_33090

theorem selected_cut_33091 : selected 9 ⟨852601, by decide⟩
    (prefixPartial 12 109969) = some ⟨12, 2, 0, 852601, 109969, 2061, 65536⟩ := by
  decide +kernel

theorem context_12_109969_852601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109969 ⟨852601, by decide⟩ :=
  accepted_of_selected 12 109969 ⟨852601, by decide⟩ ⟨12, 2, 0, 852601, 109969, 2061, 65536⟩
    (by decide) selected_cut_33091

theorem selected_cut_33092 : selected 9 ⟨813889, by decide⟩
    (prefixPartial 12 109970) = some ⟨12, 1, 0, 813889, 109970, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109970_813889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109970 ⟨813889, by decide⟩ :=
  accepted_of_selected 12 109970 ⟨813889, by decide⟩ ⟨12, 1, 0, 813889, 109970, 1, 65536⟩
    (by decide) selected_cut_33092

theorem selected_cut_33093 : selected 9 ⟨852651, by decide⟩
    (prefixPartial 12 109971) = some ⟨12, 2, 0, 852651, 109971, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_109971_852651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109971 ⟨852651, by decide⟩ :=
  accepted_of_selected 12 109971 ⟨852651, by decide⟩ ⟨12, 2, 0, 852651, 109971, 2181, 65536⟩
    (by decide) selected_cut_33093

theorem unmarked_context_11_27492_852652 : frontier 10 ⟨852652, by decide⟩
    (prefixCache 11 27492) (prefixPartial 11 27492) = false := by
  decide +kernel

theorem node_context_11_27492_852652 : EJMOriginalGlobalDAGData.nodes 10 ⟨852652, by decide⟩ =
    .split (coordinate 11) (![⟨852581, by decide⟩,⟨852601, by decide⟩,⟨813889, by decide⟩,⟨852651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27492_852652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27492 ⟨852652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27492
    ⟨852652, by decide⟩ (by decide) (![⟨852581, by decide⟩,⟨852601, by decide⟩,⟨813889, by decide⟩,⟨852651, by decide⟩]) unmarked_context_11_27492_852652 node_context_11_27492_852652
  intro a
  fin_cases a
  · exact context_12_109968_852581
  · exact context_12_109969_852601
  · exact context_12_109970_813889
  · exact context_12_109971_852651

theorem selected_cut_33094 : selected 10 ⟨852722, by decide⟩
    (prefixPartial 11 27493) = some ⟨11, 2, 0, 852722, 27493, 3605, 262144⟩ := by
  decide +kernel

theorem context_11_27493_852722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27493 ⟨852722, by decide⟩ :=
  accepted_of_selected 11 27493 ⟨852722, by decide⟩ ⟨11, 2, 0, 852722, 27493, 3605, 262144⟩
    (by decide) selected_cut_33094

theorem selected_cut_33095 : selected 9 ⟨852758, by decide⟩
    (prefixPartial 12 109976) = some ⟨12, 2, 0, 852758, 109976, 1649, 65536⟩ := by
  decide +kernel

theorem context_12_109976_852758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109976 ⟨852758, by decide⟩ :=
  accepted_of_selected 12 109976 ⟨852758, by decide⟩ ⟨12, 2, 0, 852758, 109976, 1649, 65536⟩
    (by decide) selected_cut_33095

theorem selected_cut_33096 : selected 9 ⟨852783, by decide⟩
    (prefixPartial 12 109977) = some ⟨12, 2, 0, 852783, 109977, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_109977_852783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109977 ⟨852783, by decide⟩ :=
  accepted_of_selected 12 109977 ⟨852783, by decide⟩ ⟨12, 2, 0, 852783, 109977, 1697, 65536⟩
    (by decide) selected_cut_33096

theorem selected_cut_33097 : selected 9 ⟨813979, by decide⟩
    (prefixPartial 12 109978) = some ⟨12, 1, 0, 813979, 109978, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109978_813979 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109978 ⟨813979, by decide⟩ :=
  accepted_of_selected 12 109978 ⟨813979, by decide⟩ ⟨12, 1, 0, 813979, 109978, 1, 65536⟩
    (by decide) selected_cut_33097

theorem selected_cut_33098 : selected 9 ⟨852814, by decide⟩
    (prefixPartial 12 109979) = some ⟨12, 2, 0, 852814, 109979, 1689, 65536⟩ := by
  decide +kernel

theorem context_12_109979_852814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109979 ⟨852814, by decide⟩ :=
  accepted_of_selected 12 109979 ⟨852814, by decide⟩ ⟨12, 2, 0, 852814, 109979, 1689, 65536⟩
    (by decide) selected_cut_33098

theorem unmarked_context_11_27494_852815 : frontier 10 ⟨852815, by decide⟩
    (prefixCache 11 27494) (prefixPartial 11 27494) = false := by
  decide +kernel

theorem node_context_11_27494_852815 : EJMOriginalGlobalDAGData.nodes 10 ⟨852815, by decide⟩ =
    .split (coordinate 11) (![⟨852758, by decide⟩,⟨852783, by decide⟩,⟨813979, by decide⟩,⟨852814, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27494_852815 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27494 ⟨852815, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27494
    ⟨852815, by decide⟩ (by decide) (![⟨852758, by decide⟩,⟨852783, by decide⟩,⟨813979, by decide⟩,⟨852814, by decide⟩]) unmarked_context_11_27494_852815 node_context_11_27494_852815
  intro a
  fin_cases a
  · exact context_12_109976_852758
  · exact context_12_109977_852783
  · exact context_12_109978_813979
  · exact context_12_109979_852814

theorem selected_cut_33099 : selected 9 ⟨852836, by decide⟩
    (prefixPartial 12 109980) = some ⟨12, 2, 0, 852836, 109980, 1645, 65536⟩ := by
  decide +kernel

theorem context_12_109980_852836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109980 ⟨852836, by decide⟩ :=
  accepted_of_selected 12 109980 ⟨852836, by decide⟩ ⟨12, 2, 0, 852836, 109980, 1645, 65536⟩
    (by decide) selected_cut_33099

theorem selected_cut_33100 : selected 9 ⟨852852, by decide⟩
    (prefixPartial 12 109981) = some ⟨12, 2, 0, 852852, 109981, 1693, 65536⟩ := by
  decide +kernel

theorem context_12_109981_852852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109981 ⟨852852, by decide⟩ :=
  accepted_of_selected 12 109981 ⟨852852, by decide⟩ ⟨12, 2, 0, 852852, 109981, 1693, 65536⟩
    (by decide) selected_cut_33100

theorem selected_cut_33101 : selected 9 ⟨852905, by decide⟩
    (prefixPartial 12 109982) = some ⟨12, 2, 0, 852905, 109982, 645, 65536⟩ := by
  decide +kernel

theorem context_12_109982_852905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109982 ⟨852905, by decide⟩ :=
  accepted_of_selected 12 109982 ⟨852905, by decide⟩ ⟨12, 2, 0, 852905, 109982, 645, 65536⟩
    (by decide) selected_cut_33101

theorem selected_cut_33102 : selected 9 ⟨852936, by decide⟩
    (prefixPartial 12 109983) = some ⟨12, 2, 0, 852936, 109983, 1789, 65536⟩ := by
  decide +kernel

theorem context_12_109983_852936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109983 ⟨852936, by decide⟩ :=
  accepted_of_selected 12 109983 ⟨852936, by decide⟩ ⟨12, 2, 0, 852936, 109983, 1789, 65536⟩
    (by decide) selected_cut_33102

theorem unmarked_context_11_27495_852937 : frontier 10 ⟨852937, by decide⟩
    (prefixCache 11 27495) (prefixPartial 11 27495) = false := by
  decide +kernel

theorem node_context_11_27495_852937 : EJMOriginalGlobalDAGData.nodes 10 ⟨852937, by decide⟩ =
    .split (coordinate 11) (![⟨852836, by decide⟩,⟨852852, by decide⟩,⟨852905, by decide⟩,⟨852936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27495_852937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27495 ⟨852937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27495
    ⟨852937, by decide⟩ (by decide) (![⟨852836, by decide⟩,⟨852852, by decide⟩,⟨852905, by decide⟩,⟨852936, by decide⟩]) unmarked_context_11_27495_852937 node_context_11_27495_852937
  intro a
  fin_cases a
  · exact context_12_109980_852836
  · exact context_12_109981_852852
  · exact context_12_109982_852905
  · exact context_12_109983_852936

theorem unmarked_context_10_6873_852938 : frontier 11 ⟨852938, by decide⟩
    (prefixCache 10 6873) (prefixPartial 10 6873) = false := by
  decide +kernel

theorem node_context_10_6873_852938 : EJMOriginalGlobalDAGData.nodes 11 ⟨852938, by decide⟩ =
    .split (coordinate 10) (![⟨852652, by decide⟩,⟨852722, by decide⟩,⟨852815, by decide⟩,⟨852937, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6873_852938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6873 ⟨852938, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6873
    ⟨852938, by decide⟩ (by decide) (![⟨852652, by decide⟩,⟨852722, by decide⟩,⟨852815, by decide⟩,⟨852937, by decide⟩]) unmarked_context_10_6873_852938 node_context_10_6873_852938
  intro a
  fin_cases a
  · exact context_11_27492_852652
  · exact context_11_27493_852722
  · exact context_11_27494_852815
  · exact context_11_27495_852937

theorem selected_cut_33103 : selected 9 ⟨852958, by decide⟩
    (prefixPartial 12 109984) = some ⟨12, 2, 0, 852958, 109984, 1397, 65536⟩ := by
  decide +kernel

theorem context_12_109984_852958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109984 ⟨852958, by decide⟩ :=
  accepted_of_selected 12 109984 ⟨852958, by decide⟩ ⟨12, 2, 0, 852958, 109984, 1397, 65536⟩
    (by decide) selected_cut_33103

theorem selected_cut_33104 : selected 9 ⟨852985, by decide⟩
    (prefixPartial 12 109985) = some ⟨12, 2, 0, 852985, 109985, 1421, 65536⟩ := by
  decide +kernel

theorem context_12_109985_852985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109985 ⟨852985, by decide⟩ :=
  accepted_of_selected 12 109985 ⟨852985, by decide⟩ ⟨12, 2, 0, 852985, 109985, 1421, 65536⟩
    (by decide) selected_cut_33104

theorem selected_cut_33105 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 109986) = some ⟨12, 1, 0, 769937, 109986, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109986_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109986 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 109986 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 109986, 1, 65536⟩
    (by decide) selected_cut_33105

theorem selected_cut_33106 : selected 9 ⟨853013, by decide⟩
    (prefixPartial 12 109987) = some ⟨12, 2, 0, 853013, 109987, 1597, 65536⟩ := by
  decide +kernel

theorem context_12_109987_853013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109987 ⟨853013, by decide⟩ :=
  accepted_of_selected 12 109987 ⟨853013, by decide⟩ ⟨12, 2, 0, 853013, 109987, 1597, 65536⟩
    (by decide) selected_cut_33106

theorem unmarked_context_11_27496_853014 : frontier 10 ⟨853014, by decide⟩
    (prefixCache 11 27496) (prefixPartial 11 27496) = false := by
  decide +kernel

theorem node_context_11_27496_853014 : EJMOriginalGlobalDAGData.nodes 10 ⟨853014, by decide⟩ =
    .split (coordinate 11) (![⟨852958, by decide⟩,⟨852985, by decide⟩,⟨769937, by decide⟩,⟨853013, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27496_853014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27496 ⟨853014, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27496
    ⟨853014, by decide⟩ (by decide) (![⟨852958, by decide⟩,⟨852985, by decide⟩,⟨769937, by decide⟩,⟨853013, by decide⟩]) unmarked_context_11_27496_853014 node_context_11_27496_853014
  intro a
  fin_cases a
  · exact context_12_109984_852958
  · exact context_12_109985_852985
  · exact context_12_109986_769937
  · exact context_12_109987_853013

theorem selected_cut_33107 : selected 10 ⟨853069, by decide⟩
    (prefixPartial 11 27497) = some ⟨11, 2, 0, 853069, 27497, 2897, 262144⟩ := by
  decide +kernel

theorem context_11_27497_853069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27497 ⟨853069, by decide⟩ :=
  accepted_of_selected 11 27497 ⟨853069, by decide⟩ ⟨11, 2, 0, 853069, 27497, 2897, 262144⟩
    (by decide) selected_cut_33107

theorem selected_cut_33108 : selected 10 ⟨853135, by decide⟩
    (prefixPartial 11 27498) = some ⟨11, 2, 0, 853135, 27498, 3701, 262144⟩ := by
  decide +kernel

theorem context_11_27498_853135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27498 ⟨853135, by decide⟩ :=
  accepted_of_selected 11 27498 ⟨853135, by decide⟩ ⟨11, 2, 0, 853135, 27498, 3701, 262144⟩
    (by decide) selected_cut_33108

theorem selected_cut_33109 : selected 9 ⟨853153, by decide⟩
    (prefixPartial 12 109996) = some ⟨12, 2, 0, 853153, 109996, 1377, 65536⟩ := by
  decide +kernel

theorem context_12_109996_853153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109996 ⟨853153, by decide⟩ :=
  accepted_of_selected 12 109996 ⟨853153, by decide⟩ ⟨12, 2, 0, 853153, 109996, 1377, 65536⟩
    (by decide) selected_cut_33109

theorem selected_cut_33110 : selected 9 ⟨853171, by decide⟩
    (prefixPartial 12 109997) = some ⟨12, 2, 0, 853171, 109997, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_109997_853171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109997 ⟨853171, by decide⟩ :=
  accepted_of_selected 12 109997 ⟨853171, by decide⟩ ⟨12, 2, 0, 853171, 109997, 1369, 65536⟩
    (by decide) selected_cut_33110

theorem selected_cut_33111 : selected 9 ⟨769937, by decide⟩
    (prefixPartial 12 109998) = some ⟨12, 1, 0, 769937, 109998, 1, 65536⟩ := by
  decide +kernel

theorem context_12_109998_769937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109998 ⟨769937, by decide⟩ :=
  accepted_of_selected 12 109998 ⟨769937, by decide⟩ ⟨12, 1, 0, 769937, 109998, 1, 65536⟩
    (by decide) selected_cut_33111

theorem selected_cut_33112 : selected 9 ⟨853209, by decide⟩
    (prefixPartial 12 109999) = some ⟨12, 2, 0, 853209, 109999, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_109999_853209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 109999 ⟨853209, by decide⟩ :=
  accepted_of_selected 12 109999 ⟨853209, by decide⟩ ⟨12, 2, 0, 853209, 109999, 1533, 65536⟩
    (by decide) selected_cut_33112

theorem unmarked_context_11_27499_853210 : frontier 10 ⟨853210, by decide⟩
    (prefixCache 11 27499) (prefixPartial 11 27499) = false := by
  decide +kernel

theorem node_context_11_27499_853210 : EJMOriginalGlobalDAGData.nodes 10 ⟨853210, by decide⟩ =
    .split (coordinate 11) (![⟨853153, by decide⟩,⟨853171, by decide⟩,⟨769937, by decide⟩,⟨853209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27499_853210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27499 ⟨853210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27499
    ⟨853210, by decide⟩ (by decide) (![⟨853153, by decide⟩,⟨853171, by decide⟩,⟨769937, by decide⟩,⟨853209, by decide⟩]) unmarked_context_11_27499_853210 node_context_11_27499_853210
  intro a
  fin_cases a
  · exact context_12_109996_853153
  · exact context_12_109997_853171
  · exact context_12_109998_769937
  · exact context_12_109999_853209

theorem unmarked_context_10_6874_853211 : frontier 11 ⟨853211, by decide⟩
    (prefixCache 10 6874) (prefixPartial 10 6874) = false := by
  decide +kernel

theorem node_context_10_6874_853211 : EJMOriginalGlobalDAGData.nodes 11 ⟨853211, by decide⟩ =
    .split (coordinate 10) (![⟨853014, by decide⟩,⟨853069, by decide⟩,⟨853135, by decide⟩,⟨853210, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6874_853211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6874 ⟨853211, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6874
    ⟨853211, by decide⟩ (by decide) (![⟨853014, by decide⟩,⟨853069, by decide⟩,⟨853135, by decide⟩,⟨853210, by decide⟩]) unmarked_context_10_6874_853211 node_context_10_6874_853211
  intro a
  fin_cases a
  · exact context_11_27496_853014
  · exact context_11_27497_853069
  · exact context_11_27498_853135
  · exact context_11_27499_853210

theorem selected_cut_33113 : selected 10 ⟨853248, by decide⟩
    (prefixPartial 11 27500) = some ⟨11, 2, 0, 853248, 27500, 2933, 262144⟩ := by
  decide +kernel

theorem context_11_27500_853248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27500 ⟨853248, by decide⟩ :=
  accepted_of_selected 11 27500 ⟨853248, by decide⟩ ⟨11, 2, 0, 853248, 27500, 2933, 262144⟩
    (by decide) selected_cut_33113

theorem selected_cut_33114 : selected 10 ⟨853268, by decide⟩
    (prefixPartial 11 27501) = some ⟨11, 2, 0, 853268, 27501, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_27501_853268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27501 ⟨853268, by decide⟩ :=
  accepted_of_selected 11 27501 ⟨853268, by decide⟩ ⟨11, 2, 0, 853268, 27501, 1525, 262144⟩
    (by decide) selected_cut_33114

theorem selected_cut_33115 : selected 10 ⟨853302, by decide⟩
    (prefixPartial 11 27502) = some ⟨11, 2, 0, 853302, 27502, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_27502_853302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27502 ⟨853302, by decide⟩ :=
  accepted_of_selected 11 27502 ⟨853302, by decide⟩ ⟨11, 2, 0, 853302, 27502, 2309, 262144⟩
    (by decide) selected_cut_33115

theorem selected_cut_33116 : selected 10 ⟨853304, by decide⟩
    (prefixPartial 11 27503) = some ⟨11, 2, 0, 853304, 27503, 5, 262144⟩ := by
  decide +kernel

theorem context_11_27503_853304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27503 ⟨853304, by decide⟩ :=
  accepted_of_selected 11 27503 ⟨853304, by decide⟩ ⟨11, 2, 0, 853304, 27503, 5, 262144⟩
    (by decide) selected_cut_33116

theorem unmarked_context_10_6875_853305 : frontier 11 ⟨853305, by decide⟩
    (prefixCache 10 6875) (prefixPartial 10 6875) = false := by
  decide +kernel

theorem node_context_10_6875_853305 : EJMOriginalGlobalDAGData.nodes 11 ⟨853305, by decide⟩ =
    .split (coordinate 10) (![⟨853248, by decide⟩,⟨853268, by decide⟩,⟨853302, by decide⟩,⟨853304, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6875_853305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6875 ⟨853305, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6875
    ⟨853305, by decide⟩ (by decide) (![⟨853248, by decide⟩,⟨853268, by decide⟩,⟨853302, by decide⟩,⟨853304, by decide⟩]) unmarked_context_10_6875_853305 node_context_10_6875_853305
  intro a
  fin_cases a
  · exact context_11_27500_853248
  · exact context_11_27501_853268
  · exact context_11_27502_853302
  · exact context_11_27503_853304

theorem unmarked_context_9_1718_853306 : frontier 12 ⟨853306, by decide⟩
    (prefixCache 9 1718) (prefixPartial 9 1718) = false := by
  decide +kernel

theorem node_context_9_1718_853306 : EJMOriginalGlobalDAGData.nodes 12 ⟨853306, by decide⟩ =
    .split (coordinate 9) (![⟨852555, by decide⟩,⟨852938, by decide⟩,⟨853211, by decide⟩,⟨853305, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1718_853306 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1718 ⟨853306, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1718
    ⟨853306, by decide⟩ (by decide) (![⟨852555, by decide⟩,⟨852938, by decide⟩,⟨853211, by decide⟩,⟨853305, by decide⟩]) unmarked_context_9_1718_853306 node_context_9_1718_853306
  intro a
  fin_cases a
  · exact context_10_6872_852555
  · exact context_10_6873_852938
  · exact context_10_6874_853211
  · exact context_10_6875_853305

theorem selected_cut_33117 : selected 10 ⟨853348, by decide⟩
    (prefixPartial 11 27504) = some ⟨11, 2, 0, 853348, 27504, 3657, 262144⟩ := by
  decide +kernel

theorem context_11_27504_853348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27504 ⟨853348, by decide⟩ :=
  accepted_of_selected 11 27504 ⟨853348, by decide⟩ ⟨11, 2, 0, 853348, 27504, 3657, 262144⟩
    (by decide) selected_cut_33117

theorem selected_cut_33118 : selected 10 ⟨853392, by decide⟩
    (prefixPartial 11 27505) = some ⟨11, 2, 0, 853392, 27505, 2673, 262144⟩ := by
  decide +kernel

theorem context_11_27505_853392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27505 ⟨853392, by decide⟩ :=
  accepted_of_selected 11 27505 ⟨853392, by decide⟩ ⟨11, 2, 0, 853392, 27505, 2673, 262144⟩
    (by decide) selected_cut_33118

theorem selected_cut_33119 : selected 10 ⟨853428, by decide⟩
    (prefixPartial 11 27506) = some ⟨11, 2, 0, 853428, 27506, 2529, 262144⟩ := by
  decide +kernel

theorem context_11_27506_853428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27506 ⟨853428, by decide⟩ :=
  accepted_of_selected 11 27506 ⟨853428, by decide⟩ ⟨11, 2, 0, 853428, 27506, 2529, 262144⟩
    (by decide) selected_cut_33119

theorem selected_cut_33120 : selected 10 ⟨853472, by decide⟩
    (prefixPartial 11 27507) = some ⟨11, 2, 0, 853472, 27507, 3053, 262144⟩ := by
  decide +kernel

theorem context_11_27507_853472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27507 ⟨853472, by decide⟩ :=
  accepted_of_selected 11 27507 ⟨853472, by decide⟩ ⟨11, 2, 0, 853472, 27507, 3053, 262144⟩
    (by decide) selected_cut_33120

theorem unmarked_context_10_6876_853473 : frontier 11 ⟨853473, by decide⟩
    (prefixCache 10 6876) (prefixPartial 10 6876) = false := by
  decide +kernel

theorem node_context_10_6876_853473 : EJMOriginalGlobalDAGData.nodes 11 ⟨853473, by decide⟩ =
    .split (coordinate 10) (![⟨853348, by decide⟩,⟨853392, by decide⟩,⟨853428, by decide⟩,⟨853472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6876_853473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6876 ⟨853473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6876
    ⟨853473, by decide⟩ (by decide) (![⟨853348, by decide⟩,⟨853392, by decide⟩,⟨853428, by decide⟩,⟨853472, by decide⟩]) unmarked_context_10_6876_853473 node_context_10_6876_853473
  intro a
  fin_cases a
  · exact context_11_27504_853348
  · exact context_11_27505_853392
  · exact context_11_27506_853428
  · exact context_11_27507_853472

theorem selected_cut_33121 : selected 10 ⟨853504, by decide⟩
    (prefixPartial 11 27508) = some ⟨11, 2, 0, 853504, 27508, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_27508_853504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27508 ⟨853504, by decide⟩ :=
  accepted_of_selected 11 27508 ⟨853504, by decide⟩ ⟨11, 2, 0, 853504, 27508, 2433, 262144⟩
    (by decide) selected_cut_33121

theorem selected_cut_33122 : selected 10 ⟨853519, by decide⟩
    (prefixPartial 11 27509) = some ⟨11, 2, 0, 853519, 27509, 1425, 262144⟩ := by
  decide +kernel

theorem context_11_27509_853519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27509 ⟨853519, by decide⟩ :=
  accepted_of_selected 11 27509 ⟨853519, by decide⟩ ⟨11, 2, 0, 853519, 27509, 1425, 262144⟩
    (by decide) selected_cut_33122

theorem selected_cut_33123 : selected 10 ⟨853539, by decide⟩
    (prefixPartial 11 27510) = some ⟨11, 2, 0, 853539, 27510, 1469, 262144⟩ := by
  decide +kernel

theorem context_11_27510_853539 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27510 ⟨853539, by decide⟩ :=
  accepted_of_selected 11 27510 ⟨853539, by decide⟩ ⟨11, 2, 0, 853539, 27510, 1469, 262144⟩
    (by decide) selected_cut_33123

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
