/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover147
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_14211 : selected 8 ⟨368694, by decide⟩
    (prefixPartial 13 108600) = some ⟨13, 2, 0, 368694, 108600, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_108600_368694 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108600 ⟨368694, by decide⟩ :=
  accepted_of_selected 13 108600 ⟨368694, by decide⟩ ⟨13, 2, 0, 368694, 108600, 2857, 16384⟩
    (by decide) selected_cut_14211

theorem selected_cut_14212 : selected 8 ⟨368758, by decide⟩
    (prefixPartial 13 108601) = some ⟨13, 2, 0, 368758, 108601, 3677, 16384⟩ := by
  decide +kernel

theorem context_13_108601_368758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108601 ⟨368758, by decide⟩ :=
  accepted_of_selected 13 108601 ⟨368758, by decide⟩ ⟨13, 2, 0, 368758, 108601, 3677, 16384⟩
    (by decide) selected_cut_14212

theorem selected_cut_14213 : selected 8 ⟨368790, by decide⟩
    (prefixPartial 13 108602) = some ⟨13, 2, 0, 368790, 108602, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_108602_368790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108602 ⟨368790, by decide⟩ :=
  accepted_of_selected 13 108602 ⟨368790, by decide⟩ ⟨13, 2, 0, 368790, 108602, 1929, 16384⟩
    (by decide) selected_cut_14213

theorem selected_cut_14214 : selected 8 ⟨368799, by decide⟩
    (prefixPartial 13 108603) = some ⟨13, 2, 0, 368799, 108603, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_108603_368799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108603 ⟨368799, by decide⟩ :=
  accepted_of_selected 13 108603 ⟨368799, by decide⟩ ⟨13, 2, 0, 368799, 108603, 1117, 16384⟩
    (by decide) selected_cut_14214

theorem unmarked_context_12_27150_368800 : frontier 9 ⟨368800, by decide⟩
    (prefixCache 12 27150) (prefixPartial 12 27150) = false := by
  decide +kernel

theorem node_context_12_27150_368800 : EJMOriginalGlobalDAGData.nodes 9 ⟨368800, by decide⟩ =
    .split (coordinate 12) (![⟨368694, by decide⟩,⟨368758, by decide⟩,⟨368790, by decide⟩,⟨368799, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27150_368800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27150 ⟨368800, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27150
    ⟨368800, by decide⟩ (by decide) (![⟨368694, by decide⟩,⟨368758, by decide⟩,⟨368790, by decide⟩,⟨368799, by decide⟩]) unmarked_context_12_27150_368800 node_context_12_27150_368800
  intro a
  fin_cases a
  · exact context_13_108600_368694
  · exact context_13_108601_368758
  · exact context_13_108602_368790
  · exact context_13_108603_368799

theorem selected_cut_14215 : selected 8 ⟨368861, by decide⟩
    (prefixPartial 13 108604) = some ⟨13, 2, 0, 368861, 108604, 3729, 16384⟩ := by
  decide +kernel

theorem context_13_108604_368861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108604 ⟨368861, by decide⟩ :=
  accepted_of_selected 13 108604 ⟨368861, by decide⟩ ⟨13, 2, 0, 368861, 108604, 3729, 16384⟩
    (by decide) selected_cut_14215

theorem selected_cut_14216 : selected 8 ⟨368923, by decide⟩
    (prefixPartial 13 108605) = some ⟨13, 2, 0, 368923, 108605, 3957, 16384⟩ := by
  decide +kernel

theorem context_13_108605_368923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108605 ⟨368923, by decide⟩ :=
  accepted_of_selected 13 108605 ⟨368923, by decide⟩ ⟨13, 2, 0, 368923, 108605, 3957, 16384⟩
    (by decide) selected_cut_14216

theorem selected_cut_14217 : selected 8 ⟨368943, by decide⟩
    (prefixPartial 13 108606) = some ⟨13, 2, 0, 368943, 108606, 2005, 16384⟩ := by
  decide +kernel

theorem context_13_108606_368943 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108606 ⟨368943, by decide⟩ :=
  accepted_of_selected 13 108606 ⟨368943, by decide⟩ ⟨13, 2, 0, 368943, 108606, 2005, 16384⟩
    (by decide) selected_cut_14217

theorem selected_cut_14218 : selected 8 ⟨368954, by decide⟩
    (prefixPartial 13 108607) = some ⟨13, 2, 0, 368954, 108607, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_108607_368954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108607 ⟨368954, by decide⟩ :=
  accepted_of_selected 13 108607 ⟨368954, by decide⟩ ⟨13, 2, 0, 368954, 108607, 1193, 16384⟩
    (by decide) selected_cut_14218

theorem unmarked_context_12_27151_368955 : frontier 9 ⟨368955, by decide⟩
    (prefixCache 12 27151) (prefixPartial 12 27151) = false := by
  decide +kernel

theorem node_context_12_27151_368955 : EJMOriginalGlobalDAGData.nodes 9 ⟨368955, by decide⟩ =
    .split (coordinate 12) (![⟨368861, by decide⟩,⟨368923, by decide⟩,⟨368943, by decide⟩,⟨368954, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27151_368955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27151 ⟨368955, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27151
    ⟨368955, by decide⟩ (by decide) (![⟨368861, by decide⟩,⟨368923, by decide⟩,⟨368943, by decide⟩,⟨368954, by decide⟩]) unmarked_context_12_27151_368955 node_context_12_27151_368955
  intro a
  fin_cases a
  · exact context_13_108604_368861
  · exact context_13_108605_368923
  · exact context_13_108606_368943
  · exact context_13_108607_368954

theorem unmarked_context_11_6787_368956 : frontier 10 ⟨368956, by decide⟩
    (prefixCache 11 6787) (prefixPartial 11 6787) = false := by
  decide +kernel

theorem node_context_11_6787_368956 : EJMOriginalGlobalDAGData.nodes 10 ⟨368956, by decide⟩ =
    .split (coordinate 11) (![⟨368488, by decide⟩,⟨368647, by decide⟩,⟨368800, by decide⟩,⟨368955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6787_368956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6787 ⟨368956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6787
    ⟨368956, by decide⟩ (by decide) (![⟨368488, by decide⟩,⟨368647, by decide⟩,⟨368800, by decide⟩,⟨368955, by decide⟩]) unmarked_context_11_6787_368956 node_context_11_6787_368956
  intro a
  fin_cases a
  · exact context_12_27148_368488
  · exact context_12_27149_368647
  · exact context_12_27150_368800
  · exact context_12_27151_368955

theorem unmarked_context_10_1696_368957 : frontier 11 ⟨368957, by decide⟩
    (prefixCache 10 1696) (prefixPartial 10 1696) = false := by
  decide +kernel

theorem node_context_10_1696_368957 : EJMOriginalGlobalDAGData.nodes 11 ⟨368957, by decide⟩ =
    .split (coordinate 10) (![⟨367091, by decide⟩,⟨367572, by decide⟩,⟨368324, by decide⟩,⟨368956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1696_368957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1696 ⟨368957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1696
    ⟨368957, by decide⟩ (by decide) (![⟨367091, by decide⟩,⟨367572, by decide⟩,⟨368324, by decide⟩,⟨368956, by decide⟩]) unmarked_context_10_1696_368957 node_context_10_1696_368957
  intro a
  fin_cases a
  · exact context_11_6784_367091
  · exact context_11_6785_367572
  · exact context_11_6786_368324
  · exact context_11_6787_368956

theorem selected_cut_14219 : selected 8 ⟨368980, by decide⟩
    (prefixPartial 13 108608) = some ⟨13, 2, 0, 368980, 108608, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_108608_368980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108608 ⟨368980, by decide⟩ :=
  accepted_of_selected 13 108608 ⟨368980, by decide⟩ ⟨13, 2, 0, 368980, 108608, 2201, 16384⟩
    (by decide) selected_cut_14219

theorem selected_cut_14220 : selected 8 ⟨369004, by decide⟩
    (prefixPartial 13 108609) = some ⟨13, 2, 0, 369004, 108609, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_108609_369004 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108609 ⟨369004, by decide⟩ :=
  accepted_of_selected 13 108609 ⟨369004, by decide⟩ ⟨13, 2, 0, 369004, 108609, 2217, 16384⟩
    (by decide) selected_cut_14220

theorem selected_cut_14221 : selected 8 ⟨369017, by decide⟩
    (prefixPartial 13 108610) = some ⟨13, 2, 0, 369017, 108610, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_108610_369017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108610 ⟨369017, by decide⟩ :=
  accepted_of_selected 13 108610 ⟨369017, by decide⟩ ⟨13, 2, 0, 369017, 108610, 1109, 16384⟩
    (by decide) selected_cut_14221

theorem selected_cut_14222 : selected 8 ⟨369024, by decide⟩
    (prefixPartial 13 108611) = some ⟨13, 2, 0, 369024, 108611, 949, 16384⟩ := by
  decide +kernel

theorem context_13_108611_369024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108611 ⟨369024, by decide⟩ :=
  accepted_of_selected 13 108611 ⟨369024, by decide⟩ ⟨13, 2, 0, 369024, 108611, 949, 16384⟩
    (by decide) selected_cut_14222

theorem unmarked_context_12_27152_369025 : frontier 9 ⟨369025, by decide⟩
    (prefixCache 12 27152) (prefixPartial 12 27152) = false := by
  decide +kernel

theorem node_context_12_27152_369025 : EJMOriginalGlobalDAGData.nodes 9 ⟨369025, by decide⟩ =
    .split (coordinate 12) (![⟨368980, by decide⟩,⟨369004, by decide⟩,⟨369017, by decide⟩,⟨369024, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27152_369025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27152 ⟨369025, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27152
    ⟨369025, by decide⟩ (by decide) (![⟨368980, by decide⟩,⟨369004, by decide⟩,⟨369017, by decide⟩,⟨369024, by decide⟩]) unmarked_context_12_27152_369025 node_context_12_27152_369025
  intro a
  fin_cases a
  · exact context_13_108608_368980
  · exact context_13_108609_369004
  · exact context_13_108610_369017
  · exact context_13_108611_369024

theorem selected_cut_14223 : selected 8 ⟨369052, by decide⟩
    (prefixPartial 13 108612) = some ⟨13, 2, 0, 369052, 108612, 2473, 16384⟩ := by
  decide +kernel

theorem context_13_108612_369052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108612 ⟨369052, by decide⟩ :=
  accepted_of_selected 13 108612 ⟨369052, by decide⟩ ⟨13, 2, 0, 369052, 108612, 2473, 16384⟩
    (by decide) selected_cut_14223

theorem selected_cut_14224 : selected 8 ⟨369083, by decide⟩
    (prefixPartial 13 108613) = some ⟨13, 2, 0, 369083, 108613, 2325, 16384⟩ := by
  decide +kernel

theorem context_13_108613_369083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108613 ⟨369083, by decide⟩ :=
  accepted_of_selected 13 108613 ⟨369083, by decide⟩ ⟨13, 2, 0, 369083, 108613, 2325, 16384⟩
    (by decide) selected_cut_14224

theorem selected_cut_14225 : selected 8 ⟨369099, by decide⟩
    (prefixPartial 13 108614) = some ⟨13, 2, 0, 369099, 108614, 1253, 16384⟩ := by
  decide +kernel

theorem context_13_108614_369099 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108614 ⟨369099, by decide⟩ :=
  accepted_of_selected 13 108614 ⟨369099, by decide⟩ ⟨13, 2, 0, 369099, 108614, 1253, 16384⟩
    (by decide) selected_cut_14225

theorem selected_cut_14226 : selected 8 ⟨369103, by decide⟩
    (prefixPartial 13 108615) = some ⟨13, 2, 0, 369103, 108615, 989, 16384⟩ := by
  decide +kernel

theorem context_13_108615_369103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108615 ⟨369103, by decide⟩ :=
  accepted_of_selected 13 108615 ⟨369103, by decide⟩ ⟨13, 2, 0, 369103, 108615, 989, 16384⟩
    (by decide) selected_cut_14226

theorem unmarked_context_12_27153_369104 : frontier 9 ⟨369104, by decide⟩
    (prefixCache 12 27153) (prefixPartial 12 27153) = false := by
  decide +kernel

theorem node_context_12_27153_369104 : EJMOriginalGlobalDAGData.nodes 9 ⟨369104, by decide⟩ =
    .split (coordinate 12) (![⟨369052, by decide⟩,⟨369083, by decide⟩,⟨369099, by decide⟩,⟨369103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27153_369104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27153 ⟨369104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27153
    ⟨369104, by decide⟩ (by decide) (![⟨369052, by decide⟩,⟨369083, by decide⟩,⟨369099, by decide⟩,⟨369103, by decide⟩]) unmarked_context_12_27153_369104 node_context_12_27153_369104
  intro a
  fin_cases a
  · exact context_13_108612_369052
  · exact context_13_108613_369083
  · exact context_13_108614_369099
  · exact context_13_108615_369103

theorem selected_cut_14227 : selected 8 ⟨369127, by decide⟩
    (prefixPartial 13 108616) = some ⟨13, 2, 0, 369127, 108616, 2069, 16384⟩ := by
  decide +kernel

theorem context_13_108616_369127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108616 ⟨369127, by decide⟩ :=
  accepted_of_selected 13 108616 ⟨369127, by decide⟩ ⟨13, 2, 0, 369127, 108616, 2069, 16384⟩
    (by decide) selected_cut_14227

theorem selected_cut_14228 : selected 8 ⟨369154, by decide⟩
    (prefixPartial 13 108617) = some ⟨13, 2, 0, 369154, 108617, 2293, 16384⟩ := by
  decide +kernel

theorem context_13_108617_369154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108617 ⟨369154, by decide⟩ :=
  accepted_of_selected 13 108617 ⟨369154, by decide⟩ ⟨13, 2, 0, 369154, 108617, 2293, 16384⟩
    (by decide) selected_cut_14228

theorem selected_cut_14229 : selected 8 ⟨369172, by decide⟩
    (prefixPartial 13 108618) = some ⟨13, 2, 0, 369172, 108618, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_108618_369172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108618 ⟨369172, by decide⟩ :=
  accepted_of_selected 13 108618 ⟨369172, by decide⟩ ⟨13, 2, 0, 369172, 108618, 1241, 16384⟩
    (by decide) selected_cut_14229

theorem selected_cut_14230 : selected 8 ⟨369179, by decide⟩
    (prefixPartial 13 108619) = some ⟨13, 2, 0, 369179, 108619, 985, 16384⟩ := by
  decide +kernel

theorem context_13_108619_369179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108619 ⟨369179, by decide⟩ :=
  accepted_of_selected 13 108619 ⟨369179, by decide⟩ ⟨13, 2, 0, 369179, 108619, 985, 16384⟩
    (by decide) selected_cut_14230

theorem unmarked_context_12_27154_369180 : frontier 9 ⟨369180, by decide⟩
    (prefixCache 12 27154) (prefixPartial 12 27154) = false := by
  decide +kernel

theorem node_context_12_27154_369180 : EJMOriginalGlobalDAGData.nodes 9 ⟨369180, by decide⟩ =
    .split (coordinate 12) (![⟨369127, by decide⟩,⟨369154, by decide⟩,⟨369172, by decide⟩,⟨369179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27154_369180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27154 ⟨369180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27154
    ⟨369180, by decide⟩ (by decide) (![⟨369127, by decide⟩,⟨369154, by decide⟩,⟨369172, by decide⟩,⟨369179, by decide⟩]) unmarked_context_12_27154_369180 node_context_12_27154_369180
  intro a
  fin_cases a
  · exact context_13_108616_369127
  · exact context_13_108617_369154
  · exact context_13_108618_369172
  · exact context_13_108619_369179

theorem selected_cut_14231 : selected 8 ⟨369208, by decide⟩
    (prefixPartial 13 108620) = some ⟨13, 2, 0, 369208, 108620, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_108620_369208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108620 ⟨369208, by decide⟩ :=
  accepted_of_selected 13 108620 ⟨369208, by decide⟩ ⟨13, 2, 0, 369208, 108620, 2677, 16384⟩
    (by decide) selected_cut_14231

theorem selected_cut_14232 : selected 8 ⟨369247, by decide⟩
    (prefixPartial 13 108621) = some ⟨13, 2, 0, 369247, 108621, 2857, 16384⟩ := by
  decide +kernel

theorem context_13_108621_369247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108621 ⟨369247, by decide⟩ :=
  accepted_of_selected 13 108621 ⟨369247, by decide⟩ ⟨13, 2, 0, 369247, 108621, 2857, 16384⟩
    (by decide) selected_cut_14232

theorem selected_cut_14233 : selected 8 ⟨369265, by decide⟩
    (prefixPartial 13 108622) = some ⟨13, 2, 0, 369265, 108622, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_108622_369265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108622 ⟨369265, by decide⟩ :=
  accepted_of_selected 13 108622 ⟨369265, by decide⟩ ⟨13, 2, 0, 369265, 108622, 1413, 16384⟩
    (by decide) selected_cut_14233

theorem selected_cut_14234 : selected 8 ⟨369273, by decide⟩
    (prefixPartial 13 108623) = some ⟨13, 2, 0, 369273, 108623, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_108623_369273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108623 ⟨369273, by decide⟩ :=
  accepted_of_selected 13 108623 ⟨369273, by decide⟩ ⟨13, 2, 0, 369273, 108623, 1105, 16384⟩
    (by decide) selected_cut_14234

theorem unmarked_context_12_27155_369274 : frontier 9 ⟨369274, by decide⟩
    (prefixCache 12 27155) (prefixPartial 12 27155) = false := by
  decide +kernel

theorem node_context_12_27155_369274 : EJMOriginalGlobalDAGData.nodes 9 ⟨369274, by decide⟩ =
    .split (coordinate 12) (![⟨369208, by decide⟩,⟨369247, by decide⟩,⟨369265, by decide⟩,⟨369273, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27155_369274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27155 ⟨369274, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27155
    ⟨369274, by decide⟩ (by decide) (![⟨369208, by decide⟩,⟨369247, by decide⟩,⟨369265, by decide⟩,⟨369273, by decide⟩]) unmarked_context_12_27155_369274 node_context_12_27155_369274
  intro a
  fin_cases a
  · exact context_13_108620_369208
  · exact context_13_108621_369247
  · exact context_13_108622_369265
  · exact context_13_108623_369273

theorem unmarked_context_11_6788_369275 : frontier 10 ⟨369275, by decide⟩
    (prefixCache 11 6788) (prefixPartial 11 6788) = false := by
  decide +kernel

theorem node_context_11_6788_369275 : EJMOriginalGlobalDAGData.nodes 10 ⟨369275, by decide⟩ =
    .split (coordinate 11) (![⟨369025, by decide⟩,⟨369104, by decide⟩,⟨369180, by decide⟩,⟨369274, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6788_369275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6788 ⟨369275, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6788
    ⟨369275, by decide⟩ (by decide) (![⟨369025, by decide⟩,⟨369104, by decide⟩,⟨369180, by decide⟩,⟨369274, by decide⟩]) unmarked_context_11_6788_369275 node_context_11_6788_369275
  intro a
  fin_cases a
  · exact context_12_27152_369025
  · exact context_12_27153_369104
  · exact context_12_27154_369180
  · exact context_12_27155_369274

theorem selected_cut_14235 : selected 8 ⟨369296, by decide⟩
    (prefixPartial 13 108624) = some ⟨13, 2, 0, 369296, 108624, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_108624_369296 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108624 ⟨369296, by decide⟩ :=
  accepted_of_selected 13 108624 ⟨369296, by decide⟩ ⟨13, 2, 0, 369296, 108624, 1941, 16384⟩
    (by decide) selected_cut_14235

theorem selected_cut_14236 : selected 8 ⟨369324, by decide⟩
    (prefixPartial 13 108625) = some ⟨13, 2, 0, 369324, 108625, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_108625_369324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108625 ⟨369324, by decide⟩ :=
  accepted_of_selected 13 108625 ⟨369324, by decide⟩ ⟨13, 2, 0, 369324, 108625, 2461, 16384⟩
    (by decide) selected_cut_14236

theorem selected_cut_14237 : selected 8 ⟨369340, by decide⟩
    (prefixPartial 13 108626) = some ⟨13, 2, 0, 369340, 108626, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_108626_369340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108626 ⟨369340, by decide⟩ :=
  accepted_of_selected 13 108626 ⟨369340, by decide⟩ ⟨13, 2, 0, 369340, 108626, 1161, 16384⟩
    (by decide) selected_cut_14237

theorem selected_cut_14238 : selected 8 ⟨369348, by decide⟩
    (prefixPartial 13 108627) = some ⟨13, 2, 0, 369348, 108627, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_108627_369348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108627 ⟨369348, by decide⟩ :=
  accepted_of_selected 13 108627 ⟨369348, by decide⟩ ⟨13, 2, 0, 369348, 108627, 1041, 16384⟩
    (by decide) selected_cut_14238

theorem unmarked_context_12_27156_369349 : frontier 9 ⟨369349, by decide⟩
    (prefixCache 12 27156) (prefixPartial 12 27156) = false := by
  decide +kernel

theorem node_context_12_27156_369349 : EJMOriginalGlobalDAGData.nodes 9 ⟨369349, by decide⟩ =
    .split (coordinate 12) (![⟨369296, by decide⟩,⟨369324, by decide⟩,⟨369340, by decide⟩,⟨369348, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27156_369349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27156 ⟨369349, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27156
    ⟨369349, by decide⟩ (by decide) (![⟨369296, by decide⟩,⟨369324, by decide⟩,⟨369340, by decide⟩,⟨369348, by decide⟩]) unmarked_context_12_27156_369349 node_context_12_27156_369349
  intro a
  fin_cases a
  · exact context_13_108624_369296
  · exact context_13_108625_369324
  · exact context_13_108626_369340
  · exact context_13_108627_369348

theorem selected_cut_14239 : selected 8 ⟨369381, by decide⟩
    (prefixPartial 13 108628) = some ⟨13, 2, 0, 369381, 108628, 2385, 16384⟩ := by
  decide +kernel

theorem context_13_108628_369381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108628 ⟨369381, by decide⟩ :=
  accepted_of_selected 13 108628 ⟨369381, by decide⟩ ⟨13, 2, 0, 369381, 108628, 2385, 16384⟩
    (by decide) selected_cut_14239

theorem selected_cut_14240 : selected 8 ⟨369406, by decide⟩
    (prefixPartial 13 108629) = some ⟨13, 2, 0, 369406, 108629, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_108629_369406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108629 ⟨369406, by decide⟩ :=
  accepted_of_selected 13 108629 ⟨369406, by decide⟩ ⟨13, 2, 0, 369406, 108629, 2037, 16384⟩
    (by decide) selected_cut_14240

theorem selected_cut_14241 : selected 8 ⟨369422, by decide⟩
    (prefixPartial 13 108630) = some ⟨13, 2, 0, 369422, 108630, 1237, 16384⟩ := by
  decide +kernel

theorem context_13_108630_369422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108630 ⟨369422, by decide⟩ :=
  accepted_of_selected 13 108630 ⟨369422, by decide⟩ ⟨13, 2, 0, 369422, 108630, 1237, 16384⟩
    (by decide) selected_cut_14241

theorem selected_cut_14242 : selected 8 ⟨369433, by decide⟩
    (prefixPartial 13 108631) = some ⟨13, 2, 0, 369433, 108631, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_108631_369433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108631 ⟨369433, by decide⟩ :=
  accepted_of_selected 13 108631 ⟨369433, by decide⟩ ⟨13, 2, 0, 369433, 108631, 1073, 16384⟩
    (by decide) selected_cut_14242

theorem unmarked_context_12_27157_369434 : frontier 9 ⟨369434, by decide⟩
    (prefixCache 12 27157) (prefixPartial 12 27157) = false := by
  decide +kernel

theorem node_context_12_27157_369434 : EJMOriginalGlobalDAGData.nodes 9 ⟨369434, by decide⟩ =
    .split (coordinate 12) (![⟨369381, by decide⟩,⟨369406, by decide⟩,⟨369422, by decide⟩,⟨369433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27157_369434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27157 ⟨369434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27157
    ⟨369434, by decide⟩ (by decide) (![⟨369381, by decide⟩,⟨369406, by decide⟩,⟨369422, by decide⟩,⟨369433, by decide⟩]) unmarked_context_12_27157_369434 node_context_12_27157_369434
  intro a
  fin_cases a
  · exact context_13_108628_369381
  · exact context_13_108629_369406
  · exact context_13_108630_369422
  · exact context_13_108631_369433

theorem selected_cut_14243 : selected 8 ⟨369456, by decide⟩
    (prefixPartial 13 108632) = some ⟨13, 2, 0, 369456, 108632, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_108632_369456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108632 ⟨369456, by decide⟩ :=
  accepted_of_selected 13 108632 ⟨369456, by decide⟩ ⟨13, 2, 0, 369456, 108632, 1977, 16384⟩
    (by decide) selected_cut_14243

theorem selected_cut_14244 : selected 8 ⟨369480, by decide⟩
    (prefixPartial 13 108633) = some ⟨13, 2, 0, 369480, 108633, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_108633_369480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108633 ⟨369480, by decide⟩ :=
  accepted_of_selected 13 108633 ⟨369480, by decide⟩ ⟨13, 2, 0, 369480, 108633, 2189, 16384⟩
    (by decide) selected_cut_14244

theorem selected_cut_14245 : selected 8 ⟨369498, by decide⟩
    (prefixPartial 13 108634) = some ⟨13, 2, 0, 369498, 108634, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_108634_369498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108634 ⟨369498, by decide⟩ :=
  accepted_of_selected 13 108634 ⟨369498, by decide⟩ ⟨13, 2, 0, 369498, 108634, 1329, 16384⟩
    (by decide) selected_cut_14245

theorem selected_cut_14246 : selected 8 ⟨369509, by decide⟩
    (prefixPartial 13 108635) = some ⟨13, 2, 0, 369509, 108635, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_108635_369509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108635 ⟨369509, by decide⟩ :=
  accepted_of_selected 13 108635 ⟨369509, by decide⟩ ⟨13, 2, 0, 369509, 108635, 1045, 16384⟩
    (by decide) selected_cut_14246

theorem unmarked_context_12_27158_369510 : frontier 9 ⟨369510, by decide⟩
    (prefixCache 12 27158) (prefixPartial 12 27158) = false := by
  decide +kernel

theorem node_context_12_27158_369510 : EJMOriginalGlobalDAGData.nodes 9 ⟨369510, by decide⟩ =
    .split (coordinate 12) (![⟨369456, by decide⟩,⟨369480, by decide⟩,⟨369498, by decide⟩,⟨369509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27158_369510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27158 ⟨369510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27158
    ⟨369510, by decide⟩ (by decide) (![⟨369456, by decide⟩,⟨369480, by decide⟩,⟨369498, by decide⟩,⟨369509, by decide⟩]) unmarked_context_12_27158_369510 node_context_12_27158_369510
  intro a
  fin_cases a
  · exact context_13_108632_369456
  · exact context_13_108633_369480
  · exact context_13_108634_369498
  · exact context_13_108635_369509

theorem selected_cut_14247 : selected 8 ⟨369542, by decide⟩
    (prefixPartial 13 108636) = some ⟨13, 2, 0, 369542, 108636, 2633, 16384⟩ := by
  decide +kernel

theorem context_13_108636_369542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108636 ⟨369542, by decide⟩ :=
  accepted_of_selected 13 108636 ⟨369542, by decide⟩ ⟨13, 2, 0, 369542, 108636, 2633, 16384⟩
    (by decide) selected_cut_14247

theorem selected_cut_14248 : selected 8 ⟨369570, by decide⟩
    (prefixPartial 13 108637) = some ⟨13, 2, 0, 369570, 108637, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_108637_369570 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108637 ⟨369570, by decide⟩ :=
  accepted_of_selected 13 108637 ⟨369570, by decide⟩ ⟨13, 2, 0, 369570, 108637, 2645, 16384⟩
    (by decide) selected_cut_14248

theorem selected_cut_14249 : selected 8 ⟨369589, by decide⟩
    (prefixPartial 13 108638) = some ⟨13, 2, 0, 369589, 108638, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_108638_369589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108638 ⟨369589, by decide⟩ :=
  accepted_of_selected 13 108638 ⟨369589, by decide⟩ ⟨13, 2, 0, 369589, 108638, 1405, 16384⟩
    (by decide) selected_cut_14249

theorem selected_cut_14250 : selected 8 ⟨369599, by decide⟩
    (prefixPartial 13 108639) = some ⟨13, 2, 0, 369599, 108639, 1189, 16384⟩ := by
  decide +kernel

theorem context_13_108639_369599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108639 ⟨369599, by decide⟩ :=
  accepted_of_selected 13 108639 ⟨369599, by decide⟩ ⟨13, 2, 0, 369599, 108639, 1189, 16384⟩
    (by decide) selected_cut_14250

theorem unmarked_context_12_27159_369600 : frontier 9 ⟨369600, by decide⟩
    (prefixCache 12 27159) (prefixPartial 12 27159) = false := by
  decide +kernel

theorem node_context_12_27159_369600 : EJMOriginalGlobalDAGData.nodes 9 ⟨369600, by decide⟩ =
    .split (coordinate 12) (![⟨369542, by decide⟩,⟨369570, by decide⟩,⟨369589, by decide⟩,⟨369599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27159_369600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27159 ⟨369600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27159
    ⟨369600, by decide⟩ (by decide) (![⟨369542, by decide⟩,⟨369570, by decide⟩,⟨369589, by decide⟩,⟨369599, by decide⟩]) unmarked_context_12_27159_369600 node_context_12_27159_369600
  intro a
  fin_cases a
  · exact context_13_108636_369542
  · exact context_13_108637_369570
  · exact context_13_108638_369589
  · exact context_13_108639_369599

theorem unmarked_context_11_6789_369601 : frontier 10 ⟨369601, by decide⟩
    (prefixCache 11 6789) (prefixPartial 11 6789) = false := by
  decide +kernel

theorem node_context_11_6789_369601 : EJMOriginalGlobalDAGData.nodes 10 ⟨369601, by decide⟩ =
    .split (coordinate 11) (![⟨369349, by decide⟩,⟨369434, by decide⟩,⟨369510, by decide⟩,⟨369600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6789_369601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6789 ⟨369601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6789
    ⟨369601, by decide⟩ (by decide) (![⟨369349, by decide⟩,⟨369434, by decide⟩,⟨369510, by decide⟩,⟨369600, by decide⟩]) unmarked_context_11_6789_369601 node_context_11_6789_369601
  intro a
  fin_cases a
  · exact context_12_27156_369349
  · exact context_12_27157_369434
  · exact context_12_27158_369510
  · exact context_12_27159_369600

theorem selected_cut_14251 : selected 8 ⟨369620, by decide⟩
    (prefixPartial 13 108640) = some ⟨13, 2, 0, 369620, 108640, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_108640_369620 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108640 ⟨369620, by decide⟩ :=
  accepted_of_selected 13 108640 ⟨369620, by decide⟩ ⟨13, 2, 0, 369620, 108640, 1477, 16384⟩
    (by decide) selected_cut_14251

theorem selected_cut_14252 : selected 8 ⟨369653, by decide⟩
    (prefixPartial 13 108641) = some ⟨13, 2, 0, 369653, 108641, 2053, 16384⟩ := by
  decide +kernel

theorem context_13_108641_369653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108641 ⟨369653, by decide⟩ :=
  accepted_of_selected 13 108641 ⟨369653, by decide⟩ ⟨13, 2, 0, 369653, 108641, 2053, 16384⟩
    (by decide) selected_cut_14252

theorem selected_cut_14253 : selected 8 ⟨369667, by decide⟩
    (prefixPartial 13 108642) = some ⟨13, 2, 0, 369667, 108642, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_108642_369667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108642 ⟨369667, by decide⟩ :=
  accepted_of_selected 13 108642 ⟨369667, by decide⟩ ⟨13, 2, 0, 369667, 108642, 1009, 16384⟩
    (by decide) selected_cut_14253

theorem selected_cut_14254 : selected 8 ⟨369677, by decide⟩
    (prefixPartial 13 108643) = some ⟨13, 2, 0, 369677, 108643, 845, 16384⟩ := by
  decide +kernel

theorem context_13_108643_369677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108643 ⟨369677, by decide⟩ :=
  accepted_of_selected 13 108643 ⟨369677, by decide⟩ ⟨13, 2, 0, 369677, 108643, 845, 16384⟩
    (by decide) selected_cut_14254

theorem unmarked_context_12_27160_369678 : frontier 9 ⟨369678, by decide⟩
    (prefixCache 12 27160) (prefixPartial 12 27160) = false := by
  decide +kernel

theorem node_context_12_27160_369678 : EJMOriginalGlobalDAGData.nodes 9 ⟨369678, by decide⟩ =
    .split (coordinate 12) (![⟨369620, by decide⟩,⟨369653, by decide⟩,⟨369667, by decide⟩,⟨369677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27160_369678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27160 ⟨369678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27160
    ⟨369678, by decide⟩ (by decide) (![⟨369620, by decide⟩,⟨369653, by decide⟩,⟨369667, by decide⟩,⟨369677, by decide⟩]) unmarked_context_12_27160_369678 node_context_12_27160_369678
  intro a
  fin_cases a
  · exact context_13_108640_369620
  · exact context_13_108641_369653
  · exact context_13_108642_369667
  · exact context_13_108643_369677

theorem selected_cut_14255 : selected 8 ⟨369704, by decide⟩
    (prefixPartial 13 108644) = some ⟨13, 2, 0, 369704, 108644, 1613, 16384⟩ := by
  decide +kernel

theorem context_13_108644_369704 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108644 ⟨369704, by decide⟩ :=
  accepted_of_selected 13 108644 ⟨369704, by decide⟩ ⟨13, 2, 0, 369704, 108644, 1613, 16384⟩
    (by decide) selected_cut_14255

theorem selected_cut_14256 : selected 8 ⟨369727, by decide⟩
    (prefixPartial 13 108645) = some ⟨13, 2, 0, 369727, 108645, 1961, 16384⟩ := by
  decide +kernel

theorem context_13_108645_369727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108645 ⟨369727, by decide⟩ :=
  accepted_of_selected 13 108645 ⟨369727, by decide⟩ ⟨13, 2, 0, 369727, 108645, 1961, 16384⟩
    (by decide) selected_cut_14256

theorem selected_cut_14257 : selected 8 ⟨369741, by decide⟩
    (prefixPartial 13 108646) = some ⟨13, 2, 0, 369741, 108646, 1177, 16384⟩ := by
  decide +kernel

theorem context_13_108646_369741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108646 ⟨369741, by decide⟩ :=
  accepted_of_selected 13 108646 ⟨369741, by decide⟩ ⟨13, 2, 0, 369741, 108646, 1177, 16384⟩
    (by decide) selected_cut_14257

theorem selected_cut_14258 : selected 8 ⟨369749, by decide⟩
    (prefixPartial 13 108647) = some ⟨13, 2, 0, 369749, 108647, 837, 16384⟩ := by
  decide +kernel

theorem context_13_108647_369749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108647 ⟨369749, by decide⟩ :=
  accepted_of_selected 13 108647 ⟨369749, by decide⟩ ⟨13, 2, 0, 369749, 108647, 837, 16384⟩
    (by decide) selected_cut_14258

theorem unmarked_context_12_27161_369750 : frontier 9 ⟨369750, by decide⟩
    (prefixCache 12 27161) (prefixPartial 12 27161) = false := by
  decide +kernel

theorem node_context_12_27161_369750 : EJMOriginalGlobalDAGData.nodes 9 ⟨369750, by decide⟩ =
    .split (coordinate 12) (![⟨369704, by decide⟩,⟨369727, by decide⟩,⟨369741, by decide⟩,⟨369749, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27161_369750 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27161 ⟨369750, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27161
    ⟨369750, by decide⟩ (by decide) (![⟨369704, by decide⟩,⟨369727, by decide⟩,⟨369741, by decide⟩,⟨369749, by decide⟩]) unmarked_context_12_27161_369750 node_context_12_27161_369750
  intro a
  fin_cases a
  · exact context_13_108644_369704
  · exact context_13_108645_369727
  · exact context_13_108646_369741
  · exact context_13_108647_369749

theorem selected_cut_14259 : selected 8 ⟨369786, by decide⟩
    (prefixPartial 13 108648) = some ⟨13, 2, 0, 369786, 108648, 2441, 16384⟩ := by
  decide +kernel

theorem context_13_108648_369786 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108648 ⟨369786, by decide⟩ :=
  accepted_of_selected 13 108648 ⟨369786, by decide⟩ ⟨13, 2, 0, 369786, 108648, 2441, 16384⟩
    (by decide) selected_cut_14259

theorem selected_cut_14260 : selected 8 ⟨369834, by decide⟩
    (prefixPartial 13 108649) = some ⟨13, 2, 0, 369834, 108649, 3485, 16384⟩ := by
  decide +kernel

theorem context_13_108649_369834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108649 ⟨369834, by decide⟩ :=
  accepted_of_selected 13 108649 ⟨369834, by decide⟩ ⟨13, 2, 0, 369834, 108649, 3485, 16384⟩
    (by decide) selected_cut_14260

theorem selected_cut_14261 : selected 8 ⟨369856, by decide⟩
    (prefixPartial 13 108650) = some ⟨13, 2, 0, 369856, 108650, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_108650_369856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108650 ⟨369856, by decide⟩ :=
  accepted_of_selected 13 108650 ⟨369856, by decide⟩ ⟨13, 2, 0, 369856, 108650, 2057, 16384⟩
    (by decide) selected_cut_14261

theorem selected_cut_14262 : selected 8 ⟨369863, by decide⟩
    (prefixPartial 13 108651) = some ⟨13, 2, 0, 369863, 108651, 1153, 16384⟩ := by
  decide +kernel

theorem context_13_108651_369863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108651 ⟨369863, by decide⟩ :=
  accepted_of_selected 13 108651 ⟨369863, by decide⟩ ⟨13, 2, 0, 369863, 108651, 1153, 16384⟩
    (by decide) selected_cut_14262

theorem unmarked_context_12_27162_369864 : frontier 9 ⟨369864, by decide⟩
    (prefixCache 12 27162) (prefixPartial 12 27162) = false := by
  decide +kernel

theorem node_context_12_27162_369864 : EJMOriginalGlobalDAGData.nodes 9 ⟨369864, by decide⟩ =
    .split (coordinate 12) (![⟨369786, by decide⟩,⟨369834, by decide⟩,⟨369856, by decide⟩,⟨369863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27162_369864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27162 ⟨369864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27162
    ⟨369864, by decide⟩ (by decide) (![⟨369786, by decide⟩,⟨369834, by decide⟩,⟨369856, by decide⟩,⟨369863, by decide⟩]) unmarked_context_12_27162_369864 node_context_12_27162_369864
  intro a
  fin_cases a
  · exact context_13_108648_369786
  · exact context_13_108649_369834
  · exact context_13_108650_369856
  · exact context_13_108651_369863

theorem selected_cut_14263 : selected 8 ⟨369892, by decide⟩
    (prefixPartial 13 108652) = some ⟨13, 2, 0, 369892, 108652, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_108652_369892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108652 ⟨369892, by decide⟩ :=
  accepted_of_selected 13 108652 ⟨369892, by decide⟩ ⟨13, 2, 0, 369892, 108652, 1793, 16384⟩
    (by decide) selected_cut_14263

theorem selected_cut_14264 : selected 8 ⟨369923, by decide⟩
    (prefixPartial 13 108653) = some ⟨13, 2, 0, 369923, 108653, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_108653_369923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108653 ⟨369923, by decide⟩ :=
  accepted_of_selected 13 108653 ⟨369923, by decide⟩ ⟨13, 2, 0, 369923, 108653, 2577, 16384⟩
    (by decide) selected_cut_14264

theorem selected_cut_14265 : selected 8 ⟨369942, by decide⟩
    (prefixPartial 13 108654) = some ⟨13, 2, 0, 369942, 108654, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_108654_369942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108654 ⟨369942, by decide⟩ :=
  accepted_of_selected 13 108654 ⟨369942, by decide⟩ ⟨13, 2, 0, 369942, 108654, 1241, 16384⟩
    (by decide) selected_cut_14265

theorem selected_cut_14266 : selected 8 ⟨369952, by decide⟩
    (prefixPartial 13 108655) = some ⟨13, 2, 0, 369952, 108655, 961, 16384⟩ := by
  decide +kernel

theorem context_13_108655_369952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108655 ⟨369952, by decide⟩ :=
  accepted_of_selected 13 108655 ⟨369952, by decide⟩ ⟨13, 2, 0, 369952, 108655, 961, 16384⟩
    (by decide) selected_cut_14266

theorem unmarked_context_12_27163_369953 : frontier 9 ⟨369953, by decide⟩
    (prefixCache 12 27163) (prefixPartial 12 27163) = false := by
  decide +kernel

theorem node_context_12_27163_369953 : EJMOriginalGlobalDAGData.nodes 9 ⟨369953, by decide⟩ =
    .split (coordinate 12) (![⟨369892, by decide⟩,⟨369923, by decide⟩,⟨369942, by decide⟩,⟨369952, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27163_369953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27163 ⟨369953, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27163
    ⟨369953, by decide⟩ (by decide) (![⟨369892, by decide⟩,⟨369923, by decide⟩,⟨369942, by decide⟩,⟨369952, by decide⟩]) unmarked_context_12_27163_369953 node_context_12_27163_369953
  intro a
  fin_cases a
  · exact context_13_108652_369892
  · exact context_13_108653_369923
  · exact context_13_108654_369942
  · exact context_13_108655_369952

theorem unmarked_context_11_6790_369954 : frontier 10 ⟨369954, by decide⟩
    (prefixCache 11 6790) (prefixPartial 11 6790) = false := by
  decide +kernel

theorem node_context_11_6790_369954 : EJMOriginalGlobalDAGData.nodes 10 ⟨369954, by decide⟩ =
    .split (coordinate 11) (![⟨369678, by decide⟩,⟨369750, by decide⟩,⟨369864, by decide⟩,⟨369953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6790_369954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6790 ⟨369954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6790
    ⟨369954, by decide⟩ (by decide) (![⟨369678, by decide⟩,⟨369750, by decide⟩,⟨369864, by decide⟩,⟨369953, by decide⟩]) unmarked_context_11_6790_369954 node_context_11_6790_369954
  intro a
  fin_cases a
  · exact context_12_27160_369678
  · exact context_12_27161_369750
  · exact context_12_27162_369864
  · exact context_12_27163_369953

theorem selected_cut_14267 : selected 8 ⟨369973, by decide⟩
    (prefixPartial 13 108656) = some ⟨13, 2, 0, 369973, 108656, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_108656_369973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108656 ⟨369973, by decide⟩ :=
  accepted_of_selected 13 108656 ⟨369973, by decide⟩ ⟨13, 2, 0, 369973, 108656, 1485, 16384⟩
    (by decide) selected_cut_14267

theorem selected_cut_14268 : selected 8 ⟨370003, by decide⟩
    (prefixPartial 13 108657) = some ⟨13, 2, 0, 370003, 108657, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_108657_370003 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108657 ⟨370003, by decide⟩ :=
  accepted_of_selected 13 108657 ⟨370003, by decide⟩ ⟨13, 2, 0, 370003, 108657, 2337, 16384⟩
    (by decide) selected_cut_14268

theorem selected_cut_14269 : selected 8 ⟨370018, by decide⟩
    (prefixPartial 13 108658) = some ⟨13, 2, 0, 370018, 108658, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_108658_370018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108658 ⟨370018, by decide⟩ :=
  accepted_of_selected 13 108658 ⟨370018, by decide⟩ ⟨13, 2, 0, 370018, 108658, 1109, 16384⟩
    (by decide) selected_cut_14269

theorem selected_cut_14270 : selected 8 ⟨370026, by decide⟩
    (prefixPartial 13 108659) = some ⟨13, 2, 0, 370026, 108659, 873, 16384⟩ := by
  decide +kernel

theorem context_13_108659_370026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108659 ⟨370026, by decide⟩ :=
  accepted_of_selected 13 108659 ⟨370026, by decide⟩ ⟨13, 2, 0, 370026, 108659, 873, 16384⟩
    (by decide) selected_cut_14270

theorem unmarked_context_12_27164_370027 : frontier 9 ⟨370027, by decide⟩
    (prefixCache 12 27164) (prefixPartial 12 27164) = false := by
  decide +kernel

theorem node_context_12_27164_370027 : EJMOriginalGlobalDAGData.nodes 9 ⟨370027, by decide⟩ =
    .split (coordinate 12) (![⟨369973, by decide⟩,⟨370003, by decide⟩,⟨370018, by decide⟩,⟨370026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27164_370027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27164 ⟨370027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27164
    ⟨370027, by decide⟩ (by decide) (![⟨369973, by decide⟩,⟨370003, by decide⟩,⟨370018, by decide⟩,⟨370026, by decide⟩]) unmarked_context_12_27164_370027 node_context_12_27164_370027
  intro a
  fin_cases a
  · exact context_13_108656_369973
  · exact context_13_108657_370003
  · exact context_13_108658_370018
  · exact context_13_108659_370026

theorem selected_cut_14271 : selected 8 ⟨370054, by decide⟩
    (prefixPartial 13 108660) = some ⟨13, 2, 0, 370054, 108660, 1893, 16384⟩ := by
  decide +kernel

theorem context_13_108660_370054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108660 ⟨370054, by decide⟩ :=
  accepted_of_selected 13 108660 ⟨370054, by decide⟩ ⟨13, 2, 0, 370054, 108660, 1893, 16384⟩
    (by decide) selected_cut_14271

theorem selected_cut_14272 : selected 8 ⟨370084, by decide⟩
    (prefixPartial 13 108661) = some ⟨13, 2, 0, 370084, 108661, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_108661_370084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108661 ⟨370084, by decide⟩ :=
  accepted_of_selected 13 108661 ⟨370084, by decide⟩ ⟨13, 2, 0, 370084, 108661, 2309, 16384⟩
    (by decide) selected_cut_14272

theorem selected_cut_14273 : selected 8 ⟨370098, by decide⟩
    (prefixPartial 13 108662) = some ⟨13, 2, 0, 370098, 108662, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_108662_370098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108662 ⟨370098, by decide⟩ :=
  accepted_of_selected 13 108662 ⟨370098, by decide⟩ ⟨13, 2, 0, 370098, 108662, 1161, 16384⟩
    (by decide) selected_cut_14273

theorem selected_cut_14274 : selected 8 ⟨370103, by decide⟩
    (prefixPartial 13 108663) = some ⟨13, 2, 0, 370103, 108663, 789, 16384⟩ := by
  decide +kernel

theorem context_13_108663_370103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108663 ⟨370103, by decide⟩ :=
  accepted_of_selected 13 108663 ⟨370103, by decide⟩ ⟨13, 2, 0, 370103, 108663, 789, 16384⟩
    (by decide) selected_cut_14274

theorem unmarked_context_12_27165_370104 : frontier 9 ⟨370104, by decide⟩
    (prefixCache 12 27165) (prefixPartial 12 27165) = false := by
  decide +kernel

theorem node_context_12_27165_370104 : EJMOriginalGlobalDAGData.nodes 9 ⟨370104, by decide⟩ =
    .split (coordinate 12) (![⟨370054, by decide⟩,⟨370084, by decide⟩,⟨370098, by decide⟩,⟨370103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27165_370104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27165 ⟨370104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27165
    ⟨370104, by decide⟩ (by decide) (![⟨370054, by decide⟩,⟨370084, by decide⟩,⟨370098, by decide⟩,⟨370103, by decide⟩]) unmarked_context_12_27165_370104 node_context_12_27165_370104
  intro a
  fin_cases a
  · exact context_13_108660_370054
  · exact context_13_108661_370084
  · exact context_13_108662_370098
  · exact context_13_108663_370103

theorem selected_cut_14275 : selected 8 ⟨370121, by decide⟩
    (prefixPartial 13 108664) = some ⟨13, 2, 0, 370121, 108664, 1405, 16384⟩ := by
  decide +kernel

theorem context_13_108664_370121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108664 ⟨370121, by decide⟩ :=
  accepted_of_selected 13 108664 ⟨370121, by decide⟩ ⟨13, 2, 0, 370121, 108664, 1405, 16384⟩
    (by decide) selected_cut_14275

theorem selected_cut_14276 : selected 8 ⟨370152, by decide⟩
    (prefixPartial 13 108665) = some ⟨13, 2, 0, 370152, 108665, 2337, 16384⟩ := by
  decide +kernel

theorem context_13_108665_370152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108665 ⟨370152, by decide⟩ :=
  accepted_of_selected 13 108665 ⟨370152, by decide⟩ ⟨13, 2, 0, 370152, 108665, 2337, 16384⟩
    (by decide) selected_cut_14276

theorem selected_cut_14277 : selected 8 ⟨370169, by decide⟩
    (prefixPartial 13 108666) = some ⟨13, 2, 0, 370169, 108666, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_108666_370169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108666 ⟨370169, by decide⟩ :=
  accepted_of_selected 13 108666 ⟨370169, by decide⟩ ⟨13, 2, 0, 370169, 108666, 1213, 16384⟩
    (by decide) selected_cut_14277

theorem selected_cut_14278 : selected 8 ⟨370176, by decide⟩
    (prefixPartial 13 108667) = some ⟨13, 2, 0, 370176, 108667, 761, 16384⟩ := by
  decide +kernel

theorem context_13_108667_370176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108667 ⟨370176, by decide⟩ :=
  accepted_of_selected 13 108667 ⟨370176, by decide⟩ ⟨13, 2, 0, 370176, 108667, 761, 16384⟩
    (by decide) selected_cut_14278

theorem unmarked_context_12_27166_370177 : frontier 9 ⟨370177, by decide⟩
    (prefixCache 12 27166) (prefixPartial 12 27166) = false := by
  decide +kernel

theorem node_context_12_27166_370177 : EJMOriginalGlobalDAGData.nodes 9 ⟨370177, by decide⟩ =
    .split (coordinate 12) (![⟨370121, by decide⟩,⟨370152, by decide⟩,⟨370169, by decide⟩,⟨370176, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27166_370177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27166 ⟨370177, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27166
    ⟨370177, by decide⟩ (by decide) (![⟨370121, by decide⟩,⟨370152, by decide⟩,⟨370169, by decide⟩,⟨370176, by decide⟩]) unmarked_context_12_27166_370177 node_context_12_27166_370177
  intro a
  fin_cases a
  · exact context_13_108664_370121
  · exact context_13_108665_370152
  · exact context_13_108666_370169
  · exact context_13_108667_370176

theorem selected_cut_14279 : selected 8 ⟨370207, by decide⟩
    (prefixPartial 13 108668) = some ⟨13, 2, 0, 370207, 108668, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_108668_370207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108668 ⟨370207, by decide⟩ :=
  accepted_of_selected 13 108668 ⟨370207, by decide⟩ ⟨13, 2, 0, 370207, 108668, 1929, 16384⟩
    (by decide) selected_cut_14279

theorem selected_cut_14280 : selected 8 ⟨370243, by decide⟩
    (prefixPartial 13 108669) = some ⟨13, 2, 0, 370243, 108669, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_108669_370243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108669 ⟨370243, by decide⟩ :=
  accepted_of_selected 13 108669 ⟨370243, by decide⟩ ⟨13, 2, 0, 370243, 108669, 2577, 16384⟩
    (by decide) selected_cut_14280

theorem selected_cut_14281 : selected 8 ⟨370258, by decide⟩
    (prefixPartial 13 108670) = some ⟨13, 2, 0, 370258, 108670, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_108670_370258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108670 ⟨370258, by decide⟩ :=
  accepted_of_selected 13 108670 ⟨370258, by decide⟩ ⟨13, 2, 0, 370258, 108670, 1301, 16384⟩
    (by decide) selected_cut_14281

theorem selected_cut_14282 : selected 8 ⟨370265, by decide⟩
    (prefixPartial 13 108671) = some ⟨13, 2, 0, 370265, 108671, 917, 16384⟩ := by
  decide +kernel

theorem context_13_108671_370265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108671 ⟨370265, by decide⟩ :=
  accepted_of_selected 13 108671 ⟨370265, by decide⟩ ⟨13, 2, 0, 370265, 108671, 917, 16384⟩
    (by decide) selected_cut_14282

theorem unmarked_context_12_27167_370266 : frontier 9 ⟨370266, by decide⟩
    (prefixCache 12 27167) (prefixPartial 12 27167) = false := by
  decide +kernel

theorem node_context_12_27167_370266 : EJMOriginalGlobalDAGData.nodes 9 ⟨370266, by decide⟩ =
    .split (coordinate 12) (![⟨370207, by decide⟩,⟨370243, by decide⟩,⟨370258, by decide⟩,⟨370265, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27167_370266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27167 ⟨370266, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27167
    ⟨370266, by decide⟩ (by decide) (![⟨370207, by decide⟩,⟨370243, by decide⟩,⟨370258, by decide⟩,⟨370265, by decide⟩]) unmarked_context_12_27167_370266 node_context_12_27167_370266
  intro a
  fin_cases a
  · exact context_13_108668_370207
  · exact context_13_108669_370243
  · exact context_13_108670_370258
  · exact context_13_108671_370265

theorem unmarked_context_11_6791_370267 : frontier 10 ⟨370267, by decide⟩
    (prefixCache 11 6791) (prefixPartial 11 6791) = false := by
  decide +kernel

theorem node_context_11_6791_370267 : EJMOriginalGlobalDAGData.nodes 10 ⟨370267, by decide⟩ =
    .split (coordinate 11) (![⟨370027, by decide⟩,⟨370104, by decide⟩,⟨370177, by decide⟩,⟨370266, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6791_370267 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6791 ⟨370267, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6791
    ⟨370267, by decide⟩ (by decide) (![⟨370027, by decide⟩,⟨370104, by decide⟩,⟨370177, by decide⟩,⟨370266, by decide⟩]) unmarked_context_11_6791_370267 node_context_11_6791_370267
  intro a
  fin_cases a
  · exact context_12_27164_370027
  · exact context_12_27165_370104
  · exact context_12_27166_370177
  · exact context_12_27167_370266

theorem unmarked_context_10_1697_370268 : frontier 11 ⟨370268, by decide⟩
    (prefixCache 10 1697) (prefixPartial 10 1697) = false := by
  decide +kernel

theorem node_context_10_1697_370268 : EJMOriginalGlobalDAGData.nodes 11 ⟨370268, by decide⟩ =
    .split (coordinate 10) (![⟨369275, by decide⟩,⟨369601, by decide⟩,⟨369954, by decide⟩,⟨370267, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1697_370268 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1697 ⟨370268, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1697
    ⟨370268, by decide⟩ (by decide) (![⟨369275, by decide⟩,⟨369601, by decide⟩,⟨369954, by decide⟩,⟨370267, by decide⟩]) unmarked_context_10_1697_370268 node_context_10_1697_370268
  intro a
  fin_cases a
  · exact context_11_6788_369275
  · exact context_11_6789_369601
  · exact context_11_6790_369954
  · exact context_11_6791_370267

theorem selected_cut_14283 : selected 8 ⟨370281, by decide⟩
    (prefixPartial 13 108672) = some ⟨13, 2, 0, 370281, 108672, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_108672_370281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108672 ⟨370281, by decide⟩ :=
  accepted_of_selected 13 108672 ⟨370281, by decide⟩ ⟨13, 2, 0, 370281, 108672, 1161, 16384⟩
    (by decide) selected_cut_14283

theorem selected_cut_14284 : selected 8 ⟨370302, by decide⟩
    (prefixPartial 13 108673) = some ⟨13, 2, 0, 370302, 108673, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_108673_370302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108673 ⟨370302, by decide⟩ :=
  accepted_of_selected 13 108673 ⟨370302, by decide⟩ ⟨13, 2, 0, 370302, 108673, 1973, 16384⟩
    (by decide) selected_cut_14284

theorem selected_cut_14285 : selected 8 ⟨370316, by decide⟩
    (prefixPartial 13 108674) = some ⟨13, 2, 0, 370316, 108674, 937, 16384⟩ := by
  decide +kernel

theorem context_13_108674_370316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108674 ⟨370316, by decide⟩ :=
  accepted_of_selected 13 108674 ⟨370316, by decide⟩ ⟨13, 2, 0, 370316, 108674, 937, 16384⟩
    (by decide) selected_cut_14285

theorem selected_cut_14286 : selected 8 ⟨370323, by decide⟩
    (prefixPartial 13 108675) = some ⟨13, 2, 0, 370323, 108675, 753, 16384⟩ := by
  decide +kernel

theorem context_13_108675_370323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108675 ⟨370323, by decide⟩ :=
  accepted_of_selected 13 108675 ⟨370323, by decide⟩ ⟨13, 2, 0, 370323, 108675, 753, 16384⟩
    (by decide) selected_cut_14286

theorem unmarked_context_12_27168_370324 : frontier 9 ⟨370324, by decide⟩
    (prefixCache 12 27168) (prefixPartial 12 27168) = false := by
  decide +kernel

theorem node_context_12_27168_370324 : EJMOriginalGlobalDAGData.nodes 9 ⟨370324, by decide⟩ =
    .split (coordinate 12) (![⟨370281, by decide⟩,⟨370302, by decide⟩,⟨370316, by decide⟩,⟨370323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27168_370324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27168 ⟨370324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27168
    ⟨370324, by decide⟩ (by decide) (![⟨370281, by decide⟩,⟨370302, by decide⟩,⟨370316, by decide⟩,⟨370323, by decide⟩]) unmarked_context_12_27168_370324 node_context_12_27168_370324
  intro a
  fin_cases a
  · exact context_13_108672_370281
  · exact context_13_108673_370302
  · exact context_13_108674_370316
  · exact context_13_108675_370323

theorem selected_cut_14287 : selected 8 ⟨370336, by decide⟩
    (prefixPartial 13 108676) = some ⟨13, 2, 0, 370336, 108676, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_108676_370336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108676 ⟨370336, by decide⟩ :=
  accepted_of_selected 13 108676 ⟨370336, by decide⟩ ⟨13, 2, 0, 370336, 108676, 1281, 16384⟩
    (by decide) selected_cut_14287

theorem selected_cut_14288 : selected 8 ⟨370365, by decide⟩
    (prefixPartial 13 108677) = some ⟨13, 2, 0, 370365, 108677, 2193, 16384⟩ := by
  decide +kernel

theorem context_13_108677_370365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108677 ⟨370365, by decide⟩ :=
  accepted_of_selected 13 108677 ⟨370365, by decide⟩ ⟨13, 2, 0, 370365, 108677, 2193, 16384⟩
    (by decide) selected_cut_14288

theorem selected_cut_14289 : selected 8 ⟨370379, by decide⟩
    (prefixPartial 13 108678) = some ⟨13, 2, 0, 370379, 108678, 1073, 16384⟩ := by
  decide +kernel

theorem context_13_108678_370379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108678 ⟨370379, by decide⟩ :=
  accepted_of_selected 13 108678 ⟨370379, by decide⟩ ⟨13, 2, 0, 370379, 108678, 1073, 16384⟩
    (by decide) selected_cut_14289

theorem selected_cut_14290 : selected 8 ⟨370384, by decide⟩
    (prefixPartial 13 108679) = some ⟨13, 2, 0, 370384, 108679, 809, 16384⟩ := by
  decide +kernel

theorem context_13_108679_370384 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108679 ⟨370384, by decide⟩ :=
  accepted_of_selected 13 108679 ⟨370384, by decide⟩ ⟨13, 2, 0, 370384, 108679, 809, 16384⟩
    (by decide) selected_cut_14290

theorem unmarked_context_12_27169_370385 : frontier 9 ⟨370385, by decide⟩
    (prefixCache 12 27169) (prefixPartial 12 27169) = false := by
  decide +kernel

theorem node_context_12_27169_370385 : EJMOriginalGlobalDAGData.nodes 9 ⟨370385, by decide⟩ =
    .split (coordinate 12) (![⟨370336, by decide⟩,⟨370365, by decide⟩,⟨370379, by decide⟩,⟨370384, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27169_370385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27169 ⟨370385, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27169
    ⟨370385, by decide⟩ (by decide) (![⟨370336, by decide⟩,⟨370365, by decide⟩,⟨370379, by decide⟩,⟨370384, by decide⟩]) unmarked_context_12_27169_370385 node_context_12_27169_370385
  intro a
  fin_cases a
  · exact context_13_108676_370336
  · exact context_13_108677_370365
  · exact context_13_108678_370379
  · exact context_13_108679_370384

theorem selected_cut_14291 : selected 8 ⟨370398, by decide⟩
    (prefixPartial 13 108680) = some ⟨13, 2, 0, 370398, 108680, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_108680_370398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108680 ⟨370398, by decide⟩ :=
  accepted_of_selected 13 108680 ⟨370398, by decide⟩ ⟨13, 2, 0, 370398, 108680, 1025, 16384⟩
    (by decide) selected_cut_14291

theorem selected_cut_14292 : selected 8 ⟨370419, by decide⟩
    (prefixPartial 13 108681) = some ⟨13, 2, 0, 370419, 108681, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_108681_370419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108681 ⟨370419, by decide⟩ :=
  accepted_of_selected 13 108681 ⟨370419, by decide⟩ ⟨13, 2, 0, 370419, 108681, 1793, 16384⟩
    (by decide) selected_cut_14292

theorem selected_cut_14293 : selected 8 ⟨370431, by decide⟩
    (prefixPartial 13 108682) = some ⟨13, 2, 0, 370431, 108682, 777, 16384⟩ := by
  decide +kernel

theorem context_13_108682_370431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108682 ⟨370431, by decide⟩ :=
  accepted_of_selected 13 108682 ⟨370431, by decide⟩ ⟨13, 2, 0, 370431, 108682, 777, 16384⟩
    (by decide) selected_cut_14293

theorem selected_cut_14294 : selected 8 ⟨370437, by decide⟩
    (prefixPartial 13 108683) = some ⟨13, 2, 0, 370437, 108683, 741, 16384⟩ := by
  decide +kernel

theorem context_13_108683_370437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108683 ⟨370437, by decide⟩ :=
  accepted_of_selected 13 108683 ⟨370437, by decide⟩ ⟨13, 2, 0, 370437, 108683, 741, 16384⟩
    (by decide) selected_cut_14294

theorem unmarked_context_12_27170_370438 : frontier 9 ⟨370438, by decide⟩
    (prefixCache 12 27170) (prefixPartial 12 27170) = false := by
  decide +kernel

theorem node_context_12_27170_370438 : EJMOriginalGlobalDAGData.nodes 9 ⟨370438, by decide⟩ =
    .split (coordinate 12) (![⟨370398, by decide⟩,⟨370419, by decide⟩,⟨370431, by decide⟩,⟨370437, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27170_370438 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27170 ⟨370438, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27170
    ⟨370438, by decide⟩ (by decide) (![⟨370398, by decide⟩,⟨370419, by decide⟩,⟨370431, by decide⟩,⟨370437, by decide⟩]) unmarked_context_12_27170_370438 node_context_12_27170_370438
  intro a
  fin_cases a
  · exact context_13_108680_370398
  · exact context_13_108681_370419
  · exact context_13_108682_370431
  · exact context_13_108683_370437

theorem selected_cut_14295 : selected 8 ⟨370452, by decide⟩
    (prefixPartial 13 108684) = some ⟨13, 2, 0, 370452, 108684, 1349, 16384⟩ := by
  decide +kernel

theorem context_13_108684_370452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108684 ⟨370452, by decide⟩ :=
  accepted_of_selected 13 108684 ⟨370452, by decide⟩ ⟨13, 2, 0, 370452, 108684, 1349, 16384⟩
    (by decide) selected_cut_14295

theorem selected_cut_14296 : selected 8 ⟨370485, by decide⟩
    (prefixPartial 13 108685) = some ⟨13, 2, 0, 370485, 108685, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_108685_370485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108685 ⟨370485, by decide⟩ :=
  accepted_of_selected 13 108685 ⟨370485, by decide⟩ ⟨13, 2, 0, 370485, 108685, 2349, 16384⟩
    (by decide) selected_cut_14296

theorem selected_cut_14297 : selected 8 ⟨370499, by decide⟩
    (prefixPartial 13 108686) = some ⟨13, 2, 0, 370499, 108686, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_108686_370499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108686 ⟨370499, by decide⟩ :=
  accepted_of_selected 13 108686 ⟨370499, by decide⟩ ⟨13, 2, 0, 370499, 108686, 1161, 16384⟩
    (by decide) selected_cut_14297

theorem selected_cut_14298 : selected 8 ⟨370506, by decide⟩
    (prefixPartial 13 108687) = some ⟨13, 2, 0, 370506, 108687, 905, 16384⟩ := by
  decide +kernel

theorem context_13_108687_370506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108687 ⟨370506, by decide⟩ :=
  accepted_of_selected 13 108687 ⟨370506, by decide⟩ ⟨13, 2, 0, 370506, 108687, 905, 16384⟩
    (by decide) selected_cut_14298

theorem unmarked_context_12_27171_370507 : frontier 9 ⟨370507, by decide⟩
    (prefixCache 12 27171) (prefixPartial 12 27171) = false := by
  decide +kernel

theorem node_context_12_27171_370507 : EJMOriginalGlobalDAGData.nodes 9 ⟨370507, by decide⟩ =
    .split (coordinate 12) (![⟨370452, by decide⟩,⟨370485, by decide⟩,⟨370499, by decide⟩,⟨370506, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27171_370507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27171 ⟨370507, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27171
    ⟨370507, by decide⟩ (by decide) (![⟨370452, by decide⟩,⟨370485, by decide⟩,⟨370499, by decide⟩,⟨370506, by decide⟩]) unmarked_context_12_27171_370507 node_context_12_27171_370507
  intro a
  fin_cases a
  · exact context_13_108684_370452
  · exact context_13_108685_370485
  · exact context_13_108686_370499
  · exact context_13_108687_370506

theorem unmarked_context_11_6792_370508 : frontier 10 ⟨370508, by decide⟩
    (prefixCache 11 6792) (prefixPartial 11 6792) = false := by
  decide +kernel

theorem node_context_11_6792_370508 : EJMOriginalGlobalDAGData.nodes 10 ⟨370508, by decide⟩ =
    .split (coordinate 11) (![⟨370324, by decide⟩,⟨370385, by decide⟩,⟨370438, by decide⟩,⟨370507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6792_370508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6792 ⟨370508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6792
    ⟨370508, by decide⟩ (by decide) (![⟨370324, by decide⟩,⟨370385, by decide⟩,⟨370438, by decide⟩,⟨370507, by decide⟩]) unmarked_context_11_6792_370508 node_context_11_6792_370508
  intro a
  fin_cases a
  · exact context_12_27168_370324
  · exact context_12_27169_370385
  · exact context_12_27170_370438
  · exact context_12_27171_370507

theorem selected_cut_14299 : selected 8 ⟨370519, by decide⟩
    (prefixPartial 13 108688) = some ⟨13, 2, 0, 370519, 108688, 869, 16384⟩ := by
  decide +kernel

theorem context_13_108688_370519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108688 ⟨370519, by decide⟩ :=
  accepted_of_selected 13 108688 ⟨370519, by decide⟩ ⟨13, 2, 0, 370519, 108688, 869, 16384⟩
    (by decide) selected_cut_14299

theorem selected_cut_14300 : selected 8 ⟨370544, by decide⟩
    (prefixPartial 13 108689) = some ⟨13, 2, 0, 370544, 108689, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_108689_370544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108689 ⟨370544, by decide⟩ :=
  accepted_of_selected 13 108689 ⟨370544, by decide⟩ ⟨13, 2, 0, 370544, 108689, 2225, 16384⟩
    (by decide) selected_cut_14300

theorem selected_cut_14301 : selected 8 ⟨370561, by decide⟩
    (prefixPartial 13 108690) = some ⟨13, 2, 0, 370561, 108690, 1225, 16384⟩ := by
  decide +kernel

theorem context_13_108690_370561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108690 ⟨370561, by decide⟩ :=
  accepted_of_selected 13 108690 ⟨370561, by decide⟩ ⟨13, 2, 0, 370561, 108690, 1225, 16384⟩
    (by decide) selected_cut_14301

theorem selected_cut_14302 : selected 8 ⟨370568, by decide⟩
    (prefixPartial 13 108691) = some ⟨13, 2, 0, 370568, 108691, 833, 16384⟩ := by
  decide +kernel

theorem context_13_108691_370568 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108691 ⟨370568, by decide⟩ :=
  accepted_of_selected 13 108691 ⟨370568, by decide⟩ ⟨13, 2, 0, 370568, 108691, 833, 16384⟩
    (by decide) selected_cut_14302

theorem unmarked_context_12_27172_370569 : frontier 9 ⟨370569, by decide⟩
    (prefixCache 12 27172) (prefixPartial 12 27172) = false := by
  decide +kernel

theorem node_context_12_27172_370569 : EJMOriginalGlobalDAGData.nodes 9 ⟨370569, by decide⟩ =
    .split (coordinate 12) (![⟨370519, by decide⟩,⟨370544, by decide⟩,⟨370561, by decide⟩,⟨370568, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27172_370569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27172 ⟨370569, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27172
    ⟨370569, by decide⟩ (by decide) (![⟨370519, by decide⟩,⟨370544, by decide⟩,⟨370561, by decide⟩,⟨370568, by decide⟩]) unmarked_context_12_27172_370569 node_context_12_27172_370569
  intro a
  fin_cases a
  · exact context_13_108688_370519
  · exact context_13_108689_370544
  · exact context_13_108690_370561
  · exact context_13_108691_370568

theorem selected_cut_14303 : selected 8 ⟨370580, by decide⟩
    (prefixPartial 13 108692) = some ⟨13, 2, 0, 370580, 108692, 973, 16384⟩ := by
  decide +kernel

theorem context_13_108692_370580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108692 ⟨370580, by decide⟩ :=
  accepted_of_selected 13 108692 ⟨370580, by decide⟩ ⟨13, 2, 0, 370580, 108692, 973, 16384⟩
    (by decide) selected_cut_14303

theorem selected_cut_14304 : selected 8 ⟨370602, by decide⟩
    (prefixPartial 13 108693) = some ⟨13, 2, 0, 370602, 108693, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_108693_370602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108693 ⟨370602, by decide⟩ :=
  accepted_of_selected 13 108693 ⟨370602, by decide⟩ ⟨13, 2, 0, 370602, 108693, 1749, 16384⟩
    (by decide) selected_cut_14304

theorem selected_cut_14305 : selected 8 ⟨370624, by decide⟩
    (prefixPartial 13 108694) = some ⟨13, 2, 0, 370624, 108694, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_108694_370624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108694 ⟨370624, by decide⟩ :=
  accepted_of_selected 13 108694 ⟨370624, by decide⟩ ⟨13, 2, 0, 370624, 108694, 1221, 16384⟩
    (by decide) selected_cut_14305

theorem selected_cut_14306 : selected 8 ⟨370631, by decide⟩
    (prefixPartial 13 108695) = some ⟨13, 2, 0, 370631, 108695, 781, 16384⟩ := by
  decide +kernel

theorem context_13_108695_370631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 108695 ⟨370631, by decide⟩ :=
  accepted_of_selected 13 108695 ⟨370631, by decide⟩ ⟨13, 2, 0, 370631, 108695, 781, 16384⟩
    (by decide) selected_cut_14306

theorem unmarked_context_12_27173_370632 : frontier 9 ⟨370632, by decide⟩
    (prefixCache 12 27173) (prefixPartial 12 27173) = false := by
  decide +kernel

theorem node_context_12_27173_370632 : EJMOriginalGlobalDAGData.nodes 9 ⟨370632, by decide⟩ =
    .split (coordinate 12) (![⟨370580, by decide⟩,⟨370602, by decide⟩,⟨370624, by decide⟩,⟨370631, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_27173_370632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 27173 ⟨370632, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 27173
    ⟨370632, by decide⟩ (by decide) (![⟨370580, by decide⟩,⟨370602, by decide⟩,⟨370624, by decide⟩,⟨370631, by decide⟩]) unmarked_context_12_27173_370632 node_context_12_27173_370632
  intro a
  fin_cases a
  · exact context_13_108692_370580
  · exact context_13_108693_370602
  · exact context_13_108694_370624
  · exact context_13_108695_370631

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
