/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover127
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_12291 : selected 8 ⟨326020, by decide⟩
    (prefixPartial 13 104505) = some ⟨13, 2, 0, 326020, 104505, 2961, 16384⟩ := by
  decide +kernel

theorem context_13_104505_326020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104505 ⟨326020, by decide⟩ :=
  accepted_of_selected 13 104505 ⟨326020, by decide⟩ ⟨13, 2, 0, 326020, 104505, 2961, 16384⟩
    (by decide) selected_cut_12291

theorem selected_cut_12292 : selected 8 ⟨326040, by decide⟩
    (prefixPartial 13 104506) = some ⟨13, 2, 0, 326040, 104506, 1541, 16384⟩ := by
  decide +kernel

theorem context_13_104506_326040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104506 ⟨326040, by decide⟩ :=
  accepted_of_selected 13 104506 ⟨326040, by decide⟩ ⟨13, 2, 0, 326040, 104506, 1541, 16384⟩
    (by decide) selected_cut_12292

theorem selected_cut_12293 : selected 8 ⟨326048, by decide⟩
    (prefixPartial 13 104507) = some ⟨13, 2, 0, 326048, 104507, 997, 16384⟩ := by
  decide +kernel

theorem context_13_104507_326048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104507 ⟨326048, by decide⟩ :=
  accepted_of_selected 13 104507 ⟨326048, by decide⟩ ⟨13, 2, 0, 326048, 104507, 997, 16384⟩
    (by decide) selected_cut_12293

theorem unmarked_context_12_26126_326049 : frontier 9 ⟨326049, by decide⟩
    (prefixCache 12 26126) (prefixPartial 12 26126) = false := by
  decide +kernel

theorem node_context_12_26126_326049 : EJMOriginalGlobalDAGData.nodes 9 ⟨326049, by decide⟩ =
    .split (coordinate 12) (![⟨325976, by decide⟩,⟨326020, by decide⟩,⟨326040, by decide⟩,⟨326048, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26126_326049 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26126 ⟨326049, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26126
    ⟨326049, by decide⟩ (by decide) (![⟨325976, by decide⟩,⟨326020, by decide⟩,⟨326040, by decide⟩,⟨326048, by decide⟩]) unmarked_context_12_26126_326049 node_context_12_26126_326049
  intro a
  fin_cases a
  · exact context_13_104504_325976
  · exact context_13_104505_326020
  · exact context_13_104506_326040
  · exact context_13_104507_326048

theorem selected_cut_12294 : selected 8 ⟨326096, by decide⟩
    (prefixPartial 13 104508) = some ⟨13, 2, 0, 326096, 104508, 3101, 16384⟩ := by
  decide +kernel

theorem context_13_104508_326096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104508 ⟨326096, by decide⟩ :=
  accepted_of_selected 13 104508 ⟨326096, by decide⟩ ⟨13, 2, 0, 326096, 104508, 3101, 16384⟩
    (by decide) selected_cut_12294

theorem selected_cut_12295 : selected 8 ⟨326157, by decide⟩
    (prefixPartial 13 104509) = some ⟨13, 2, 0, 326157, 104509, 3761, 16384⟩ := by
  decide +kernel

theorem context_13_104509_326157 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104509 ⟨326157, by decide⟩ :=
  accepted_of_selected 13 104509 ⟨326157, by decide⟩ ⟨13, 2, 0, 326157, 104509, 3761, 16384⟩
    (by decide) selected_cut_12295

theorem selected_cut_12296 : selected 8 ⟨326183, by decide⟩
    (prefixPartial 13 104510) = some ⟨13, 2, 0, 326183, 104510, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_104510_326183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104510 ⟨326183, by decide⟩ :=
  accepted_of_selected 13 104510 ⟨326183, by decide⟩ ⟨13, 2, 0, 326183, 104510, 2049, 16384⟩
    (by decide) selected_cut_12296

theorem selected_cut_12297 : selected 8 ⟨326188, by decide⟩
    (prefixPartial 13 104511) = some ⟨13, 2, 0, 326188, 104511, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_104511_326188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104511 ⟨326188, by decide⟩ :=
  accepted_of_selected 13 104511 ⟨326188, by decide⟩ ⟨13, 2, 0, 326188, 104511, 1093, 16384⟩
    (by decide) selected_cut_12297

theorem unmarked_context_12_26127_326189 : frontier 9 ⟨326189, by decide⟩
    (prefixCache 12 26127) (prefixPartial 12 26127) = false := by
  decide +kernel

theorem node_context_12_26127_326189 : EJMOriginalGlobalDAGData.nodes 9 ⟨326189, by decide⟩ =
    .split (coordinate 12) (![⟨326096, by decide⟩,⟨326157, by decide⟩,⟨326183, by decide⟩,⟨326188, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26127_326189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26127 ⟨326189, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26127
    ⟨326189, by decide⟩ (by decide) (![⟨326096, by decide⟩,⟨326157, by decide⟩,⟨326183, by decide⟩,⟨326188, by decide⟩]) unmarked_context_12_26127_326189 node_context_12_26127_326189
  intro a
  fin_cases a
  · exact context_13_104508_326096
  · exact context_13_104509_326157
  · exact context_13_104510_326183
  · exact context_13_104511_326188

theorem unmarked_context_11_6531_326190 : frontier 10 ⟨326190, by decide⟩
    (prefixCache 11 6531) (prefixPartial 11 6531) = false := by
  decide +kernel

theorem node_context_11_6531_326190 : EJMOriginalGlobalDAGData.nodes 10 ⟨326190, by decide⟩ =
    .split (coordinate 11) (![⟨325787, by decide⟩,⟨325944, by decide⟩,⟨326049, by decide⟩,⟨326189, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6531_326190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6531 ⟨326190, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6531
    ⟨326190, by decide⟩ (by decide) (![⟨325787, by decide⟩,⟨325944, by decide⟩,⟨326049, by decide⟩,⟨326189, by decide⟩]) unmarked_context_11_6531_326190 node_context_11_6531_326190
  intro a
  fin_cases a
  · exact context_12_26124_325787
  · exact context_12_26125_325944
  · exact context_12_26126_326049
  · exact context_12_26127_326189

theorem unmarked_context_10_1632_326191 : frontier 11 ⟨326191, by decide⟩
    (prefixCache 10 1632) (prefixPartial 10 1632) = false := by
  decide +kernel

theorem node_context_10_1632_326191 : EJMOriginalGlobalDAGData.nodes 11 ⟨326191, by decide⟩ =
    .split (coordinate 10) (![⟨324597, by decide⟩,⟨324982, by decide⟩,⟨325670, by decide⟩,⟨326190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1632_326191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1632 ⟨326191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1632
    ⟨326191, by decide⟩ (by decide) (![⟨324597, by decide⟩,⟨324982, by decide⟩,⟨325670, by decide⟩,⟨326190, by decide⟩]) unmarked_context_10_1632_326191 node_context_10_1632_326191
  intro a
  fin_cases a
  · exact context_11_6528_324597
  · exact context_11_6529_324982
  · exact context_11_6530_325670
  · exact context_11_6531_326190

theorem selected_cut_12298 : selected 8 ⟨326212, by decide⟩
    (prefixPartial 13 104512) = some ⟨13, 2, 0, 326212, 104512, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_104512_326212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104512 ⟨326212, by decide⟩ :=
  accepted_of_selected 13 104512 ⟨326212, by decide⟩ ⟨13, 2, 0, 326212, 104512, 1641, 16384⟩
    (by decide) selected_cut_12298

theorem selected_cut_12299 : selected 8 ⟨326233, by decide⟩
    (prefixPartial 13 104513) = some ⟨13, 2, 0, 326233, 104513, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_104513_326233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104513 ⟨326233, by decide⟩ :=
  accepted_of_selected 13 104513 ⟨326233, by decide⟩ ⟨13, 2, 0, 326233, 104513, 1425, 16384⟩
    (by decide) selected_cut_12299

theorem selected_cut_12300 : selected 8 ⟨326247, by decide⟩
    (prefixPartial 13 104514) = some ⟨13, 2, 0, 326247, 104514, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_104514_326247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104514 ⟨326247, by decide⟩ :=
  accepted_of_selected 13 104514 ⟨326247, by decide⟩ ⟨13, 2, 0, 326247, 104514, 1013, 16384⟩
    (by decide) selected_cut_12300

theorem selected_cut_12301 : selected 8 ⟨326254, by decide⟩
    (prefixPartial 13 104515) = some ⟨13, 2, 0, 326254, 104515, 757, 16384⟩ := by
  decide +kernel

theorem context_13_104515_326254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104515 ⟨326254, by decide⟩ :=
  accepted_of_selected 13 104515 ⟨326254, by decide⟩ ⟨13, 2, 0, 326254, 104515, 757, 16384⟩
    (by decide) selected_cut_12301

theorem unmarked_context_12_26128_326255 : frontier 9 ⟨326255, by decide⟩
    (prefixCache 12 26128) (prefixPartial 12 26128) = false := by
  decide +kernel

theorem node_context_12_26128_326255 : EJMOriginalGlobalDAGData.nodes 9 ⟨326255, by decide⟩ =
    .split (coordinate 12) (![⟨326212, by decide⟩,⟨326233, by decide⟩,⟨326247, by decide⟩,⟨326254, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26128_326255 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26128 ⟨326255, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26128
    ⟨326255, by decide⟩ (by decide) (![⟨326212, by decide⟩,⟨326233, by decide⟩,⟨326247, by decide⟩,⟨326254, by decide⟩]) unmarked_context_12_26128_326255 node_context_12_26128_326255
  intro a
  fin_cases a
  · exact context_13_104512_326212
  · exact context_13_104513_326233
  · exact context_13_104514_326247
  · exact context_13_104515_326254

theorem selected_cut_12302 : selected 8 ⟨326278, by decide⟩
    (prefixPartial 13 104516) = some ⟨13, 2, 0, 326278, 104516, 2273, 16384⟩ := by
  decide +kernel

theorem context_13_104516_326278 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104516 ⟨326278, by decide⟩ :=
  accepted_of_selected 13 104516 ⟨326278, by decide⟩ ⟨13, 2, 0, 326278, 104516, 2273, 16384⟩
    (by decide) selected_cut_12302

theorem selected_cut_12303 : selected 8 ⟨326303, by decide⟩
    (prefixPartial 13 104517) = some ⟨13, 2, 0, 326303, 104517, 1797, 16384⟩ := by
  decide +kernel

theorem context_13_104517_326303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104517 ⟨326303, by decide⟩ :=
  accepted_of_selected 13 104517 ⟨326303, by decide⟩ ⟨13, 2, 0, 326303, 104517, 1797, 16384⟩
    (by decide) selected_cut_12303

theorem selected_cut_12304 : selected 8 ⟨326321, by decide⟩
    (prefixPartial 13 104518) = some ⟨13, 2, 0, 326321, 104518, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_104518_326321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104518 ⟨326321, by decide⟩ :=
  accepted_of_selected 13 104518 ⟨326321, by decide⟩ ⟨13, 2, 0, 326321, 104518, 1313, 16384⟩
    (by decide) selected_cut_12304

theorem selected_cut_12305 : selected 8 ⟨326329, by decide⟩
    (prefixPartial 13 104519) = some ⟨13, 2, 0, 326329, 104519, 841, 16384⟩ := by
  decide +kernel

theorem context_13_104519_326329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104519 ⟨326329, by decide⟩ :=
  accepted_of_selected 13 104519 ⟨326329, by decide⟩ ⟨13, 2, 0, 326329, 104519, 841, 16384⟩
    (by decide) selected_cut_12305

theorem unmarked_context_12_26129_326330 : frontier 9 ⟨326330, by decide⟩
    (prefixCache 12 26129) (prefixPartial 12 26129) = false := by
  decide +kernel

theorem node_context_12_26129_326330 : EJMOriginalGlobalDAGData.nodes 9 ⟨326330, by decide⟩ =
    .split (coordinate 12) (![⟨326278, by decide⟩,⟨326303, by decide⟩,⟨326321, by decide⟩,⟨326329, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26129_326330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26129 ⟨326330, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26129
    ⟨326330, by decide⟩ (by decide) (![⟨326278, by decide⟩,⟨326303, by decide⟩,⟨326321, by decide⟩,⟨326329, by decide⟩]) unmarked_context_12_26129_326330 node_context_12_26129_326330
  intro a
  fin_cases a
  · exact context_13_104516_326278
  · exact context_13_104517_326303
  · exact context_13_104518_326321
  · exact context_13_104519_326329

theorem selected_cut_12306 : selected 8 ⟨326350, by decide⟩
    (prefixPartial 13 104520) = some ⟨13, 2, 0, 326350, 104520, 1745, 16384⟩ := by
  decide +kernel

theorem context_13_104520_326350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104520 ⟨326350, by decide⟩ :=
  accepted_of_selected 13 104520 ⟨326350, by decide⟩ ⟨13, 2, 0, 326350, 104520, 1745, 16384⟩
    (by decide) selected_cut_12306

theorem selected_cut_12307 : selected 8 ⟨326372, by decide⟩
    (prefixPartial 13 104521) = some ⟨13, 2, 0, 326372, 104521, 1569, 16384⟩ := by
  decide +kernel

theorem context_13_104521_326372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104521 ⟨326372, by decide⟩ :=
  accepted_of_selected 13 104521 ⟨326372, by decide⟩ ⟨13, 2, 0, 326372, 104521, 1569, 16384⟩
    (by decide) selected_cut_12307

theorem selected_cut_12308 : selected 8 ⟨326386, by decide⟩
    (prefixPartial 13 104522) = some ⟨13, 2, 0, 326386, 104522, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_104522_326386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104522 ⟨326386, by decide⟩ :=
  accepted_of_selected 13 104522 ⟨326386, by decide⟩ ⟨13, 2, 0, 326386, 104522, 1081, 16384⟩
    (by decide) selected_cut_12308

theorem selected_cut_12309 : selected 8 ⟨326394, by decide⟩
    (prefixPartial 13 104523) = some ⟨13, 2, 0, 326394, 104523, 821, 16384⟩ := by
  decide +kernel

theorem context_13_104523_326394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104523 ⟨326394, by decide⟩ :=
  accepted_of_selected 13 104523 ⟨326394, by decide⟩ ⟨13, 2, 0, 326394, 104523, 821, 16384⟩
    (by decide) selected_cut_12309

theorem unmarked_context_12_26130_326395 : frontier 9 ⟨326395, by decide⟩
    (prefixCache 12 26130) (prefixPartial 12 26130) = false := by
  decide +kernel

theorem node_context_12_26130_326395 : EJMOriginalGlobalDAGData.nodes 9 ⟨326395, by decide⟩ =
    .split (coordinate 12) (![⟨326350, by decide⟩,⟨326372, by decide⟩,⟨326386, by decide⟩,⟨326394, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26130_326395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26130 ⟨326395, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26130
    ⟨326395, by decide⟩ (by decide) (![⟨326350, by decide⟩,⟨326372, by decide⟩,⟨326386, by decide⟩,⟨326394, by decide⟩]) unmarked_context_12_26130_326395 node_context_12_26130_326395
  intro a
  fin_cases a
  · exact context_13_104520_326350
  · exact context_13_104521_326372
  · exact context_13_104522_326386
  · exact context_13_104523_326394

theorem selected_cut_12310 : selected 8 ⟨326422, by decide⟩
    (prefixPartial 13 104524) = some ⟨13, 2, 0, 326422, 104524, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_104524_326422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104524 ⟨326422, by decide⟩ :=
  accepted_of_selected 13 104524 ⟨326422, by decide⟩ ⟨13, 2, 0, 326422, 104524, 2433, 16384⟩
    (by decide) selected_cut_12310

theorem selected_cut_12311 : selected 8 ⟨326450, by decide⟩
    (prefixPartial 13 104525) = some ⟨13, 2, 0, 326450, 104525, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_104525_326450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104525 ⟨326450, by decide⟩ :=
  accepted_of_selected 13 104525 ⟨326450, by decide⟩ ⟨13, 2, 0, 326450, 104525, 2301, 16384⟩
    (by decide) selected_cut_12311

theorem selected_cut_12312 : selected 8 ⟨326469, by decide⟩
    (prefixPartial 13 104526) = some ⟨13, 2, 0, 326469, 104526, 1481, 16384⟩ := by
  decide +kernel

theorem context_13_104526_326469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104526 ⟨326469, by decide⟩ :=
  accepted_of_selected 13 104526 ⟨326469, by decide⟩ ⟨13, 2, 0, 326469, 104526, 1481, 16384⟩
    (by decide) selected_cut_12312

theorem selected_cut_12313 : selected 8 ⟨326472, by decide⟩
    (prefixPartial 13 104527) = some ⟨13, 2, 0, 326472, 104527, 957, 16384⟩ := by
  decide +kernel

theorem context_13_104527_326472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104527 ⟨326472, by decide⟩ :=
  accepted_of_selected 13 104527 ⟨326472, by decide⟩ ⟨13, 2, 0, 326472, 104527, 957, 16384⟩
    (by decide) selected_cut_12313

theorem unmarked_context_12_26131_326473 : frontier 9 ⟨326473, by decide⟩
    (prefixCache 12 26131) (prefixPartial 12 26131) = false := by
  decide +kernel

theorem node_context_12_26131_326473 : EJMOriginalGlobalDAGData.nodes 9 ⟨326473, by decide⟩ =
    .split (coordinate 12) (![⟨326422, by decide⟩,⟨326450, by decide⟩,⟨326469, by decide⟩,⟨326472, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26131_326473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26131 ⟨326473, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26131
    ⟨326473, by decide⟩ (by decide) (![⟨326422, by decide⟩,⟨326450, by decide⟩,⟨326469, by decide⟩,⟨326472, by decide⟩]) unmarked_context_12_26131_326473 node_context_12_26131_326473
  intro a
  fin_cases a
  · exact context_13_104524_326422
  · exact context_13_104525_326450
  · exact context_13_104526_326469
  · exact context_13_104527_326472

theorem unmarked_context_11_6532_326474 : frontier 10 ⟨326474, by decide⟩
    (prefixCache 11 6532) (prefixPartial 11 6532) = false := by
  decide +kernel

theorem node_context_11_6532_326474 : EJMOriginalGlobalDAGData.nodes 10 ⟨326474, by decide⟩ =
    .split (coordinate 11) (![⟨326255, by decide⟩,⟨326330, by decide⟩,⟨326395, by decide⟩,⟨326473, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6532_326474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6532 ⟨326474, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6532
    ⟨326474, by decide⟩ (by decide) (![⟨326255, by decide⟩,⟨326330, by decide⟩,⟨326395, by decide⟩,⟨326473, by decide⟩]) unmarked_context_11_6532_326474 node_context_11_6532_326474
  intro a
  fin_cases a
  · exact context_12_26128_326255
  · exact context_12_26129_326330
  · exact context_12_26130_326395
  · exact context_12_26131_326473

theorem selected_cut_12314 : selected 8 ⟨326501, by decide⟩
    (prefixPartial 13 104528) = some ⟨13, 2, 0, 326501, 104528, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_104528_326501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104528 ⟨326501, by decide⟩ :=
  accepted_of_selected 13 104528 ⟨326501, by decide⟩ ⟨13, 2, 0, 326501, 104528, 2253, 16384⟩
    (by decide) selected_cut_12314

theorem selected_cut_12315 : selected 8 ⟨326550, by decide⟩
    (prefixPartial 13 104529) = some ⟨13, 2, 0, 326550, 104529, 3105, 16384⟩ := by
  decide +kernel

theorem context_13_104529_326550 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104529 ⟨326550, by decide⟩ :=
  accepted_of_selected 13 104529 ⟨326550, by decide⟩ ⟨13, 2, 0, 326550, 104529, 3105, 16384⟩
    (by decide) selected_cut_12315

theorem selected_cut_12316 : selected 8 ⟨326567, by decide⟩
    (prefixPartial 13 104530) = some ⟨13, 2, 0, 326567, 104530, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_104530_326567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104530 ⟨326567, by decide⟩ :=
  accepted_of_selected 13 104530 ⟨326567, by decide⟩ ⟨13, 2, 0, 326567, 104530, 1557, 16384⟩
    (by decide) selected_cut_12316

theorem selected_cut_12317 : selected 8 ⟨326574, by decide⟩
    (prefixPartial 13 104531) = some ⟨13, 2, 0, 326574, 104531, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_104531_326574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104531 ⟨326574, by decide⟩ :=
  accepted_of_selected 13 104531 ⟨326574, by decide⟩ ⟨13, 2, 0, 326574, 104531, 1113, 16384⟩
    (by decide) selected_cut_12317

theorem unmarked_context_12_26132_326575 : frontier 9 ⟨326575, by decide⟩
    (prefixCache 12 26132) (prefixPartial 12 26132) = false := by
  decide +kernel

theorem node_context_12_26132_326575 : EJMOriginalGlobalDAGData.nodes 9 ⟨326575, by decide⟩ =
    .split (coordinate 12) (![⟨326501, by decide⟩,⟨326550, by decide⟩,⟨326567, by decide⟩,⟨326574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26132_326575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26132 ⟨326575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26132
    ⟨326575, by decide⟩ (by decide) (![⟨326501, by decide⟩,⟨326550, by decide⟩,⟨326567, by decide⟩,⟨326574, by decide⟩]) unmarked_context_12_26132_326575 node_context_12_26132_326575
  intro a
  fin_cases a
  · exact context_13_104528_326501
  · exact context_13_104529_326550
  · exact context_13_104530_326567
  · exact context_13_104531_326574

theorem selected_cut_12318 : selected 8 ⟨326612, by decide⟩
    (prefixPartial 13 104532) = some ⟨13, 2, 0, 326612, 104532, 3045, 16384⟩ := by
  decide +kernel

theorem context_13_104532_326612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104532 ⟨326612, by decide⟩ :=
  accepted_of_selected 13 104532 ⟨326612, by decide⟩ ⟨13, 2, 0, 326612, 104532, 3045, 16384⟩
    (by decide) selected_cut_12318

theorem selected_cut_12319 : selected 8 ⟨326671, by decide⟩
    (prefixPartial 13 104533) = some ⟨13, 2, 0, 326671, 104533, 3349, 16384⟩ := by
  decide +kernel

theorem context_13_104533_326671 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104533 ⟨326671, by decide⟩ :=
  accepted_of_selected 13 104533 ⟨326671, by decide⟩ ⟨13, 2, 0, 326671, 104533, 3349, 16384⟩
    (by decide) selected_cut_12319

theorem selected_cut_12320 : selected 8 ⟨326688, by decide⟩
    (prefixPartial 13 104534) = some ⟨13, 2, 0, 326688, 104534, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_104534_326688 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104534 ⟨326688, by decide⟩ :=
  accepted_of_selected 13 104534 ⟨326688, by decide⟩ ⟨13, 2, 0, 326688, 104534, 1841, 16384⟩
    (by decide) selected_cut_12320

theorem selected_cut_12321 : selected 8 ⟨326698, by decide⟩
    (prefixPartial 13 104535) = some ⟨13, 2, 0, 326698, 104535, 1173, 16384⟩ := by
  decide +kernel

theorem context_13_104535_326698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104535 ⟨326698, by decide⟩ :=
  accepted_of_selected 13 104535 ⟨326698, by decide⟩ ⟨13, 2, 0, 326698, 104535, 1173, 16384⟩
    (by decide) selected_cut_12321

theorem unmarked_context_12_26133_326699 : frontier 9 ⟨326699, by decide⟩
    (prefixCache 12 26133) (prefixPartial 12 26133) = false := by
  decide +kernel

theorem node_context_12_26133_326699 : EJMOriginalGlobalDAGData.nodes 9 ⟨326699, by decide⟩ =
    .split (coordinate 12) (![⟨326612, by decide⟩,⟨326671, by decide⟩,⟨326688, by decide⟩,⟨326698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26133_326699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26133 ⟨326699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26133
    ⟨326699, by decide⟩ (by decide) (![⟨326612, by decide⟩,⟨326671, by decide⟩,⟨326688, by decide⟩,⟨326698, by decide⟩]) unmarked_context_12_26133_326699 node_context_12_26133_326699
  intro a
  fin_cases a
  · exact context_13_104532_326612
  · exact context_13_104533_326671
  · exact context_13_104534_326688
  · exact context_13_104535_326698

theorem selected_cut_12322 : selected 8 ⟨326733, by decide⟩
    (prefixPartial 13 104536) = some ⟨13, 2, 0, 326733, 104536, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_104536_326733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104536 ⟨326733, by decide⟩ :=
  accepted_of_selected 13 104536 ⟨326733, by decide⟩ ⟨13, 2, 0, 326733, 104536, 2437, 16384⟩
    (by decide) selected_cut_12322

theorem selected_cut_12323 : selected 8 ⟨326774, by decide⟩
    (prefixPartial 13 104537) = some ⟨13, 2, 0, 326774, 104537, 3085, 16384⟩ := by
  decide +kernel

theorem context_13_104537_326774 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104537 ⟨326774, by decide⟩ :=
  accepted_of_selected 13 104537 ⟨326774, by decide⟩ ⟨13, 2, 0, 326774, 104537, 3085, 16384⟩
    (by decide) selected_cut_12323

theorem selected_cut_12324 : selected 8 ⟨326793, by decide⟩
    (prefixPartial 13 104538) = some ⟨13, 2, 0, 326793, 104538, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_104538_326793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104538 ⟨326793, by decide⟩ :=
  accepted_of_selected 13 104538 ⟨326793, by decide⟩ ⟨13, 2, 0, 326793, 104538, 1597, 16384⟩
    (by decide) selected_cut_12324

theorem selected_cut_12325 : selected 8 ⟨326801, by decide⟩
    (prefixPartial 13 104539) = some ⟨13, 2, 0, 326801, 104539, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_104539_326801 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104539 ⟨326801, by decide⟩ :=
  accepted_of_selected 13 104539 ⟨326801, by decide⟩ ⟨13, 2, 0, 326801, 104539, 1185, 16384⟩
    (by decide) selected_cut_12325

theorem unmarked_context_12_26134_326802 : frontier 9 ⟨326802, by decide⟩
    (prefixCache 12 26134) (prefixPartial 12 26134) = false := by
  decide +kernel

theorem node_context_12_26134_326802 : EJMOriginalGlobalDAGData.nodes 9 ⟨326802, by decide⟩ =
    .split (coordinate 12) (![⟨326733, by decide⟩,⟨326774, by decide⟩,⟨326793, by decide⟩,⟨326801, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26134_326802 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26134 ⟨326802, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26134
    ⟨326802, by decide⟩ (by decide) (![⟨326733, by decide⟩,⟨326774, by decide⟩,⟨326793, by decide⟩,⟨326801, by decide⟩]) unmarked_context_12_26134_326802 node_context_12_26134_326802
  intro a
  fin_cases a
  · exact context_13_104536_326733
  · exact context_13_104537_326774
  · exact context_13_104538_326793
  · exact context_13_104539_326801

theorem selected_cut_12326 : selected 8 ⟨326850, by decide⟩
    (prefixPartial 13 104540) = some ⟨13, 2, 0, 326850, 104540, 3245, 16384⟩ := by
  decide +kernel

theorem context_13_104540_326850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104540 ⟨326850, by decide⟩ :=
  accepted_of_selected 13 104540 ⟨326850, by decide⟩ ⟨13, 2, 0, 326850, 104540, 3245, 16384⟩
    (by decide) selected_cut_12326

theorem selected_cut_12327 : selected 7 ⟨326873, by decide⟩
    (prefixPartial 14 418164) = some ⟨14, 2, 0, 326873, 418164, 1197, 4096⟩ := by
  decide +kernel

theorem context_14_418164_326873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 418164 ⟨326873, by decide⟩ :=
  accepted_of_selected 14 418164 ⟨326873, by decide⟩ ⟨14, 2, 0, 326873, 418164, 1197, 4096⟩
    (by decide) selected_cut_12327

theorem selected_cut_12328 : selected 7 ⟨326888, by decide⟩
    (prefixPartial 14 418165) = some ⟨14, 2, 0, 326888, 418165, 937, 4096⟩ := by
  decide +kernel

theorem context_14_418165_326888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 418165 ⟨326888, by decide⟩ :=
  accepted_of_selected 14 418165 ⟨326888, by decide⟩ ⟨14, 2, 0, 326888, 418165, 937, 4096⟩
    (by decide) selected_cut_12328

theorem selected_cut_12329 : selected 7 ⟨326913, by decide⟩
    (prefixPartial 14 418166) = some ⟨14, 2, 0, 326913, 418166, 1093, 4096⟩ := by
  decide +kernel

theorem context_14_418166_326913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 418166 ⟨326913, by decide⟩ :=
  accepted_of_selected 14 418166 ⟨326913, by decide⟩ ⟨14, 2, 0, 326913, 418166, 1093, 4096⟩
    (by decide) selected_cut_12329

theorem selected_cut_12330 : selected 7 ⟨326926, by decide⟩
    (prefixPartial 14 418167) = some ⟨14, 2, 0, 326926, 418167, 1057, 4096⟩ := by
  decide +kernel

theorem context_14_418167_326926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 418167 ⟨326926, by decide⟩ :=
  accepted_of_selected 14 418167 ⟨326926, by decide⟩ ⟨14, 2, 0, 326926, 418167, 1057, 4096⟩
    (by decide) selected_cut_12330

theorem unmarked_context_13_104541_326927 : frontier 8 ⟨326927, by decide⟩
    (prefixCache 13 104541) (prefixPartial 13 104541) = false := by
  decide +kernel

theorem node_context_13_104541_326927 : EJMOriginalGlobalDAGData.nodes 8 ⟨326927, by decide⟩ =
    .split (coordinate 13) (![⟨326873, by decide⟩,⟨326888, by decide⟩,⟨326913, by decide⟩,⟨326926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_104541_326927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104541 ⟨326927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 104541
    ⟨326927, by decide⟩ (by decide) (![⟨326873, by decide⟩,⟨326888, by decide⟩,⟨326913, by decide⟩,⟨326926, by decide⟩]) unmarked_context_13_104541_326927 node_context_13_104541_326927
  intro a
  fin_cases a
  · exact context_14_418164_326873
  · exact context_14_418165_326888
  · exact context_14_418166_326913
  · exact context_14_418167_326926

theorem selected_cut_12331 : selected 8 ⟨326950, by decide⟩
    (prefixPartial 13 104542) = some ⟨13, 2, 0, 326950, 104542, 1985, 16384⟩ := by
  decide +kernel

theorem context_13_104542_326950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104542 ⟨326950, by decide⟩ :=
  accepted_of_selected 13 104542 ⟨326950, by decide⟩ ⟨13, 2, 0, 326950, 104542, 1985, 16384⟩
    (by decide) selected_cut_12331

theorem selected_cut_12332 : selected 8 ⟨326955, by decide⟩
    (prefixPartial 13 104543) = some ⟨13, 2, 0, 326955, 104543, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_104543_326955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104543 ⟨326955, by decide⟩ :=
  accepted_of_selected 13 104543 ⟨326955, by decide⟩ ⟨13, 2, 0, 326955, 104543, 1277, 16384⟩
    (by decide) selected_cut_12332

theorem unmarked_context_12_26135_326956 : frontier 9 ⟨326956, by decide⟩
    (prefixCache 12 26135) (prefixPartial 12 26135) = false := by
  decide +kernel

theorem node_context_12_26135_326956 : EJMOriginalGlobalDAGData.nodes 9 ⟨326956, by decide⟩ =
    .split (coordinate 12) (![⟨326850, by decide⟩,⟨326927, by decide⟩,⟨326950, by decide⟩,⟨326955, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26135_326956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26135 ⟨326956, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26135
    ⟨326956, by decide⟩ (by decide) (![⟨326850, by decide⟩,⟨326927, by decide⟩,⟨326950, by decide⟩,⟨326955, by decide⟩]) unmarked_context_12_26135_326956 node_context_12_26135_326956
  intro a
  fin_cases a
  · exact context_13_104540_326850
  · exact context_13_104541_326927
  · exact context_13_104542_326950
  · exact context_13_104543_326955

theorem unmarked_context_11_6533_326957 : frontier 10 ⟨326957, by decide⟩
    (prefixCache 11 6533) (prefixPartial 11 6533) = false := by
  decide +kernel

theorem node_context_11_6533_326957 : EJMOriginalGlobalDAGData.nodes 10 ⟨326957, by decide⟩ =
    .split (coordinate 11) (![⟨326575, by decide⟩,⟨326699, by decide⟩,⟨326802, by decide⟩,⟨326956, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6533_326957 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6533 ⟨326957, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6533
    ⟨326957, by decide⟩ (by decide) (![⟨326575, by decide⟩,⟨326699, by decide⟩,⟨326802, by decide⟩,⟨326956, by decide⟩]) unmarked_context_11_6533_326957 node_context_11_6533_326957
  intro a
  fin_cases a
  · exact context_12_26132_326575
  · exact context_12_26133_326699
  · exact context_12_26134_326802
  · exact context_12_26135_326956

theorem selected_cut_12333 : selected 8 ⟨326972, by decide⟩
    (prefixPartial 13 104544) = some ⟨13, 2, 0, 326972, 104544, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_104544_326972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104544 ⟨326972, by decide⟩ :=
  accepted_of_selected 13 104544 ⟨326972, by decide⟩ ⟨13, 2, 0, 326972, 104544, 1113, 16384⟩
    (by decide) selected_cut_12333

theorem selected_cut_12334 : selected 8 ⟨326993, by decide⟩
    (prefixPartial 13 104545) = some ⟨13, 2, 0, 326993, 104545, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_104545_326993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104545 ⟨326993, by decide⟩ :=
  accepted_of_selected 13 104545 ⟨326993, by decide⟩ ⟨13, 2, 0, 326993, 104545, 1521, 16384⟩
    (by decide) selected_cut_12334

theorem selected_cut_12335 : selected 8 ⟨327006, by decide⟩
    (prefixPartial 13 104546) = some ⟨13, 2, 0, 327006, 104546, 997, 16384⟩ := by
  decide +kernel

theorem context_13_104546_327006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104546 ⟨327006, by decide⟩ :=
  accepted_of_selected 13 104546 ⟨327006, by decide⟩ ⟨13, 2, 0, 327006, 104546, 997, 16384⟩
    (by decide) selected_cut_12335

theorem selected_cut_12336 : selected 8 ⟨327011, by decide⟩
    (prefixPartial 13 104547) = some ⟨13, 2, 0, 327011, 104547, 873, 16384⟩ := by
  decide +kernel

theorem context_13_104547_327011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104547 ⟨327011, by decide⟩ :=
  accepted_of_selected 13 104547 ⟨327011, by decide⟩ ⟨13, 2, 0, 327011, 104547, 873, 16384⟩
    (by decide) selected_cut_12336

theorem unmarked_context_12_26136_327012 : frontier 9 ⟨327012, by decide⟩
    (prefixCache 12 26136) (prefixPartial 12 26136) = false := by
  decide +kernel

theorem node_context_12_26136_327012 : EJMOriginalGlobalDAGData.nodes 9 ⟨327012, by decide⟩ =
    .split (coordinate 12) (![⟨326972, by decide⟩,⟨326993, by decide⟩,⟨327006, by decide⟩,⟨327011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26136_327012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26136 ⟨327012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26136
    ⟨327012, by decide⟩ (by decide) (![⟨326972, by decide⟩,⟨326993, by decide⟩,⟨327006, by decide⟩,⟨327011, by decide⟩]) unmarked_context_12_26136_327012 node_context_12_26136_327012
  intro a
  fin_cases a
  · exact context_13_104544_326972
  · exact context_13_104545_326993
  · exact context_13_104546_327006
  · exact context_13_104547_327011

theorem selected_cut_12337 : selected 8 ⟨327036, by decide⟩
    (prefixPartial 13 104548) = some ⟨13, 2, 0, 327036, 104548, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_104548_327036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104548 ⟨327036, by decide⟩ :=
  accepted_of_selected 13 104548 ⟨327036, by decide⟩ ⟨13, 2, 0, 327036, 104548, 1453, 16384⟩
    (by decide) selected_cut_12337

theorem selected_cut_12338 : selected 8 ⟨327063, by decide⟩
    (prefixPartial 13 104549) = some ⟨13, 2, 0, 327063, 104549, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_104549_327063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104549 ⟨327063, by decide⟩ :=
  accepted_of_selected 13 104549 ⟨327063, by decide⟩ ⟨13, 2, 0, 327063, 104549, 1565, 16384⟩
    (by decide) selected_cut_12338

theorem selected_cut_12339 : selected 8 ⟨327081, by decide⟩
    (prefixPartial 13 104550) = some ⟨13, 2, 0, 327081, 104550, 1261, 16384⟩ := by
  decide +kernel

theorem context_13_104550_327081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104550 ⟨327081, by decide⟩ :=
  accepted_of_selected 13 104550 ⟨327081, by decide⟩ ⟨13, 2, 0, 327081, 104550, 1261, 16384⟩
    (by decide) selected_cut_12339

theorem selected_cut_12340 : selected 8 ⟨327089, by decide⟩
    (prefixPartial 13 104551) = some ⟨13, 2, 0, 327089, 104551, 897, 16384⟩ := by
  decide +kernel

theorem context_13_104551_327089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104551 ⟨327089, by decide⟩ :=
  accepted_of_selected 13 104551 ⟨327089, by decide⟩ ⟨13, 2, 0, 327089, 104551, 897, 16384⟩
    (by decide) selected_cut_12340

theorem unmarked_context_12_26137_327090 : frontier 9 ⟨327090, by decide⟩
    (prefixCache 12 26137) (prefixPartial 12 26137) = false := by
  decide +kernel

theorem node_context_12_26137_327090 : EJMOriginalGlobalDAGData.nodes 9 ⟨327090, by decide⟩ =
    .split (coordinate 12) (![⟨327036, by decide⟩,⟨327063, by decide⟩,⟨327081, by decide⟩,⟨327089, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26137_327090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26137 ⟨327090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26137
    ⟨327090, by decide⟩ (by decide) (![⟨327036, by decide⟩,⟨327063, by decide⟩,⟨327081, by decide⟩,⟨327089, by decide⟩]) unmarked_context_12_26137_327090 node_context_12_26137_327090
  intro a
  fin_cases a
  · exact context_13_104548_327036
  · exact context_13_104549_327063
  · exact context_13_104550_327081
  · exact context_13_104551_327089

theorem selected_cut_12341 : selected 8 ⟨327120, by decide⟩
    (prefixPartial 13 104552) = some ⟨13, 2, 0, 327120, 104552, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_104552_327120 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104552 ⟨327120, by decide⟩ :=
  accepted_of_selected 13 104552 ⟨327120, by decide⟩ ⟨13, 2, 0, 327120, 104552, 2057, 16384⟩
    (by decide) selected_cut_12341

theorem selected_cut_12342 : selected 8 ⟨327154, by decide⟩
    (prefixPartial 13 104553) = some ⟨13, 2, 0, 327154, 104553, 2889, 16384⟩ := by
  decide +kernel

theorem context_13_104553_327154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104553 ⟨327154, by decide⟩ :=
  accepted_of_selected 13 104553 ⟨327154, by decide⟩ ⟨13, 2, 0, 327154, 104553, 2889, 16384⟩
    (by decide) selected_cut_12342

theorem selected_cut_12343 : selected 8 ⟨327174, by decide⟩
    (prefixPartial 13 104554) = some ⟨13, 2, 0, 327174, 104554, 1981, 16384⟩ := by
  decide +kernel

theorem context_13_104554_327174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104554 ⟨327174, by decide⟩ :=
  accepted_of_selected 13 104554 ⟨327174, by decide⟩ ⟨13, 2, 0, 327174, 104554, 1981, 16384⟩
    (by decide) selected_cut_12343

theorem selected_cut_12344 : selected 8 ⟨327181, by decide⟩
    (prefixPartial 13 104555) = some ⟨13, 2, 0, 327181, 104555, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_104555_327181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104555 ⟨327181, by decide⟩ :=
  accepted_of_selected 13 104555 ⟨327181, by decide⟩ ⟨13, 2, 0, 327181, 104555, 1229, 16384⟩
    (by decide) selected_cut_12344

theorem unmarked_context_12_26138_327182 : frontier 9 ⟨327182, by decide⟩
    (prefixCache 12 26138) (prefixPartial 12 26138) = false := by
  decide +kernel

theorem node_context_12_26138_327182 : EJMOriginalGlobalDAGData.nodes 9 ⟨327182, by decide⟩ =
    .split (coordinate 12) (![⟨327120, by decide⟩,⟨327154, by decide⟩,⟨327174, by decide⟩,⟨327181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26138_327182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26138 ⟨327182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26138
    ⟨327182, by decide⟩ (by decide) (![⟨327120, by decide⟩,⟨327154, by decide⟩,⟨327174, by decide⟩,⟨327181, by decide⟩]) unmarked_context_12_26138_327182 node_context_12_26138_327182
  intro a
  fin_cases a
  · exact context_13_104552_327120
  · exact context_13_104553_327154
  · exact context_13_104554_327174
  · exact context_13_104555_327181

theorem selected_cut_12345 : selected 8 ⟨327200, by decide⟩
    (prefixPartial 13 104556) = some ⟨13, 2, 0, 327200, 104556, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_104556_327200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104556 ⟨327200, by decide⟩ :=
  accepted_of_selected 13 104556 ⟨327200, by decide⟩ ⟨13, 2, 0, 327200, 104556, 1409, 16384⟩
    (by decide) selected_cut_12345

theorem selected_cut_12346 : selected 8 ⟨327229, by decide⟩
    (prefixPartial 13 104557) = some ⟨13, 2, 0, 327229, 104557, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_104557_327229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104557 ⟨327229, by decide⟩ :=
  accepted_of_selected 13 104557 ⟨327229, by decide⟩ ⟨13, 2, 0, 327229, 104557, 2093, 16384⟩
    (by decide) selected_cut_12346

theorem selected_cut_12347 : selected 8 ⟨327249, by decide⟩
    (prefixPartial 13 104558) = some ⟨13, 2, 0, 327249, 104558, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_104558_327249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104558 ⟨327249, by decide⟩ :=
  accepted_of_selected 13 104558 ⟨327249, by decide⟩ ⟨13, 2, 0, 327249, 104558, 1321, 16384⟩
    (by decide) selected_cut_12347

theorem selected_cut_12348 : selected 8 ⟨327258, by decide⟩
    (prefixPartial 13 104559) = some ⟨13, 2, 0, 327258, 104559, 993, 16384⟩ := by
  decide +kernel

theorem context_13_104559_327258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104559 ⟨327258, by decide⟩ :=
  accepted_of_selected 13 104559 ⟨327258, by decide⟩ ⟨13, 2, 0, 327258, 104559, 993, 16384⟩
    (by decide) selected_cut_12348

theorem unmarked_context_12_26139_327259 : frontier 9 ⟨327259, by decide⟩
    (prefixCache 12 26139) (prefixPartial 12 26139) = false := by
  decide +kernel

theorem node_context_12_26139_327259 : EJMOriginalGlobalDAGData.nodes 9 ⟨327259, by decide⟩ =
    .split (coordinate 12) (![⟨327200, by decide⟩,⟨327229, by decide⟩,⟨327249, by decide⟩,⟨327258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26139_327259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26139 ⟨327259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26139
    ⟨327259, by decide⟩ (by decide) (![⟨327200, by decide⟩,⟨327229, by decide⟩,⟨327249, by decide⟩,⟨327258, by decide⟩]) unmarked_context_12_26139_327259 node_context_12_26139_327259
  intro a
  fin_cases a
  · exact context_13_104556_327200
  · exact context_13_104557_327229
  · exact context_13_104558_327249
  · exact context_13_104559_327258

theorem unmarked_context_11_6534_327260 : frontier 10 ⟨327260, by decide⟩
    (prefixCache 11 6534) (prefixPartial 11 6534) = false := by
  decide +kernel

theorem node_context_11_6534_327260 : EJMOriginalGlobalDAGData.nodes 10 ⟨327260, by decide⟩ =
    .split (coordinate 11) (![⟨327012, by decide⟩,⟨327090, by decide⟩,⟨327182, by decide⟩,⟨327259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6534_327260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6534 ⟨327260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6534
    ⟨327260, by decide⟩ (by decide) (![⟨327012, by decide⟩,⟨327090, by decide⟩,⟨327182, by decide⟩,⟨327259, by decide⟩]) unmarked_context_11_6534_327260 node_context_11_6534_327260
  intro a
  fin_cases a
  · exact context_12_26136_327012
  · exact context_12_26137_327090
  · exact context_12_26138_327182
  · exact context_12_26139_327259

theorem selected_cut_12349 : selected 8 ⟨327275, by decide⟩
    (prefixPartial 13 104560) = some ⟨13, 2, 0, 327275, 104560, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_104560_327275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104560 ⟨327275, by decide⟩ :=
  accepted_of_selected 13 104560 ⟨327275, by decide⟩ ⟨13, 2, 0, 327275, 104560, 1049, 16384⟩
    (by decide) selected_cut_12349

theorem selected_cut_12350 : selected 8 ⟨327298, by decide⟩
    (prefixPartial 13 104561) = some ⟨13, 2, 0, 327298, 104561, 1597, 16384⟩ := by
  decide +kernel

theorem context_13_104561_327298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104561 ⟨327298, by decide⟩ :=
  accepted_of_selected 13 104561 ⟨327298, by decide⟩ ⟨13, 2, 0, 327298, 104561, 1597, 16384⟩
    (by decide) selected_cut_12350

theorem selected_cut_12351 : selected 8 ⟨327316, by decide⟩
    (prefixPartial 13 104562) = some ⟨13, 2, 0, 327316, 104562, 1109, 16384⟩ := by
  decide +kernel

theorem context_13_104562_327316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104562 ⟨327316, by decide⟩ :=
  accepted_of_selected 13 104562 ⟨327316, by decide⟩ ⟨13, 2, 0, 327316, 104562, 1109, 16384⟩
    (by decide) selected_cut_12351

theorem selected_cut_12352 : selected 8 ⟨327323, by decide⟩
    (prefixPartial 13 104563) = some ⟨13, 2, 0, 327323, 104563, 829, 16384⟩ := by
  decide +kernel

theorem context_13_104563_327323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104563 ⟨327323, by decide⟩ :=
  accepted_of_selected 13 104563 ⟨327323, by decide⟩ ⟨13, 2, 0, 327323, 104563, 829, 16384⟩
    (by decide) selected_cut_12352

theorem unmarked_context_12_26140_327324 : frontier 9 ⟨327324, by decide⟩
    (prefixCache 12 26140) (prefixPartial 12 26140) = false := by
  decide +kernel

theorem node_context_12_26140_327324 : EJMOriginalGlobalDAGData.nodes 9 ⟨327324, by decide⟩ =
    .split (coordinate 12) (![⟨327275, by decide⟩,⟨327298, by decide⟩,⟨327316, by decide⟩,⟨327323, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26140_327324 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26140 ⟨327324, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26140
    ⟨327324, by decide⟩ (by decide) (![⟨327275, by decide⟩,⟨327298, by decide⟩,⟨327316, by decide⟩,⟨327323, by decide⟩]) unmarked_context_12_26140_327324 node_context_12_26140_327324
  intro a
  fin_cases a
  · exact context_13_104560_327275
  · exact context_13_104561_327298
  · exact context_13_104562_327316
  · exact context_13_104563_327323

theorem selected_cut_12353 : selected 8 ⟨327342, by decide⟩
    (prefixPartial 13 104564) = some ⟨13, 2, 0, 327342, 104564, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_104564_327342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104564 ⟨327342, by decide⟩ :=
  accepted_of_selected 13 104564 ⟨327342, by decide⟩ ⟨13, 2, 0, 327342, 104564, 1525, 16384⟩
    (by decide) selected_cut_12353

theorem selected_cut_12354 : selected 8 ⟨327367, by decide⟩
    (prefixPartial 13 104565) = some ⟨13, 2, 0, 327367, 104565, 1809, 16384⟩ := by
  decide +kernel

theorem context_13_104565_327367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104565 ⟨327367, by decide⟩ :=
  accepted_of_selected 13 104565 ⟨327367, by decide⟩ ⟨13, 2, 0, 327367, 104565, 1809, 16384⟩
    (by decide) selected_cut_12354

theorem selected_cut_12355 : selected 8 ⟨327388, by decide⟩
    (prefixPartial 13 104566) = some ⟨13, 2, 0, 327388, 104566, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_104566_327388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104566 ⟨327388, by decide⟩ :=
  accepted_of_selected 13 104566 ⟨327388, by decide⟩ ⟨13, 2, 0, 327388, 104566, 1245, 16384⟩
    (by decide) selected_cut_12355

theorem selected_cut_12356 : selected 8 ⟨327393, by decide⟩
    (prefixPartial 13 104567) = some ⟨13, 2, 0, 327393, 104567, 741, 16384⟩ := by
  decide +kernel

theorem context_13_104567_327393 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104567 ⟨327393, by decide⟩ :=
  accepted_of_selected 13 104567 ⟨327393, by decide⟩ ⟨13, 2, 0, 327393, 104567, 741, 16384⟩
    (by decide) selected_cut_12356

theorem unmarked_context_12_26141_327394 : frontier 9 ⟨327394, by decide⟩
    (prefixCache 12 26141) (prefixPartial 12 26141) = false := by
  decide +kernel

theorem node_context_12_26141_327394 : EJMOriginalGlobalDAGData.nodes 9 ⟨327394, by decide⟩ =
    .split (coordinate 12) (![⟨327342, by decide⟩,⟨327367, by decide⟩,⟨327388, by decide⟩,⟨327393, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26141_327394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26141 ⟨327394, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26141
    ⟨327394, by decide⟩ (by decide) (![⟨327342, by decide⟩,⟨327367, by decide⟩,⟨327388, by decide⟩,⟨327393, by decide⟩]) unmarked_context_12_26141_327394 node_context_12_26141_327394
  intro a
  fin_cases a
  · exact context_13_104564_327342
  · exact context_13_104565_327367
  · exact context_13_104566_327388
  · exact context_13_104567_327393

theorem selected_cut_12357 : selected 8 ⟨327407, by decide⟩
    (prefixPartial 13 104568) = some ⟨13, 2, 0, 327407, 104568, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_104568_327407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104568 ⟨327407, by decide⟩ :=
  accepted_of_selected 13 104568 ⟨327407, by decide⟩ ⟨13, 2, 0, 327407, 104568, 1117, 16384⟩
    (by decide) selected_cut_12357

theorem selected_cut_12358 : selected 8 ⟨327429, by decide⟩
    (prefixPartial 13 104569) = some ⟨13, 2, 0, 327429, 104569, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_104569_327429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104569 ⟨327429, by decide⟩ :=
  accepted_of_selected 13 104569 ⟨327429, by decide⟩ ⟨13, 2, 0, 327429, 104569, 1645, 16384⟩
    (by decide) selected_cut_12358

theorem selected_cut_12359 : selected 8 ⟨327444, by decide⟩
    (prefixPartial 13 104570) = some ⟨13, 2, 0, 327444, 104570, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_104570_327444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104570 ⟨327444, by decide⟩ :=
  accepted_of_selected 13 104570 ⟨327444, by decide⟩ ⟨13, 2, 0, 327444, 104570, 1077, 16384⟩
    (by decide) selected_cut_12359

theorem selected_cut_12360 : selected 8 ⟨327451, by decide⟩
    (prefixPartial 13 104571) = some ⟨13, 2, 0, 327451, 104571, 773, 16384⟩ := by
  decide +kernel

theorem context_13_104571_327451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104571 ⟨327451, by decide⟩ :=
  accepted_of_selected 13 104571 ⟨327451, by decide⟩ ⟨13, 2, 0, 327451, 104571, 773, 16384⟩
    (by decide) selected_cut_12360

theorem unmarked_context_12_26142_327452 : frontier 9 ⟨327452, by decide⟩
    (prefixCache 12 26142) (prefixPartial 12 26142) = false := by
  decide +kernel

theorem node_context_12_26142_327452 : EJMOriginalGlobalDAGData.nodes 9 ⟨327452, by decide⟩ =
    .split (coordinate 12) (![⟨327407, by decide⟩,⟨327429, by decide⟩,⟨327444, by decide⟩,⟨327451, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26142_327452 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26142 ⟨327452, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26142
    ⟨327452, by decide⟩ (by decide) (![⟨327407, by decide⟩,⟨327429, by decide⟩,⟨327444, by decide⟩,⟨327451, by decide⟩]) unmarked_context_12_26142_327452 node_context_12_26142_327452
  intro a
  fin_cases a
  · exact context_13_104568_327407
  · exact context_13_104569_327429
  · exact context_13_104570_327444
  · exact context_13_104571_327451

theorem selected_cut_12361 : selected 8 ⟨327472, by decide⟩
    (prefixPartial 13 104572) = some ⟨13, 2, 0, 327472, 104572, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_104572_327472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104572 ⟨327472, by decide⟩ :=
  accepted_of_selected 13 104572 ⟨327472, by decide⟩ ⟨13, 2, 0, 327472, 104572, 1457, 16384⟩
    (by decide) selected_cut_12361

theorem selected_cut_12362 : selected 8 ⟨327501, by decide⟩
    (prefixPartial 13 104573) = some ⟨13, 2, 0, 327501, 104573, 2061, 16384⟩ := by
  decide +kernel

theorem context_13_104573_327501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104573 ⟨327501, by decide⟩ :=
  accepted_of_selected 13 104573 ⟨327501, by decide⟩ ⟨13, 2, 0, 327501, 104573, 2061, 16384⟩
    (by decide) selected_cut_12362

theorem selected_cut_12363 : selected 8 ⟨327520, by decide⟩
    (prefixPartial 13 104574) = some ⟨13, 2, 0, 327520, 104574, 1429, 16384⟩ := by
  decide +kernel

theorem context_13_104574_327520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104574 ⟨327520, by decide⟩ :=
  accepted_of_selected 13 104574 ⟨327520, by decide⟩ ⟨13, 2, 0, 327520, 104574, 1429, 16384⟩
    (by decide) selected_cut_12363

theorem selected_cut_12364 : selected 8 ⟨327528, by decide⟩
    (prefixPartial 13 104575) = some ⟨13, 2, 0, 327528, 104575, 845, 16384⟩ := by
  decide +kernel

theorem context_13_104575_327528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104575 ⟨327528, by decide⟩ :=
  accepted_of_selected 13 104575 ⟨327528, by decide⟩ ⟨13, 2, 0, 327528, 104575, 845, 16384⟩
    (by decide) selected_cut_12364

theorem unmarked_context_12_26143_327529 : frontier 9 ⟨327529, by decide⟩
    (prefixCache 12 26143) (prefixPartial 12 26143) = false := by
  decide +kernel

theorem node_context_12_26143_327529 : EJMOriginalGlobalDAGData.nodes 9 ⟨327529, by decide⟩ =
    .split (coordinate 12) (![⟨327472, by decide⟩,⟨327501, by decide⟩,⟨327520, by decide⟩,⟨327528, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26143_327529 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26143 ⟨327529, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26143
    ⟨327529, by decide⟩ (by decide) (![⟨327472, by decide⟩,⟨327501, by decide⟩,⟨327520, by decide⟩,⟨327528, by decide⟩]) unmarked_context_12_26143_327529 node_context_12_26143_327529
  intro a
  fin_cases a
  · exact context_13_104572_327472
  · exact context_13_104573_327501
  · exact context_13_104574_327520
  · exact context_13_104575_327528

theorem unmarked_context_11_6535_327530 : frontier 10 ⟨327530, by decide⟩
    (prefixCache 11 6535) (prefixPartial 11 6535) = false := by
  decide +kernel

theorem node_context_11_6535_327530 : EJMOriginalGlobalDAGData.nodes 10 ⟨327530, by decide⟩ =
    .split (coordinate 11) (![⟨327324, by decide⟩,⟨327394, by decide⟩,⟨327452, by decide⟩,⟨327529, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6535_327530 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6535 ⟨327530, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6535
    ⟨327530, by decide⟩ (by decide) (![⟨327324, by decide⟩,⟨327394, by decide⟩,⟨327452, by decide⟩,⟨327529, by decide⟩]) unmarked_context_11_6535_327530 node_context_11_6535_327530
  intro a
  fin_cases a
  · exact context_12_26140_327324
  · exact context_12_26141_327394
  · exact context_12_26142_327452
  · exact context_12_26143_327529

theorem unmarked_context_10_1633_327531 : frontier 11 ⟨327531, by decide⟩
    (prefixCache 10 1633) (prefixPartial 10 1633) = false := by
  decide +kernel

theorem node_context_10_1633_327531 : EJMOriginalGlobalDAGData.nodes 11 ⟨327531, by decide⟩ =
    .split (coordinate 10) (![⟨326474, by decide⟩,⟨326957, by decide⟩,⟨327260, by decide⟩,⟨327530, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1633_327531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1633 ⟨327531, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1633
    ⟨327531, by decide⟩ (by decide) (![⟨326474, by decide⟩,⟨326957, by decide⟩,⟨327260, by decide⟩,⟨327530, by decide⟩]) unmarked_context_10_1633_327531 node_context_10_1633_327531
  intro a
  fin_cases a
  · exact context_11_6532_326474
  · exact context_11_6533_326957
  · exact context_11_6534_327260
  · exact context_11_6535_327530

theorem selected_cut_12365 : selected 8 ⟨327542, by decide⟩
    (prefixPartial 13 104576) = some ⟨13, 2, 0, 327542, 104576, 973, 16384⟩ := by
  decide +kernel

theorem context_13_104576_327542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104576 ⟨327542, by decide⟩ :=
  accepted_of_selected 13 104576 ⟨327542, by decide⟩ ⟨13, 2, 0, 327542, 104576, 973, 16384⟩
    (by decide) selected_cut_12365

theorem selected_cut_12366 : selected 8 ⟨327564, by decide⟩
    (prefixPartial 13 104577) = some ⟨13, 2, 0, 327564, 104577, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_104577_327564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104577 ⟨327564, by decide⟩ :=
  accepted_of_selected 13 104577 ⟨327564, by decide⟩ ⟨13, 2, 0, 327564, 104577, 1509, 16384⟩
    (by decide) selected_cut_12366

theorem selected_cut_12367 : selected 8 ⟨327574, by decide⟩
    (prefixPartial 13 104578) = some ⟨13, 2, 0, 327574, 104578, 965, 16384⟩ := by
  decide +kernel

theorem context_13_104578_327574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104578 ⟨327574, by decide⟩ :=
  accepted_of_selected 13 104578 ⟨327574, by decide⟩ ⟨13, 2, 0, 327574, 104578, 965, 16384⟩
    (by decide) selected_cut_12367

theorem selected_cut_12368 : selected 8 ⟨327578, by decide⟩
    (prefixPartial 13 104579) = some ⟨13, 2, 0, 327578, 104579, 705, 16384⟩ := by
  decide +kernel

theorem context_13_104579_327578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104579 ⟨327578, by decide⟩ :=
  accepted_of_selected 13 104579 ⟨327578, by decide⟩ ⟨13, 2, 0, 327578, 104579, 705, 16384⟩
    (by decide) selected_cut_12368

theorem unmarked_context_12_26144_327579 : frontier 9 ⟨327579, by decide⟩
    (prefixCache 12 26144) (prefixPartial 12 26144) = false := by
  decide +kernel

theorem node_context_12_26144_327579 : EJMOriginalGlobalDAGData.nodes 9 ⟨327579, by decide⟩ =
    .split (coordinate 12) (![⟨327542, by decide⟩,⟨327564, by decide⟩,⟨327574, by decide⟩,⟨327578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26144_327579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26144 ⟨327579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26144
    ⟨327579, by decide⟩ (by decide) (![⟨327542, by decide⟩,⟨327564, by decide⟩,⟨327574, by decide⟩,⟨327578, by decide⟩]) unmarked_context_12_26144_327579 node_context_12_26144_327579
  intro a
  fin_cases a
  · exact context_13_104576_327542
  · exact context_13_104577_327564
  · exact context_13_104578_327574
  · exact context_13_104579_327578

theorem selected_cut_12369 : selected 8 ⟨327593, by decide⟩
    (prefixPartial 13 104580) = some ⟨13, 2, 0, 327593, 104580, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_104580_327593 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104580 ⟨327593, by decide⟩ :=
  accepted_of_selected 13 104580 ⟨327593, by decide⟩ ⟨13, 2, 0, 327593, 104580, 1333, 16384⟩
    (by decide) selected_cut_12369

theorem selected_cut_12370 : selected 8 ⟨327624, by decide⟩
    (prefixPartial 13 104581) = some ⟨13, 2, 0, 327624, 104581, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_104581_327624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104581 ⟨327624, by decide⟩ :=
  accepted_of_selected 13 104581 ⟨327624, by decide⟩ ⟨13, 2, 0, 327624, 104581, 2277, 16384⟩
    (by decide) selected_cut_12370

theorem selected_cut_12371 : selected 8 ⟨327641, by decide⟩
    (prefixPartial 13 104582) = some ⟨13, 2, 0, 327641, 104582, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_104582_327641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104582 ⟨327641, by decide⟩ :=
  accepted_of_selected 13 104582 ⟨327641, by decide⟩ ⟨13, 2, 0, 327641, 104582, 1289, 16384⟩
    (by decide) selected_cut_12371

theorem selected_cut_12372 : selected 8 ⟨327650, by decide⟩
    (prefixPartial 13 104583) = some ⟨13, 2, 0, 327650, 104583, 857, 16384⟩ := by
  decide +kernel

theorem context_13_104583_327650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104583 ⟨327650, by decide⟩ :=
  accepted_of_selected 13 104583 ⟨327650, by decide⟩ ⟨13, 2, 0, 327650, 104583, 857, 16384⟩
    (by decide) selected_cut_12372

theorem unmarked_context_12_26145_327651 : frontier 9 ⟨327651, by decide⟩
    (prefixCache 12 26145) (prefixPartial 12 26145) = false := by
  decide +kernel

theorem node_context_12_26145_327651 : EJMOriginalGlobalDAGData.nodes 9 ⟨327651, by decide⟩ =
    .split (coordinate 12) (![⟨327593, by decide⟩,⟨327624, by decide⟩,⟨327641, by decide⟩,⟨327650, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26145_327651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26145 ⟨327651, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26145
    ⟨327651, by decide⟩ (by decide) (![⟨327593, by decide⟩,⟨327624, by decide⟩,⟨327641, by decide⟩,⟨327650, by decide⟩]) unmarked_context_12_26145_327651 node_context_12_26145_327651
  intro a
  fin_cases a
  · exact context_13_104580_327593
  · exact context_13_104581_327624
  · exact context_13_104582_327641
  · exact context_13_104583_327650

theorem selected_cut_12373 : selected 8 ⟨327664, by decide⟩
    (prefixPartial 13 104584) = some ⟨13, 2, 0, 327664, 104584, 997, 16384⟩ := by
  decide +kernel

theorem context_13_104584_327664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104584 ⟨327664, by decide⟩ :=
  accepted_of_selected 13 104584 ⟨327664, by decide⟩ ⟨13, 2, 0, 327664, 104584, 997, 16384⟩
    (by decide) selected_cut_12373

theorem selected_cut_12374 : selected 8 ⟨327686, by decide⟩
    (prefixPartial 13 104585) = some ⟨13, 2, 0, 327686, 104585, 1645, 16384⟩ := by
  decide +kernel

theorem context_13_104585_327686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104585 ⟨327686, by decide⟩ :=
  accepted_of_selected 13 104585 ⟨327686, by decide⟩ ⟨13, 2, 0, 327686, 104585, 1645, 16384⟩
    (by decide) selected_cut_12374

theorem selected_cut_12375 : selected 8 ⟨327696, by decide⟩
    (prefixPartial 13 104586) = some ⟨13, 2, 0, 327696, 104586, 889, 16384⟩ := by
  decide +kernel

theorem context_13_104586_327696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104586 ⟨327696, by decide⟩ :=
  accepted_of_selected 13 104586 ⟨327696, by decide⟩ ⟨13, 2, 0, 327696, 104586, 889, 16384⟩
    (by decide) selected_cut_12375

theorem selected_cut_12376 : selected 8 ⟨327702, by decide⟩
    (prefixPartial 13 104587) = some ⟨13, 2, 0, 327702, 104587, 769, 16384⟩ := by
  decide +kernel

theorem context_13_104587_327702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104587 ⟨327702, by decide⟩ :=
  accepted_of_selected 13 104587 ⟨327702, by decide⟩ ⟨13, 2, 0, 327702, 104587, 769, 16384⟩
    (by decide) selected_cut_12376

theorem unmarked_context_12_26146_327703 : frontier 9 ⟨327703, by decide⟩
    (prefixCache 12 26146) (prefixPartial 12 26146) = false := by
  decide +kernel

theorem node_context_12_26146_327703 : EJMOriginalGlobalDAGData.nodes 9 ⟨327703, by decide⟩ =
    .split (coordinate 12) (![⟨327664, by decide⟩,⟨327686, by decide⟩,⟨327696, by decide⟩,⟨327702, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26146_327703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26146 ⟨327703, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26146
    ⟨327703, by decide⟩ (by decide) (![⟨327664, by decide⟩,⟨327686, by decide⟩,⟨327696, by decide⟩,⟨327702, by decide⟩]) unmarked_context_12_26146_327703 node_context_12_26146_327703
  intro a
  fin_cases a
  · exact context_13_104584_327664
  · exact context_13_104585_327686
  · exact context_13_104586_327696
  · exact context_13_104587_327702

theorem selected_cut_12377 : selected 8 ⟨327714, by decide⟩
    (prefixPartial 13 104588) = some ⟨13, 2, 0, 327714, 104588, 1233, 16384⟩ := by
  decide +kernel

theorem context_13_104588_327714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104588 ⟨327714, by decide⟩ :=
  accepted_of_selected 13 104588 ⟨327714, by decide⟩ ⟨13, 2, 0, 327714, 104588, 1233, 16384⟩
    (by decide) selected_cut_12377

theorem selected_cut_12378 : selected 8 ⟨327749, by decide⟩
    (prefixPartial 13 104589) = some ⟨13, 2, 0, 327749, 104589, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_104589_327749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104589 ⟨327749, by decide⟩ :=
  accepted_of_selected 13 104589 ⟨327749, by decide⟩ ⟨13, 2, 0, 327749, 104589, 2505, 16384⟩
    (by decide) selected_cut_12378

theorem selected_cut_12379 : selected 8 ⟨327767, by decide⟩
    (prefixPartial 13 104590) = some ⟨13, 2, 0, 327767, 104590, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_104590_327767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104590 ⟨327767, by decide⟩ :=
  accepted_of_selected 13 104590 ⟨327767, by decide⟩ ⟨13, 2, 0, 327767, 104590, 1333, 16384⟩
    (by decide) selected_cut_12379

theorem selected_cut_12380 : selected 8 ⟨327771, by decide⟩
    (prefixPartial 13 104591) = some ⟨13, 2, 0, 327771, 104591, 893, 16384⟩ := by
  decide +kernel

theorem context_13_104591_327771 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104591 ⟨327771, by decide⟩ :=
  accepted_of_selected 13 104591 ⟨327771, by decide⟩ ⟨13, 2, 0, 327771, 104591, 893, 16384⟩
    (by decide) selected_cut_12380

theorem unmarked_context_12_26147_327772 : frontier 9 ⟨327772, by decide⟩
    (prefixCache 12 26147) (prefixPartial 12 26147) = false := by
  decide +kernel

theorem node_context_12_26147_327772 : EJMOriginalGlobalDAGData.nodes 9 ⟨327772, by decide⟩ =
    .split (coordinate 12) (![⟨327714, by decide⟩,⟨327749, by decide⟩,⟨327767, by decide⟩,⟨327771, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26147_327772 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26147 ⟨327772, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26147
    ⟨327772, by decide⟩ (by decide) (![⟨327714, by decide⟩,⟨327749, by decide⟩,⟨327767, by decide⟩,⟨327771, by decide⟩]) unmarked_context_12_26147_327772 node_context_12_26147_327772
  intro a
  fin_cases a
  · exact context_13_104588_327714
  · exact context_13_104589_327749
  · exact context_13_104590_327767
  · exact context_13_104591_327771

theorem unmarked_context_11_6536_327773 : frontier 10 ⟨327773, by decide⟩
    (prefixCache 11 6536) (prefixPartial 11 6536) = false := by
  decide +kernel

theorem node_context_11_6536_327773 : EJMOriginalGlobalDAGData.nodes 10 ⟨327773, by decide⟩ =
    .split (coordinate 11) (![⟨327579, by decide⟩,⟨327651, by decide⟩,⟨327703, by decide⟩,⟨327772, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6536_327773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6536 ⟨327773, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6536
    ⟨327773, by decide⟩ (by decide) (![⟨327579, by decide⟩,⟨327651, by decide⟩,⟨327703, by decide⟩,⟨327772, by decide⟩]) unmarked_context_11_6536_327773 node_context_11_6536_327773
  intro a
  fin_cases a
  · exact context_12_26144_327579
  · exact context_12_26145_327651
  · exact context_12_26146_327703
  · exact context_12_26147_327772

theorem selected_cut_12381 : selected 8 ⟨327783, by decide⟩
    (prefixPartial 13 104592) = some ⟨13, 2, 0, 327783, 104592, 773, 16384⟩ := by
  decide +kernel

theorem context_13_104592_327783 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104592 ⟨327783, by decide⟩ :=
  accepted_of_selected 13 104592 ⟨327783, by decide⟩ ⟨13, 2, 0, 327783, 104592, 773, 16384⟩
    (by decide) selected_cut_12381

theorem selected_cut_12382 : selected 8 ⟨327806, by decide⟩
    (prefixPartial 13 104593) = some ⟨13, 2, 0, 327806, 104593, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_104593_327806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104593 ⟨327806, by decide⟩ :=
  accepted_of_selected 13 104593 ⟨327806, by decide⟩ ⟨13, 2, 0, 327806, 104593, 1861, 16384⟩
    (by decide) selected_cut_12382

theorem selected_cut_12383 : selected 8 ⟨327817, by decide⟩
    (prefixPartial 13 104594) = some ⟨13, 2, 0, 327817, 104594, 1093, 16384⟩ := by
  decide +kernel

theorem context_13_104594_327817 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104594 ⟨327817, by decide⟩ :=
  accepted_of_selected 13 104594 ⟨327817, by decide⟩ ⟨13, 2, 0, 327817, 104594, 1093, 16384⟩
    (by decide) selected_cut_12383

theorem selected_cut_12384 : selected 8 ⟨327821, by decide⟩
    (prefixPartial 13 104595) = some ⟨13, 2, 0, 327821, 104595, 741, 16384⟩ := by
  decide +kernel

theorem context_13_104595_327821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104595 ⟨327821, by decide⟩ :=
  accepted_of_selected 13 104595 ⟨327821, by decide⟩ ⟨13, 2, 0, 327821, 104595, 741, 16384⟩
    (by decide) selected_cut_12384

theorem unmarked_context_12_26148_327822 : frontier 9 ⟨327822, by decide⟩
    (prefixCache 12 26148) (prefixPartial 12 26148) = false := by
  decide +kernel

theorem node_context_12_26148_327822 : EJMOriginalGlobalDAGData.nodes 9 ⟨327822, by decide⟩ =
    .split (coordinate 12) (![⟨327783, by decide⟩,⟨327806, by decide⟩,⟨327817, by decide⟩,⟨327821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_26148_327822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 26148 ⟨327822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 26148
    ⟨327822, by decide⟩ (by decide) (![⟨327783, by decide⟩,⟨327806, by decide⟩,⟨327817, by decide⟩,⟨327821, by decide⟩]) unmarked_context_12_26148_327822 node_context_12_26148_327822
  intro a
  fin_cases a
  · exact context_13_104592_327783
  · exact context_13_104593_327806
  · exact context_13_104594_327817
  · exact context_13_104595_327821

theorem selected_cut_12385 : selected 8 ⟨327832, by decide⟩
    (prefixPartial 13 104596) = some ⟨13, 2, 0, 327832, 104596, 1025, 16384⟩ := by
  decide +kernel

theorem context_13_104596_327832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104596 ⟨327832, by decide⟩ :=
  accepted_of_selected 13 104596 ⟨327832, by decide⟩ ⟨13, 2, 0, 327832, 104596, 1025, 16384⟩
    (by decide) selected_cut_12385

theorem selected_cut_12386 : selected 8 ⟨327857, by decide⟩
    (prefixPartial 13 104597) = some ⟨13, 2, 0, 327857, 104597, 2089, 16384⟩ := by
  decide +kernel

theorem context_13_104597_327857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 104597 ⟨327857, by decide⟩ :=
  accepted_of_selected 13 104597 ⟨327857, by decide⟩ ⟨13, 2, 0, 327857, 104597, 2089, 16384⟩
    (by decide) selected_cut_12386

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
