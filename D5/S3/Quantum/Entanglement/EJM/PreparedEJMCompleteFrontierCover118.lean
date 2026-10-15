/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover117
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_25619_304034 : frontier 9 ⟨304034, by decide⟩
    (prefixCache 12 25619) (prefixPartial 12 25619) = false := by
  decide +kernel

theorem node_context_12_25619_304034 : EJMOriginalGlobalDAGData.nodes 9 ⟨304034, by decide⟩ =
    .split (coordinate 12) (![⟨303975, by decide⟩,⟨304003, by decide⟩,⟨304025, by decide⟩,⟨304033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25619_304034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25619 ⟨304034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25619
    ⟨304034, by decide⟩ (by decide) (![⟨303975, by decide⟩,⟨304003, by decide⟩,⟨304025, by decide⟩,⟨304033, by decide⟩]) unmarked_context_12_25619_304034 node_context_12_25619_304034
  intro a
  fin_cases a
  · exact context_13_102476_303975
  · exact context_13_102477_304003
  · exact context_13_102478_304025
  · exact context_13_102479_304033

theorem unmarked_context_11_6404_304035 : frontier 10 ⟨304035, by decide⟩
    (prefixCache 11 6404) (prefixPartial 11 6404) = false := by
  decide +kernel

theorem node_context_11_6404_304035 : EJMOriginalGlobalDAGData.nodes 10 ⟨304035, by decide⟩ =
    .split (coordinate 11) (![⟨266170, by decide⟩,⟨303873, by decide⟩,⟨303956, by decide⟩,⟨304034, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6404_304035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6404 ⟨304035, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6404
    ⟨304035, by decide⟩ (by decide) (![⟨266170, by decide⟩,⟨303873, by decide⟩,⟨303956, by decide⟩,⟨304034, by decide⟩]) unmarked_context_11_6404_304035 node_context_11_6404_304035
  intro a
  fin_cases a
  · exact context_12_25616_266170
  · exact context_12_25617_303873
  · exact context_12_25618_303956
  · exact context_12_25619_304034

theorem selected_cut_11331 : selected 8 ⟨304059, by decide⟩
    (prefixPartial 13 102480) = some ⟨13, 2, 0, 304059, 102480, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_102480_304059 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102480 ⟨304059, by decide⟩ :=
  accepted_of_selected 13 102480 ⟨304059, by decide⟩ ⟨13, 2, 0, 304059, 102480, 1601, 16384⟩
    (by decide) selected_cut_11331

theorem selected_cut_11332 : selected 8 ⟨304107, by decide⟩
    (prefixPartial 13 102481) = some ⟨13, 2, 0, 304107, 102481, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_102481_304107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102481 ⟨304107, by decide⟩ :=
  accepted_of_selected 13 102481 ⟨304107, by decide⟩ ⟨13, 2, 0, 304107, 102481, 2809, 16384⟩
    (by decide) selected_cut_11332

theorem selected_cut_11333 : selected 8 ⟨304130, by decide⟩
    (prefixPartial 13 102482) = some ⟨13, 2, 0, 304130, 102482, 1637, 16384⟩ := by
  decide +kernel

theorem context_13_102482_304130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102482 ⟨304130, by decide⟩ :=
  accepted_of_selected 13 102482 ⟨304130, by decide⟩ ⟨13, 2, 0, 304130, 102482, 1637, 16384⟩
    (by decide) selected_cut_11333

theorem selected_cut_11334 : selected 8 ⟨304144, by decide⟩
    (prefixPartial 13 102483) = some ⟨13, 2, 0, 304144, 102483, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_102483_304144 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102483 ⟨304144, by decide⟩ :=
  accepted_of_selected 13 102483 ⟨304144, by decide⟩ ⟨13, 2, 0, 304144, 102483, 1013, 16384⟩
    (by decide) selected_cut_11334

theorem unmarked_context_12_25620_304145 : frontier 9 ⟨304145, by decide⟩
    (prefixCache 12 25620) (prefixPartial 12 25620) = false := by
  decide +kernel

theorem node_context_12_25620_304145 : EJMOriginalGlobalDAGData.nodes 9 ⟨304145, by decide⟩ =
    .split (coordinate 12) (![⟨304059, by decide⟩,⟨304107, by decide⟩,⟨304130, by decide⟩,⟨304144, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25620_304145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25620 ⟨304145, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25620
    ⟨304145, by decide⟩ (by decide) (![⟨304059, by decide⟩,⟨304107, by decide⟩,⟨304130, by decide⟩,⟨304144, by decide⟩]) unmarked_context_12_25620_304145 node_context_12_25620_304145
  intro a
  fin_cases a
  · exact context_13_102480_304059
  · exact context_13_102481_304107
  · exact context_13_102482_304130
  · exact context_13_102483_304144

theorem selected_cut_11335 : selected 9 ⟨68180, by decide⟩
    (prefixPartial 12 25621) = some ⟨12, 1, 0, 68180, 25621, 1, 65536⟩ := by
  decide +kernel

theorem context_12_25621_68180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25621 ⟨68180, by decide⟩ :=
  accepted_of_selected 12 25621 ⟨68180, by decide⟩ ⟨12, 1, 0, 68180, 25621, 1, 65536⟩
    (by decide) selected_cut_11335

theorem selected_cut_11336 : selected 8 ⟨304193, by decide⟩
    (prefixPartial 13 102488) = some ⟨13, 2, 0, 304193, 102488, 2225, 16384⟩ := by
  decide +kernel

theorem context_13_102488_304193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102488 ⟨304193, by decide⟩ :=
  accepted_of_selected 13 102488 ⟨304193, by decide⟩ ⟨13, 2, 0, 304193, 102488, 2225, 16384⟩
    (by decide) selected_cut_11336

theorem selected_cut_11337 : selected 8 ⟨304248, by decide⟩
    (prefixPartial 13 102489) = some ⟨13, 2, 0, 304248, 102489, 2917, 16384⟩ := by
  decide +kernel

theorem context_13_102489_304248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102489 ⟨304248, by decide⟩ :=
  accepted_of_selected 13 102489 ⟨304248, by decide⟩ ⟨13, 2, 0, 304248, 102489, 2917, 16384⟩
    (by decide) selected_cut_11337

theorem selected_cut_11338 : selected 8 ⟨304270, by decide⟩
    (prefixPartial 13 102490) = some ⟨13, 2, 0, 304270, 102490, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_102490_304270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102490 ⟨304270, by decide⟩ :=
  accepted_of_selected 13 102490 ⟨304270, by decide⟩ ⟨13, 2, 0, 304270, 102490, 1889, 16384⟩
    (by decide) selected_cut_11338

theorem selected_cut_11339 : selected 8 ⟨304279, by decide⟩
    (prefixPartial 13 102491) = some ⟨13, 2, 0, 304279, 102491, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_102491_304279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102491 ⟨304279, by decide⟩ :=
  accepted_of_selected 13 102491 ⟨304279, by decide⟩ ⟨13, 2, 0, 304279, 102491, 1161, 16384⟩
    (by decide) selected_cut_11339

theorem unmarked_context_12_25622_304280 : frontier 9 ⟨304280, by decide⟩
    (prefixCache 12 25622) (prefixPartial 12 25622) = false := by
  decide +kernel

theorem node_context_12_25622_304280 : EJMOriginalGlobalDAGData.nodes 9 ⟨304280, by decide⟩ =
    .split (coordinate 12) (![⟨304193, by decide⟩,⟨304248, by decide⟩,⟨304270, by decide⟩,⟨304279, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25622_304280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25622 ⟨304280, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25622
    ⟨304280, by decide⟩ (by decide) (![⟨304193, by decide⟩,⟨304248, by decide⟩,⟨304270, by decide⟩,⟨304279, by decide⟩]) unmarked_context_12_25622_304280 node_context_12_25622_304280
  intro a
  fin_cases a
  · exact context_13_102488_304193
  · exact context_13_102489_304248
  · exact context_13_102490_304270
  · exact context_13_102491_304279

theorem selected_cut_11340 : selected 8 ⟨304327, by decide⟩
    (prefixPartial 13 102492) = some ⟨13, 2, 0, 304327, 102492, 2529, 16384⟩ := by
  decide +kernel

theorem context_13_102492_304327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102492 ⟨304327, by decide⟩ :=
  accepted_of_selected 13 102492 ⟨304327, by decide⟩ ⟨13, 2, 0, 304327, 102492, 2529, 16384⟩
    (by decide) selected_cut_11340

theorem selected_cut_11341 : selected 8 ⟨304404, by decide⟩
    (prefixPartial 13 102493) = some ⟨13, 2, 0, 304404, 102493, 3425, 16384⟩ := by
  decide +kernel

theorem context_13_102493_304404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102493 ⟨304404, by decide⟩ :=
  accepted_of_selected 13 102493 ⟨304404, by decide⟩ ⟨13, 2, 0, 304404, 102493, 3425, 16384⟩
    (by decide) selected_cut_11341

theorem selected_cut_11342 : selected 8 ⟨304433, by decide⟩
    (prefixPartial 13 102494) = some ⟨13, 2, 0, 304433, 102494, 2141, 16384⟩ := by
  decide +kernel

theorem context_13_102494_304433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102494 ⟨304433, by decide⟩ :=
  accepted_of_selected 13 102494 ⟨304433, by decide⟩ ⟨13, 2, 0, 304433, 102494, 2141, 16384⟩
    (by decide) selected_cut_11342

theorem selected_cut_11343 : selected 8 ⟨304445, by decide⟩
    (prefixPartial 13 102495) = some ⟨13, 2, 0, 304445, 102495, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_102495_304445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102495 ⟨304445, by decide⟩ :=
  accepted_of_selected 13 102495 ⟨304445, by decide⟩ ⟨13, 2, 0, 304445, 102495, 1165, 16384⟩
    (by decide) selected_cut_11343

theorem unmarked_context_12_25623_304446 : frontier 9 ⟨304446, by decide⟩
    (prefixCache 12 25623) (prefixPartial 12 25623) = false := by
  decide +kernel

theorem node_context_12_25623_304446 : EJMOriginalGlobalDAGData.nodes 9 ⟨304446, by decide⟩ =
    .split (coordinate 12) (![⟨304327, by decide⟩,⟨304404, by decide⟩,⟨304433, by decide⟩,⟨304445, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25623_304446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25623 ⟨304446, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25623
    ⟨304446, by decide⟩ (by decide) (![⟨304327, by decide⟩,⟨304404, by decide⟩,⟨304433, by decide⟩,⟨304445, by decide⟩]) unmarked_context_12_25623_304446 node_context_12_25623_304446
  intro a
  fin_cases a
  · exact context_13_102492_304327
  · exact context_13_102493_304404
  · exact context_13_102494_304433
  · exact context_13_102495_304445

theorem unmarked_context_11_6405_304447 : frontier 10 ⟨304447, by decide⟩
    (prefixCache 11 6405) (prefixPartial 11 6405) = false := by
  decide +kernel

theorem node_context_11_6405_304447 : EJMOriginalGlobalDAGData.nodes 10 ⟨304447, by decide⟩ =
    .split (coordinate 11) (![⟨304145, by decide⟩,⟨68180, by decide⟩,⟨304280, by decide⟩,⟨304446, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6405_304447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6405 ⟨304447, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6405
    ⟨304447, by decide⟩ (by decide) (![⟨304145, by decide⟩,⟨68180, by decide⟩,⟨304280, by decide⟩,⟨304446, by decide⟩]) unmarked_context_11_6405_304447 node_context_11_6405_304447
  intro a
  fin_cases a
  · exact context_12_25620_304145
  · exact context_12_25621_68180
  · exact context_12_25622_304280
  · exact context_12_25623_304446

theorem selected_cut_11344 : selected 8 ⟨304462, by decide⟩
    (prefixPartial 13 102496) = some ⟨13, 2, 0, 304462, 102496, 917, 16384⟩ := by
  decide +kernel

theorem context_13_102496_304462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102496 ⟨304462, by decide⟩ :=
  accepted_of_selected 13 102496 ⟨304462, by decide⟩ ⟨13, 2, 0, 304462, 102496, 917, 16384⟩
    (by decide) selected_cut_11344

theorem selected_cut_11345 : selected 8 ⟨304488, by decide⟩
    (prefixPartial 13 102497) = some ⟨13, 2, 0, 304488, 102497, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_102497_304488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102497 ⟨304488, by decide⟩ :=
  accepted_of_selected 13 102497 ⟨304488, by decide⟩ ⟨13, 2, 0, 304488, 102497, 1709, 16384⟩
    (by decide) selected_cut_11345

theorem selected_cut_11346 : selected 8 ⟨304505, by decide⟩
    (prefixPartial 13 102498) = some ⟨13, 2, 0, 304505, 102498, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_102498_304505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102498 ⟨304505, by decide⟩ :=
  accepted_of_selected 13 102498 ⟨304505, by decide⟩ ⟨13, 2, 0, 304505, 102498, 1285, 16384⟩
    (by decide) selected_cut_11346

theorem selected_cut_11347 : selected 8 ⟨304513, by decide⟩
    (prefixPartial 13 102499) = some ⟨13, 2, 0, 304513, 102499, 913, 16384⟩ := by
  decide +kernel

theorem context_13_102499_304513 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102499 ⟨304513, by decide⟩ :=
  accepted_of_selected 13 102499 ⟨304513, by decide⟩ ⟨13, 2, 0, 304513, 102499, 913, 16384⟩
    (by decide) selected_cut_11347

theorem unmarked_context_12_25624_304514 : frontier 9 ⟨304514, by decide⟩
    (prefixCache 12 25624) (prefixPartial 12 25624) = false := by
  decide +kernel

theorem node_context_12_25624_304514 : EJMOriginalGlobalDAGData.nodes 9 ⟨304514, by decide⟩ =
    .split (coordinate 12) (![⟨304462, by decide⟩,⟨304488, by decide⟩,⟨304505, by decide⟩,⟨304513, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25624_304514 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25624 ⟨304514, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25624
    ⟨304514, by decide⟩ (by decide) (![⟨304462, by decide⟩,⟨304488, by decide⟩,⟨304505, by decide⟩,⟨304513, by decide⟩]) unmarked_context_12_25624_304514 node_context_12_25624_304514
  intro a
  fin_cases a
  · exact context_13_102496_304462
  · exact context_13_102497_304488
  · exact context_13_102498_304505
  · exact context_13_102499_304513

theorem selected_cut_11348 : selected 8 ⟨304528, by decide⟩
    (prefixPartial 13 102500) = some ⟨13, 2, 0, 304528, 102500, 1197, 16384⟩ := by
  decide +kernel

theorem context_13_102500_304528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102500 ⟨304528, by decide⟩ :=
  accepted_of_selected 13 102500 ⟨304528, by decide⟩ ⟨13, 2, 0, 304528, 102500, 1197, 16384⟩
    (by decide) selected_cut_11348

theorem selected_cut_11349 : selected 8 ⟨304559, by decide⟩
    (prefixPartial 13 102501) = some ⟨13, 2, 0, 304559, 102501, 1641, 16384⟩ := by
  decide +kernel

theorem context_13_102501_304559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102501 ⟨304559, by decide⟩ :=
  accepted_of_selected 13 102501 ⟨304559, by decide⟩ ⟨13, 2, 0, 304559, 102501, 1641, 16384⟩
    (by decide) selected_cut_11349

theorem selected_cut_11350 : selected 8 ⟨304576, by decide⟩
    (prefixPartial 13 102502) = some ⟨13, 2, 0, 304576, 102502, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_102502_304576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102502 ⟨304576, by decide⟩ :=
  accepted_of_selected 13 102502 ⟨304576, by decide⟩ ⟨13, 2, 0, 304576, 102502, 1337, 16384⟩
    (by decide) selected_cut_11350

theorem selected_cut_11351 : selected 8 ⟨304584, by decide⟩
    (prefixPartial 13 102503) = some ⟨13, 2, 0, 304584, 102503, 841, 16384⟩ := by
  decide +kernel

theorem context_13_102503_304584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102503 ⟨304584, by decide⟩ :=
  accepted_of_selected 13 102503 ⟨304584, by decide⟩ ⟨13, 2, 0, 304584, 102503, 841, 16384⟩
    (by decide) selected_cut_11351

theorem unmarked_context_12_25625_304585 : frontier 9 ⟨304585, by decide⟩
    (prefixCache 12 25625) (prefixPartial 12 25625) = false := by
  decide +kernel

theorem node_context_12_25625_304585 : EJMOriginalGlobalDAGData.nodes 9 ⟨304585, by decide⟩ =
    .split (coordinate 12) (![⟨304528, by decide⟩,⟨304559, by decide⟩,⟨304576, by decide⟩,⟨304584, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25625_304585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25625 ⟨304585, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25625
    ⟨304585, by decide⟩ (by decide) (![⟨304528, by decide⟩,⟨304559, by decide⟩,⟨304576, by decide⟩,⟨304584, by decide⟩]) unmarked_context_12_25625_304585 node_context_12_25625_304585
  intro a
  fin_cases a
  · exact context_13_102500_304528
  · exact context_13_102501_304559
  · exact context_13_102502_304576
  · exact context_13_102503_304584

theorem selected_cut_11352 : selected 8 ⟨304602, by decide⟩
    (prefixPartial 13 102504) = some ⟨13, 2, 0, 304602, 102504, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_102504_304602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102504 ⟨304602, by decide⟩ :=
  accepted_of_selected 13 102504 ⟨304602, by decide⟩ ⟨13, 2, 0, 304602, 102504, 1125, 16384⟩
    (by decide) selected_cut_11352

theorem selected_cut_11353 : selected 8 ⟨304632, by decide⟩
    (prefixPartial 13 102505) = some ⟨13, 2, 0, 304632, 102505, 1813, 16384⟩ := by
  decide +kernel

theorem context_13_102505_304632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102505 ⟨304632, by decide⟩ :=
  accepted_of_selected 13 102505 ⟨304632, by decide⟩ ⟨13, 2, 0, 304632, 102505, 1813, 16384⟩
    (by decide) selected_cut_11353

theorem selected_cut_11354 : selected 8 ⟨304646, by decide⟩
    (prefixPartial 13 102506) = some ⟨13, 2, 0, 304646, 102506, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_102506_304646 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102506 ⟨304646, by decide⟩ :=
  accepted_of_selected 13 102506 ⟨304646, by decide⟩ ⟨13, 2, 0, 304646, 102506, 1193, 16384⟩
    (by decide) selected_cut_11354

theorem selected_cut_11355 : selected 8 ⟨304651, by decide⟩
    (prefixPartial 13 102507) = some ⟨13, 2, 0, 304651, 102507, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_102507_304651 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102507 ⟨304651, by decide⟩ :=
  accepted_of_selected 13 102507 ⟨304651, by decide⟩ ⟨13, 2, 0, 304651, 102507, 1013, 16384⟩
    (by decide) selected_cut_11355

theorem unmarked_context_12_25626_304652 : frontier 9 ⟨304652, by decide⟩
    (prefixCache 12 25626) (prefixPartial 12 25626) = false := by
  decide +kernel

theorem node_context_12_25626_304652 : EJMOriginalGlobalDAGData.nodes 9 ⟨304652, by decide⟩ =
    .split (coordinate 12) (![⟨304602, by decide⟩,⟨304632, by decide⟩,⟨304646, by decide⟩,⟨304651, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25626_304652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25626 ⟨304652, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25626
    ⟨304652, by decide⟩ (by decide) (![⟨304602, by decide⟩,⟨304632, by decide⟩,⟨304646, by decide⟩,⟨304651, by decide⟩]) unmarked_context_12_25626_304652 node_context_12_25626_304652
  intro a
  fin_cases a
  · exact context_13_102504_304602
  · exact context_13_102505_304632
  · exact context_13_102506_304646
  · exact context_13_102507_304651

theorem selected_cut_11356 : selected 8 ⟨304669, by decide⟩
    (prefixPartial 13 102508) = some ⟨13, 2, 0, 304669, 102508, 1269, 16384⟩ := by
  decide +kernel

theorem context_13_102508_304669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102508 ⟨304669, by decide⟩ :=
  accepted_of_selected 13 102508 ⟨304669, by decide⟩ ⟨13, 2, 0, 304669, 102508, 1269, 16384⟩
    (by decide) selected_cut_11356

theorem selected_cut_11357 : selected 8 ⟨304703, by decide⟩
    (prefixPartial 13 102509) = some ⟨13, 2, 0, 304703, 102509, 2101, 16384⟩ := by
  decide +kernel

theorem context_13_102509_304703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102509 ⟨304703, by decide⟩ :=
  accepted_of_selected 13 102509 ⟨304703, by decide⟩ ⟨13, 2, 0, 304703, 102509, 2101, 16384⟩
    (by decide) selected_cut_11357

theorem selected_cut_11358 : selected 8 ⟨304726, by decide⟩
    (prefixPartial 13 102510) = some ⟨13, 2, 0, 304726, 102510, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_102510_304726 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102510 ⟨304726, by decide⟩ :=
  accepted_of_selected 13 102510 ⟨304726, by decide⟩ ⟨13, 2, 0, 304726, 102510, 1461, 16384⟩
    (by decide) selected_cut_11358

theorem selected_cut_11359 : selected 8 ⟨304733, by decide⟩
    (prefixPartial 13 102511) = some ⟨13, 2, 0, 304733, 102511, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_102511_304733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102511 ⟨304733, by decide⟩ :=
  accepted_of_selected 13 102511 ⟨304733, by decide⟩ ⟨13, 2, 0, 304733, 102511, 1009, 16384⟩
    (by decide) selected_cut_11359

theorem unmarked_context_12_25627_304734 : frontier 9 ⟨304734, by decide⟩
    (prefixCache 12 25627) (prefixPartial 12 25627) = false := by
  decide +kernel

theorem node_context_12_25627_304734 : EJMOriginalGlobalDAGData.nodes 9 ⟨304734, by decide⟩ =
    .split (coordinate 12) (![⟨304669, by decide⟩,⟨304703, by decide⟩,⟨304726, by decide⟩,⟨304733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25627_304734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25627 ⟨304734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25627
    ⟨304734, by decide⟩ (by decide) (![⟨304669, by decide⟩,⟨304703, by decide⟩,⟨304726, by decide⟩,⟨304733, by decide⟩]) unmarked_context_12_25627_304734 node_context_12_25627_304734
  intro a
  fin_cases a
  · exact context_13_102508_304669
  · exact context_13_102509_304703
  · exact context_13_102510_304726
  · exact context_13_102511_304733

theorem unmarked_context_11_6406_304735 : frontier 10 ⟨304735, by decide⟩
    (prefixCache 11 6406) (prefixPartial 11 6406) = false := by
  decide +kernel

theorem node_context_11_6406_304735 : EJMOriginalGlobalDAGData.nodes 10 ⟨304735, by decide⟩ =
    .split (coordinate 11) (![⟨304514, by decide⟩,⟨304585, by decide⟩,⟨304652, by decide⟩,⟨304734, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6406_304735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6406 ⟨304735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6406
    ⟨304735, by decide⟩ (by decide) (![⟨304514, by decide⟩,⟨304585, by decide⟩,⟨304652, by decide⟩,⟨304734, by decide⟩]) unmarked_context_11_6406_304735 node_context_11_6406_304735
  intro a
  fin_cases a
  · exact context_12_25624_304514
  · exact context_12_25625_304585
  · exact context_12_25626_304652
  · exact context_12_25627_304734

theorem selected_cut_11360 : selected 9 ⟨304792, by decide⟩
    (prefixPartial 12 25628) = some ⟨12, 2, 0, 304792, 25628, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_25628_304792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25628 ⟨304792, by decide⟩ :=
  accepted_of_selected 12 25628 ⟨304792, by decide⟩ ⟨12, 2, 0, 304792, 25628, 4077, 65536⟩
    (by decide) selected_cut_11360

theorem selected_cut_11361 : selected 8 ⟨304806, by decide⟩
    (prefixPartial 13 102516) = some ⟨13, 2, 0, 304806, 102516, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_102516_304806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102516 ⟨304806, by decide⟩ :=
  accepted_of_selected 13 102516 ⟨304806, by decide⟩ ⟨13, 2, 0, 304806, 102516, 1105, 16384⟩
    (by decide) selected_cut_11361

theorem selected_cut_11362 : selected 8 ⟨304836, by decide⟩
    (prefixPartial 13 102517) = some ⟨13, 2, 0, 304836, 102517, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_102517_304836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102517 ⟨304836, by decide⟩ :=
  accepted_of_selected 13 102517 ⟨304836, by decide⟩ ⟨13, 2, 0, 304836, 102517, 1537, 16384⟩
    (by decide) selected_cut_11362

theorem selected_cut_11363 : selected 8 ⟨304855, by decide⟩
    (prefixPartial 13 102518) = some ⟨13, 2, 0, 304855, 102518, 1281, 16384⟩ := by
  decide +kernel

theorem context_13_102518_304855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102518 ⟨304855, by decide⟩ :=
  accepted_of_selected 13 102518 ⟨304855, by decide⟩ ⟨13, 2, 0, 304855, 102518, 1281, 16384⟩
    (by decide) selected_cut_11363

theorem selected_cut_11364 : selected 8 ⟨304861, by decide⟩
    (prefixPartial 13 102519) = some ⟨13, 2, 0, 304861, 102519, 673, 16384⟩ := by
  decide +kernel

theorem context_13_102519_304861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102519 ⟨304861, by decide⟩ :=
  accepted_of_selected 13 102519 ⟨304861, by decide⟩ ⟨13, 2, 0, 304861, 102519, 673, 16384⟩
    (by decide) selected_cut_11364

theorem unmarked_context_12_25629_304862 : frontier 9 ⟨304862, by decide⟩
    (prefixCache 12 25629) (prefixPartial 12 25629) = false := by
  decide +kernel

theorem node_context_12_25629_304862 : EJMOriginalGlobalDAGData.nodes 9 ⟨304862, by decide⟩ =
    .split (coordinate 12) (![⟨304806, by decide⟩,⟨304836, by decide⟩,⟨304855, by decide⟩,⟨304861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25629_304862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25629 ⟨304862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25629
    ⟨304862, by decide⟩ (by decide) (![⟨304806, by decide⟩,⟨304836, by decide⟩,⟨304855, by decide⟩,⟨304861, by decide⟩]) unmarked_context_12_25629_304862 node_context_12_25629_304862
  intro a
  fin_cases a
  · exact context_13_102516_304806
  · exact context_13_102517_304836
  · exact context_13_102518_304855
  · exact context_13_102519_304861

theorem selected_cut_11365 : selected 8 ⟨304878, by decide⟩
    (prefixPartial 13 102520) = some ⟨13, 2, 0, 304878, 102520, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_102520_304878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102520 ⟨304878, by decide⟩ :=
  accepted_of_selected 13 102520 ⟨304878, by decide⟩ ⟨13, 2, 0, 304878, 102520, 1017, 16384⟩
    (by decide) selected_cut_11365

theorem selected_cut_11366 : selected 8 ⟨304904, by decide⟩
    (prefixPartial 13 102521) = some ⟨13, 2, 0, 304904, 102521, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_102521_304904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102521 ⟨304904, by decide⟩ :=
  accepted_of_selected 13 102521 ⟨304904, by decide⟩ ⟨13, 2, 0, 304904, 102521, 1761, 16384⟩
    (by decide) selected_cut_11366

theorem selected_cut_11367 : selected 8 ⟨304922, by decide⟩
    (prefixPartial 13 102522) = some ⟨13, 2, 0, 304922, 102522, 1297, 16384⟩ := by
  decide +kernel

theorem context_13_102522_304922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102522 ⟨304922, by decide⟩ :=
  accepted_of_selected 13 102522 ⟨304922, by decide⟩ ⟨13, 2, 0, 304922, 102522, 1297, 16384⟩
    (by decide) selected_cut_11367

theorem selected_cut_11368 : selected 8 ⟨304934, by decide⟩
    (prefixPartial 13 102523) = some ⟨13, 2, 0, 304934, 102523, 837, 16384⟩ := by
  decide +kernel

theorem context_13_102523_304934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102523 ⟨304934, by decide⟩ :=
  accepted_of_selected 13 102523 ⟨304934, by decide⟩ ⟨13, 2, 0, 304934, 102523, 837, 16384⟩
    (by decide) selected_cut_11368

theorem unmarked_context_12_25630_304935 : frontier 9 ⟨304935, by decide⟩
    (prefixCache 12 25630) (prefixPartial 12 25630) = false := by
  decide +kernel

theorem node_context_12_25630_304935 : EJMOriginalGlobalDAGData.nodes 9 ⟨304935, by decide⟩ =
    .split (coordinate 12) (![⟨304878, by decide⟩,⟨304904, by decide⟩,⟨304922, by decide⟩,⟨304934, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25630_304935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25630 ⟨304935, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25630
    ⟨304935, by decide⟩ (by decide) (![⟨304878, by decide⟩,⟨304904, by decide⟩,⟨304922, by decide⟩,⟨304934, by decide⟩]) unmarked_context_12_25630_304935 node_context_12_25630_304935
  intro a
  fin_cases a
  · exact context_13_102520_304878
  · exact context_13_102521_304904
  · exact context_13_102522_304922
  · exact context_13_102523_304934

theorem selected_cut_11369 : selected 8 ⟨304951, by decide⟩
    (prefixPartial 13 102524) = some ⟨13, 2, 0, 304951, 102524, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_102524_304951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102524 ⟨304951, by decide⟩ :=
  accepted_of_selected 13 102524 ⟨304951, by decide⟩ ⟨13, 2, 0, 304951, 102524, 1049, 16384⟩
    (by decide) selected_cut_11369

theorem selected_cut_11370 : selected 8 ⟨304982, by decide⟩
    (prefixPartial 13 102525) = some ⟨13, 2, 0, 304982, 102525, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_102525_304982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102525 ⟨304982, by decide⟩ :=
  accepted_of_selected 13 102525 ⟨304982, by decide⟩ ⟨13, 2, 0, 304982, 102525, 1877, 16384⟩
    (by decide) selected_cut_11370

theorem selected_cut_11371 : selected 8 ⟨305002, by decide⟩
    (prefixPartial 13 102526) = some ⟨13, 2, 0, 305002, 102526, 1457, 16384⟩ := by
  decide +kernel

theorem context_13_102526_305002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102526 ⟨305002, by decide⟩ :=
  accepted_of_selected 13 102526 ⟨305002, by decide⟩ ⟨13, 2, 0, 305002, 102526, 1457, 16384⟩
    (by decide) selected_cut_11371

theorem selected_cut_11372 : selected 8 ⟨305010, by decide⟩
    (prefixPartial 13 102527) = some ⟨13, 2, 0, 305010, 102527, 749, 16384⟩ := by
  decide +kernel

theorem context_13_102527_305010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102527 ⟨305010, by decide⟩ :=
  accepted_of_selected 13 102527 ⟨305010, by decide⟩ ⟨13, 2, 0, 305010, 102527, 749, 16384⟩
    (by decide) selected_cut_11372

theorem unmarked_context_12_25631_305011 : frontier 9 ⟨305011, by decide⟩
    (prefixCache 12 25631) (prefixPartial 12 25631) = false := by
  decide +kernel

theorem node_context_12_25631_305011 : EJMOriginalGlobalDAGData.nodes 9 ⟨305011, by decide⟩ =
    .split (coordinate 12) (![⟨304951, by decide⟩,⟨304982, by decide⟩,⟨305002, by decide⟩,⟨305010, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25631_305011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25631 ⟨305011, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25631
    ⟨305011, by decide⟩ (by decide) (![⟨304951, by decide⟩,⟨304982, by decide⟩,⟨305002, by decide⟩,⟨305010, by decide⟩]) unmarked_context_12_25631_305011 node_context_12_25631_305011
  intro a
  fin_cases a
  · exact context_13_102524_304951
  · exact context_13_102525_304982
  · exact context_13_102526_305002
  · exact context_13_102527_305010

theorem unmarked_context_11_6407_305012 : frontier 10 ⟨305012, by decide⟩
    (prefixCache 11 6407) (prefixPartial 11 6407) = false := by
  decide +kernel

theorem node_context_11_6407_305012 : EJMOriginalGlobalDAGData.nodes 10 ⟨305012, by decide⟩ =
    .split (coordinate 11) (![⟨304792, by decide⟩,⟨304862, by decide⟩,⟨304935, by decide⟩,⟨305011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6407_305012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6407 ⟨305012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6407
    ⟨305012, by decide⟩ (by decide) (![⟨304792, by decide⟩,⟨304862, by decide⟩,⟨304935, by decide⟩,⟨305011, by decide⟩]) unmarked_context_11_6407_305012 node_context_11_6407_305012
  intro a
  fin_cases a
  · exact context_12_25628_304792
  · exact context_12_25629_304862
  · exact context_12_25630_304935
  · exact context_12_25631_305011

theorem unmarked_context_10_1601_305013 : frontier 11 ⟨305013, by decide⟩
    (prefixCache 10 1601) (prefixPartial 10 1601) = false := by
  decide +kernel

theorem node_context_10_1601_305013 : EJMOriginalGlobalDAGData.nodes 11 ⟨305013, by decide⟩ =
    .split (coordinate 10) (![⟨304035, by decide⟩,⟨304447, by decide⟩,⟨304735, by decide⟩,⟨305012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1601_305013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1601 ⟨305013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1601
    ⟨305013, by decide⟩ (by decide) (![⟨304035, by decide⟩,⟨304447, by decide⟩,⟨304735, by decide⟩,⟨305012, by decide⟩]) unmarked_context_10_1601_305013 node_context_10_1601_305013
  intro a
  fin_cases a
  · exact context_11_6404_304035
  · exact context_11_6405_304447
  · exact context_11_6406_304735
  · exact context_11_6407_305012

theorem selected_cut_11373 : selected 8 ⟨305030, by decide⟩
    (prefixPartial 13 102528) = some ⟨13, 2, 0, 305030, 102528, 1017, 16384⟩ := by
  decide +kernel

theorem context_13_102528_305030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102528 ⟨305030, by decide⟩ :=
  accepted_of_selected 13 102528 ⟨305030, by decide⟩ ⟨13, 2, 0, 305030, 102528, 1017, 16384⟩
    (by decide) selected_cut_11373

theorem selected_cut_11374 : selected 8 ⟨305094, by decide⟩
    (prefixPartial 13 102529) = some ⟨13, 2, 0, 305094, 102529, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_102529_305094 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102529 ⟨305094, by decide⟩ :=
  accepted_of_selected 13 102529 ⟨305094, by decide⟩ ⟨13, 2, 0, 305094, 102529, 2153, 16384⟩
    (by decide) selected_cut_11374

theorem selected_cut_11375 : selected 8 ⟨305131, by decide⟩
    (prefixPartial 13 102530) = some ⟨13, 2, 0, 305131, 102530, 957, 16384⟩ := by
  decide +kernel

theorem context_13_102530_305131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102530 ⟨305131, by decide⟩ :=
  accepted_of_selected 13 102530 ⟨305131, by decide⟩ ⟨13, 2, 0, 305131, 102530, 957, 16384⟩
    (by decide) selected_cut_11375

theorem selected_cut_11376 : selected 8 ⟨305149, by decide⟩
    (prefixPartial 13 102531) = some ⟨13, 2, 0, 305149, 102531, 277, 16384⟩ := by
  decide +kernel

theorem context_13_102531_305149 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102531 ⟨305149, by decide⟩ :=
  accepted_of_selected 13 102531 ⟨305149, by decide⟩ ⟨13, 2, 0, 305149, 102531, 277, 16384⟩
    (by decide) selected_cut_11376

theorem unmarked_context_12_25632_305150 : frontier 9 ⟨305150, by decide⟩
    (prefixCache 12 25632) (prefixPartial 12 25632) = false := by
  decide +kernel

theorem node_context_12_25632_305150 : EJMOriginalGlobalDAGData.nodes 9 ⟨305150, by decide⟩ =
    .split (coordinate 12) (![⟨305030, by decide⟩,⟨305094, by decide⟩,⟨305131, by decide⟩,⟨305149, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25632_305150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25632 ⟨305150, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25632
    ⟨305150, by decide⟩ (by decide) (![⟨305030, by decide⟩,⟨305094, by decide⟩,⟨305131, by decide⟩,⟨305149, by decide⟩]) unmarked_context_12_25632_305150 node_context_12_25632_305150
  intro a
  fin_cases a
  · exact context_13_102528_305030
  · exact context_13_102529_305094
  · exact context_13_102530_305131
  · exact context_13_102531_305149

theorem selected_cut_11377 : selected 8 ⟨305163, by decide⟩
    (prefixPartial 13 102532) = some ⟨13, 2, 0, 305163, 102532, 961, 16384⟩ := by
  decide +kernel

theorem context_13_102532_305163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102532 ⟨305163, by decide⟩ :=
  accepted_of_selected 13 102532 ⟨305163, by decide⟩ ⟨13, 2, 0, 305163, 102532, 961, 16384⟩
    (by decide) selected_cut_11377

theorem selected_cut_11378 : selected 8 ⟨305189, by decide⟩
    (prefixPartial 13 102533) = some ⟨13, 2, 0, 305189, 102533, 1621, 16384⟩ := by
  decide +kernel

theorem context_13_102533_305189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102533 ⟨305189, by decide⟩ :=
  accepted_of_selected 13 102533 ⟨305189, by decide⟩ ⟨13, 2, 0, 305189, 102533, 1621, 16384⟩
    (by decide) selected_cut_11378

theorem selected_cut_11379 : selected 8 ⟨305204, by decide⟩
    (prefixPartial 13 102534) = some ⟨13, 2, 0, 305204, 102534, 949, 16384⟩ := by
  decide +kernel

theorem context_13_102534_305204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102534 ⟨305204, by decide⟩ :=
  accepted_of_selected 13 102534 ⟨305204, by decide⟩ ⟨13, 2, 0, 305204, 102534, 949, 16384⟩
    (by decide) selected_cut_11379

theorem selected_cut_11380 : selected 8 ⟨305212, by decide⟩
    (prefixPartial 13 102535) = some ⟨13, 2, 0, 305212, 102535, 773, 16384⟩ := by
  decide +kernel

theorem context_13_102535_305212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102535 ⟨305212, by decide⟩ :=
  accepted_of_selected 13 102535 ⟨305212, by decide⟩ ⟨13, 2, 0, 305212, 102535, 773, 16384⟩
    (by decide) selected_cut_11380

theorem unmarked_context_12_25633_305213 : frontier 9 ⟨305213, by decide⟩
    (prefixCache 12 25633) (prefixPartial 12 25633) = false := by
  decide +kernel

theorem node_context_12_25633_305213 : EJMOriginalGlobalDAGData.nodes 9 ⟨305213, by decide⟩ =
    .split (coordinate 12) (![⟨305163, by decide⟩,⟨305189, by decide⟩,⟨305204, by decide⟩,⟨305212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25633_305213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25633 ⟨305213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25633
    ⟨305213, by decide⟩ (by decide) (![⟨305163, by decide⟩,⟨305189, by decide⟩,⟨305204, by decide⟩,⟨305212, by decide⟩]) unmarked_context_12_25633_305213 node_context_12_25633_305213
  intro a
  fin_cases a
  · exact context_13_102532_305163
  · exact context_13_102533_305189
  · exact context_13_102534_305204
  · exact context_13_102535_305212

theorem selected_cut_11381 : selected 8 ⟨305225, by decide⟩
    (prefixPartial 13 102536) = some ⟨13, 2, 0, 305225, 102536, 853, 16384⟩ := by
  decide +kernel

theorem context_13_102536_305225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102536 ⟨305225, by decide⟩ :=
  accepted_of_selected 13 102536 ⟨305225, by decide⟩ ⟨13, 2, 0, 305225, 102536, 853, 16384⟩
    (by decide) selected_cut_11381

theorem selected_cut_11382 : selected 8 ⟨305251, by decide⟩
    (prefixPartial 13 102537) = some ⟨13, 2, 0, 305251, 102537, 1861, 16384⟩ := by
  decide +kernel

theorem context_13_102537_305251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102537 ⟨305251, by decide⟩ :=
  accepted_of_selected 13 102537 ⟨305251, by decide⟩ ⟨13, 2, 0, 305251, 102537, 1861, 16384⟩
    (by decide) selected_cut_11382

theorem selected_cut_11383 : selected 8 ⟨305265, by decide⟩
    (prefixPartial 13 102538) = some ⟨13, 2, 0, 305265, 102538, 909, 16384⟩ := by
  decide +kernel

theorem context_13_102538_305265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102538 ⟨305265, by decide⟩ :=
  accepted_of_selected 13 102538 ⟨305265, by decide⟩ ⟨13, 2, 0, 305265, 102538, 909, 16384⟩
    (by decide) selected_cut_11383

theorem selected_cut_11384 : selected 8 ⟨305272, by decide⟩
    (prefixPartial 13 102539) = some ⟨13, 2, 0, 305272, 102539, 841, 16384⟩ := by
  decide +kernel

theorem context_13_102539_305272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102539 ⟨305272, by decide⟩ :=
  accepted_of_selected 13 102539 ⟨305272, by decide⟩ ⟨13, 2, 0, 305272, 102539, 841, 16384⟩
    (by decide) selected_cut_11384

theorem unmarked_context_12_25634_305273 : frontier 9 ⟨305273, by decide⟩
    (prefixCache 12 25634) (prefixPartial 12 25634) = false := by
  decide +kernel

theorem node_context_12_25634_305273 : EJMOriginalGlobalDAGData.nodes 9 ⟨305273, by decide⟩ =
    .split (coordinate 12) (![⟨305225, by decide⟩,⟨305251, by decide⟩,⟨305265, by decide⟩,⟨305272, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25634_305273 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25634 ⟨305273, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25634
    ⟨305273, by decide⟩ (by decide) (![⟨305225, by decide⟩,⟨305251, by decide⟩,⟨305265, by decide⟩,⟨305272, by decide⟩]) unmarked_context_12_25634_305273 node_context_12_25634_305273
  intro a
  fin_cases a
  · exact context_13_102536_305225
  · exact context_13_102537_305251
  · exact context_13_102538_305265
  · exact context_13_102539_305272

theorem selected_cut_11385 : selected 8 ⟨305284, by decide⟩
    (prefixPartial 13 102540) = some ⟨13, 2, 0, 305284, 102540, 917, 16384⟩ := by
  decide +kernel

theorem context_13_102540_305284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102540 ⟨305284, by decide⟩ :=
  accepted_of_selected 13 102540 ⟨305284, by decide⟩ ⟨13, 2, 0, 305284, 102540, 917, 16384⟩
    (by decide) selected_cut_11385

theorem selected_cut_11386 : selected 8 ⟨305314, by decide⟩
    (prefixPartial 13 102541) = some ⟨13, 2, 0, 305314, 102541, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_102541_305314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102541 ⟨305314, by decide⟩ :=
  accepted_of_selected 13 102541 ⟨305314, by decide⟩ ⟨13, 2, 0, 305314, 102541, 1957, 16384⟩
    (by decide) selected_cut_11386

theorem selected_cut_11387 : selected 8 ⟨305327, by decide⟩
    (prefixPartial 13 102542) = some ⟨13, 2, 0, 305327, 102542, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_102542_305327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102542 ⟨305327, by decide⟩ :=
  accepted_of_selected 13 102542 ⟨305327, by decide⟩ ⟨13, 2, 0, 305327, 102542, 1033, 16384⟩
    (by decide) selected_cut_11387

theorem selected_cut_11388 : selected 8 ⟨305330, by decide⟩
    (prefixPartial 13 102543) = some ⟨13, 2, 0, 305330, 102543, 721, 16384⟩ := by
  decide +kernel

theorem context_13_102543_305330 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102543 ⟨305330, by decide⟩ :=
  accepted_of_selected 13 102543 ⟨305330, by decide⟩ ⟨13, 2, 0, 305330, 102543, 721, 16384⟩
    (by decide) selected_cut_11388

theorem unmarked_context_12_25635_305331 : frontier 9 ⟨305331, by decide⟩
    (prefixCache 12 25635) (prefixPartial 12 25635) = false := by
  decide +kernel

theorem node_context_12_25635_305331 : EJMOriginalGlobalDAGData.nodes 9 ⟨305331, by decide⟩ =
    .split (coordinate 12) (![⟨305284, by decide⟩,⟨305314, by decide⟩,⟨305327, by decide⟩,⟨305330, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25635_305331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25635 ⟨305331, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25635
    ⟨305331, by decide⟩ (by decide) (![⟨305284, by decide⟩,⟨305314, by decide⟩,⟨305327, by decide⟩,⟨305330, by decide⟩]) unmarked_context_12_25635_305331 node_context_12_25635_305331
  intro a
  fin_cases a
  · exact context_13_102540_305284
  · exact context_13_102541_305314
  · exact context_13_102542_305327
  · exact context_13_102543_305330

theorem unmarked_context_11_6408_305332 : frontier 10 ⟨305332, by decide⟩
    (prefixCache 11 6408) (prefixPartial 11 6408) = false := by
  decide +kernel

theorem node_context_11_6408_305332 : EJMOriginalGlobalDAGData.nodes 10 ⟨305332, by decide⟩ =
    .split (coordinate 11) (![⟨305150, by decide⟩,⟨305213, by decide⟩,⟨305273, by decide⟩,⟨305331, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6408_305332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6408 ⟨305332, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6408
    ⟨305332, by decide⟩ (by decide) (![⟨305150, by decide⟩,⟨305213, by decide⟩,⟨305273, by decide⟩,⟨305331, by decide⟩]) unmarked_context_11_6408_305332 node_context_11_6408_305332
  intro a
  fin_cases a
  · exact context_12_25632_305150
  · exact context_12_25633_305213
  · exact context_12_25634_305273
  · exact context_12_25635_305331

theorem selected_cut_11389 : selected 9 ⟨305383, by decide⟩
    (prefixPartial 12 25636) = some ⟨12, 2, 0, 305383, 25636, 4085, 65536⟩ := by
  decide +kernel

theorem context_12_25636_305383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25636 ⟨305383, by decide⟩ :=
  accepted_of_selected 12 25636 ⟨305383, by decide⟩ ⟨12, 2, 0, 305383, 25636, 4085, 65536⟩
    (by decide) selected_cut_11389

theorem selected_cut_11390 : selected 8 ⟨305394, by decide⟩
    (prefixPartial 13 102548) = some ⟨13, 2, 0, 305394, 102548, 757, 16384⟩ := by
  decide +kernel

theorem context_13_102548_305394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102548 ⟨305394, by decide⟩ :=
  accepted_of_selected 13 102548 ⟨305394, by decide⟩ ⟨13, 2, 0, 305394, 102548, 757, 16384⟩
    (by decide) selected_cut_11390

theorem selected_cut_11391 : selected 8 ⟨305424, by decide⟩
    (prefixPartial 13 102549) = some ⟨13, 2, 0, 305424, 102549, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_102549_305424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102549 ⟨305424, by decide⟩ :=
  accepted_of_selected 13 102549 ⟨305424, by decide⟩ ⟨13, 2, 0, 305424, 102549, 1785, 16384⟩
    (by decide) selected_cut_11391

theorem selected_cut_11392 : selected 8 ⟨305437, by decide⟩
    (prefixPartial 13 102550) = some ⟨13, 2, 0, 305437, 102550, 1141, 16384⟩ := by
  decide +kernel

theorem context_13_102550_305437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102550 ⟨305437, by decide⟩ :=
  accepted_of_selected 13 102550 ⟨305437, by decide⟩ ⟨13, 2, 0, 305437, 102550, 1141, 16384⟩
    (by decide) selected_cut_11392

theorem selected_cut_11393 : selected 8 ⟨305442, by decide⟩
    (prefixPartial 13 102551) = some ⟨13, 2, 0, 305442, 102551, 681, 16384⟩ := by
  decide +kernel

theorem context_13_102551_305442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102551 ⟨305442, by decide⟩ :=
  accepted_of_selected 13 102551 ⟨305442, by decide⟩ ⟨13, 2, 0, 305442, 102551, 681, 16384⟩
    (by decide) selected_cut_11393

theorem unmarked_context_12_25637_305443 : frontier 9 ⟨305443, by decide⟩
    (prefixCache 12 25637) (prefixPartial 12 25637) = false := by
  decide +kernel

theorem node_context_12_25637_305443 : EJMOriginalGlobalDAGData.nodes 9 ⟨305443, by decide⟩ =
    .split (coordinate 12) (![⟨305394, by decide⟩,⟨305424, by decide⟩,⟨305437, by decide⟩,⟨305442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25637_305443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25637 ⟨305443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25637
    ⟨305443, by decide⟩ (by decide) (![⟨305394, by decide⟩,⟨305424, by decide⟩,⟨305437, by decide⟩,⟨305442, by decide⟩]) unmarked_context_12_25637_305443 node_context_12_25637_305443
  intro a
  fin_cases a
  · exact context_13_102548_305394
  · exact context_13_102549_305424
  · exact context_13_102550_305437
  · exact context_13_102551_305442

theorem selected_cut_11394 : selected 8 ⟨305453, by decide⟩
    (prefixPartial 13 102552) = some ⟨13, 2, 0, 305453, 102552, 733, 16384⟩ := by
  decide +kernel

theorem context_13_102552_305453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102552 ⟨305453, by decide⟩ :=
  accepted_of_selected 13 102552 ⟨305453, by decide⟩ ⟨13, 2, 0, 305453, 102552, 733, 16384⟩
    (by decide) selected_cut_11394

theorem selected_cut_11395 : selected 8 ⟨305480, by decide⟩
    (prefixPartial 13 102553) = some ⟨13, 2, 0, 305480, 102553, 2085, 16384⟩ := by
  decide +kernel

theorem context_13_102553_305480 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102553 ⟨305480, by decide⟩ :=
  accepted_of_selected 13 102553 ⟨305480, by decide⟩ ⟨13, 2, 0, 305480, 102553, 2085, 16384⟩
    (by decide) selected_cut_11395

theorem selected_cut_11396 : selected 8 ⟨305495, by decide⟩
    (prefixPartial 13 102554) = some ⟨13, 2, 0, 305495, 102554, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_102554_305495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102554 ⟨305495, by decide⟩ :=
  accepted_of_selected 13 102554 ⟨305495, by decide⟩ ⟨13, 2, 0, 305495, 102554, 1105, 16384⟩
    (by decide) selected_cut_11396

theorem selected_cut_11397 : selected 8 ⟨305507, by decide⟩
    (prefixPartial 13 102555) = some ⟨13, 2, 0, 305507, 102555, 801, 16384⟩ := by
  decide +kernel

theorem context_13_102555_305507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102555 ⟨305507, by decide⟩ :=
  accepted_of_selected 13 102555 ⟨305507, by decide⟩ ⟨13, 2, 0, 305507, 102555, 801, 16384⟩
    (by decide) selected_cut_11397

theorem unmarked_context_12_25638_305508 : frontier 9 ⟨305508, by decide⟩
    (prefixCache 12 25638) (prefixPartial 12 25638) = false := by
  decide +kernel

theorem node_context_12_25638_305508 : EJMOriginalGlobalDAGData.nodes 9 ⟨305508, by decide⟩ =
    .split (coordinate 12) (![⟨305453, by decide⟩,⟨305480, by decide⟩,⟨305495, by decide⟩,⟨305507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25638_305508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25638 ⟨305508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25638
    ⟨305508, by decide⟩ (by decide) (![⟨305453, by decide⟩,⟨305480, by decide⟩,⟨305495, by decide⟩,⟨305507, by decide⟩]) unmarked_context_12_25638_305508 node_context_12_25638_305508
  intro a
  fin_cases a
  · exact context_13_102552_305453
  · exact context_13_102553_305480
  · exact context_13_102554_305495
  · exact context_13_102555_305507

theorem selected_cut_11398 : selected 8 ⟨305519, by decide⟩
    (prefixPartial 13 102556) = some ⟨13, 2, 0, 305519, 102556, 829, 16384⟩ := by
  decide +kernel

theorem context_13_102556_305519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102556 ⟨305519, by decide⟩ :=
  accepted_of_selected 13 102556 ⟨305519, by decide⟩ ⟨13, 2, 0, 305519, 102556, 829, 16384⟩
    (by decide) selected_cut_11398

theorem selected_cut_11399 : selected 8 ⟨305552, by decide⟩
    (prefixPartial 13 102557) = some ⟨13, 2, 0, 305552, 102557, 2381, 16384⟩ := by
  decide +kernel

theorem context_13_102557_305552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102557 ⟨305552, by decide⟩ :=
  accepted_of_selected 13 102557 ⟨305552, by decide⟩ ⟨13, 2, 0, 305552, 102557, 2381, 16384⟩
    (by decide) selected_cut_11399

theorem selected_cut_11400 : selected 8 ⟨305569, by decide⟩
    (prefixPartial 13 102558) = some ⟨13, 2, 0, 305569, 102558, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_102558_305569 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102558 ⟨305569, by decide⟩ :=
  accepted_of_selected 13 102558 ⟨305569, by decide⟩ ⟨13, 2, 0, 305569, 102558, 1229, 16384⟩
    (by decide) selected_cut_11400

theorem selected_cut_11401 : selected 8 ⟨305572, by decide⟩
    (prefixPartial 13 102559) = some ⟨13, 2, 0, 305572, 102559, 725, 16384⟩ := by
  decide +kernel

theorem context_13_102559_305572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102559 ⟨305572, by decide⟩ :=
  accepted_of_selected 13 102559 ⟨305572, by decide⟩ ⟨13, 2, 0, 305572, 102559, 725, 16384⟩
    (by decide) selected_cut_11401

theorem unmarked_context_12_25639_305573 : frontier 9 ⟨305573, by decide⟩
    (prefixCache 12 25639) (prefixPartial 12 25639) = false := by
  decide +kernel

theorem node_context_12_25639_305573 : EJMOriginalGlobalDAGData.nodes 9 ⟨305573, by decide⟩ =
    .split (coordinate 12) (![⟨305519, by decide⟩,⟨305552, by decide⟩,⟨305569, by decide⟩,⟨305572, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25639_305573 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25639 ⟨305573, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25639
    ⟨305573, by decide⟩ (by decide) (![⟨305519, by decide⟩,⟨305552, by decide⟩,⟨305569, by decide⟩,⟨305572, by decide⟩]) unmarked_context_12_25639_305573 node_context_12_25639_305573
  intro a
  fin_cases a
  · exact context_13_102556_305519
  · exact context_13_102557_305552
  · exact context_13_102558_305569
  · exact context_13_102559_305572

theorem unmarked_context_11_6409_305574 : frontier 10 ⟨305574, by decide⟩
    (prefixCache 11 6409) (prefixPartial 11 6409) = false := by
  decide +kernel

theorem node_context_11_6409_305574 : EJMOriginalGlobalDAGData.nodes 10 ⟨305574, by decide⟩ =
    .split (coordinate 11) (![⟨305383, by decide⟩,⟨305443, by decide⟩,⟨305508, by decide⟩,⟨305573, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6409_305574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6409 ⟨305574, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6409
    ⟨305574, by decide⟩ (by decide) (![⟨305383, by decide⟩,⟨305443, by decide⟩,⟨305508, by decide⟩,⟨305573, by decide⟩]) unmarked_context_11_6409_305574 node_context_11_6409_305574
  intro a
  fin_cases a
  · exact context_12_25636_305383
  · exact context_12_25637_305443
  · exact context_12_25638_305508
  · exact context_12_25639_305573

theorem selected_cut_11402 : selected 8 ⟨305584, by decide⟩
    (prefixPartial 13 102560) = some ⟨13, 2, 0, 305584, 102560, 505, 16384⟩ := by
  decide +kernel

theorem context_13_102560_305584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102560 ⟨305584, by decide⟩ :=
  accepted_of_selected 13 102560 ⟨305584, by decide⟩ ⟨13, 2, 0, 305584, 102560, 505, 16384⟩
    (by decide) selected_cut_11402

theorem selected_cut_11403 : selected 8 ⟨305612, by decide⟩
    (prefixPartial 13 102561) = some ⟨13, 2, 0, 305612, 102561, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_102561_305612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102561 ⟨305612, by decide⟩ :=
  accepted_of_selected 13 102561 ⟨305612, by decide⟩ ⟨13, 2, 0, 305612, 102561, 1889, 16384⟩
    (by decide) selected_cut_11403

theorem selected_cut_11404 : selected 8 ⟨305632, by decide⟩
    (prefixPartial 13 102562) = some ⟨13, 2, 0, 305632, 102562, 1273, 16384⟩ := by
  decide +kernel

theorem context_13_102562_305632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102562 ⟨305632, by decide⟩ :=
  accepted_of_selected 13 102562 ⟨305632, by decide⟩ ⟨13, 2, 0, 305632, 102562, 1273, 16384⟩
    (by decide) selected_cut_11404

theorem selected_cut_11405 : selected 8 ⟨305644, by decide⟩
    (prefixPartial 13 102563) = some ⟨13, 2, 0, 305644, 102563, 821, 16384⟩ := by
  decide +kernel

theorem context_13_102563_305644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102563 ⟨305644, by decide⟩ :=
  accepted_of_selected 13 102563 ⟨305644, by decide⟩ ⟨13, 2, 0, 305644, 102563, 821, 16384⟩
    (by decide) selected_cut_11405

theorem unmarked_context_12_25640_305645 : frontier 9 ⟨305645, by decide⟩
    (prefixCache 12 25640) (prefixPartial 12 25640) = false := by
  decide +kernel

theorem node_context_12_25640_305645 : EJMOriginalGlobalDAGData.nodes 9 ⟨305645, by decide⟩ =
    .split (coordinate 12) (![⟨305584, by decide⟩,⟨305612, by decide⟩,⟨305632, by decide⟩,⟨305644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25640_305645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25640 ⟨305645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25640
    ⟨305645, by decide⟩ (by decide) (![⟨305584, by decide⟩,⟨305612, by decide⟩,⟨305632, by decide⟩,⟨305644, by decide⟩]) unmarked_context_12_25640_305645 node_context_12_25640_305645
  intro a
  fin_cases a
  · exact context_13_102560_305584
  · exact context_13_102561_305612
  · exact context_13_102562_305632
  · exact context_13_102563_305644

theorem selected_cut_11406 : selected 8 ⟨305653, by decide⟩
    (prefixPartial 13 102564) = some ⟨13, 2, 0, 305653, 102564, 729, 16384⟩ := by
  decide +kernel

theorem context_13_102564_305653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102564 ⟨305653, by decide⟩ :=
  accepted_of_selected 13 102564 ⟨305653, by decide⟩ ⟨13, 2, 0, 305653, 102564, 729, 16384⟩
    (by decide) selected_cut_11406

theorem selected_cut_11407 : selected 8 ⟨305683, by decide⟩
    (prefixPartial 13 102565) = some ⟨13, 2, 0, 305683, 102565, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_102565_305683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102565 ⟨305683, by decide⟩ :=
  accepted_of_selected 13 102565 ⟨305683, by decide⟩ ⟨13, 2, 0, 305683, 102565, 2121, 16384⟩
    (by decide) selected_cut_11407

theorem selected_cut_11408 : selected 8 ⟨305702, by decide⟩
    (prefixPartial 13 102566) = some ⟨13, 2, 0, 305702, 102566, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_102566_305702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102566 ⟨305702, by decide⟩ :=
  accepted_of_selected 13 102566 ⟨305702, by decide⟩ ⟨13, 2, 0, 305702, 102566, 1245, 16384⟩
    (by decide) selected_cut_11408

theorem selected_cut_11409 : selected 8 ⟨305711, by decide⟩
    (prefixPartial 13 102567) = some ⟨13, 2, 0, 305711, 102567, 829, 16384⟩ := by
  decide +kernel

theorem context_13_102567_305711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102567 ⟨305711, by decide⟩ :=
  accepted_of_selected 13 102567 ⟨305711, by decide⟩ ⟨13, 2, 0, 305711, 102567, 829, 16384⟩
    (by decide) selected_cut_11409

theorem unmarked_context_12_25641_305712 : frontier 9 ⟨305712, by decide⟩
    (prefixCache 12 25641) (prefixPartial 12 25641) = false := by
  decide +kernel

theorem node_context_12_25641_305712 : EJMOriginalGlobalDAGData.nodes 9 ⟨305712, by decide⟩ =
    .split (coordinate 12) (![⟨305653, by decide⟩,⟨305683, by decide⟩,⟨305702, by decide⟩,⟨305711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25641_305712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25641 ⟨305712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25641
    ⟨305712, by decide⟩ (by decide) (![⟨305653, by decide⟩,⟨305683, by decide⟩,⟨305702, by decide⟩,⟨305711, by decide⟩]) unmarked_context_12_25641_305712 node_context_12_25641_305712
  intro a
  fin_cases a
  · exact context_13_102564_305653
  · exact context_13_102565_305683
  · exact context_13_102566_305702
  · exact context_13_102567_305711

theorem selected_cut_11410 : selected 8 ⟨305722, by decide⟩
    (prefixPartial 13 102568) = some ⟨13, 2, 0, 305722, 102568, 609, 16384⟩ := by
  decide +kernel

theorem context_13_102568_305722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102568 ⟨305722, by decide⟩ :=
  accepted_of_selected 13 102568 ⟨305722, by decide⟩ ⟨13, 2, 0, 305722, 102568, 609, 16384⟩
    (by decide) selected_cut_11410

theorem selected_cut_11411 : selected 8 ⟨305747, by decide⟩
    (prefixPartial 13 102569) = some ⟨13, 2, 0, 305747, 102569, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_102569_305747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102569 ⟨305747, by decide⟩ :=
  accepted_of_selected 13 102569 ⟨305747, by decide⟩ ⟨13, 2, 0, 305747, 102569, 2117, 16384⟩
    (by decide) selected_cut_11411

theorem selected_cut_11412 : selected 8 ⟨305759, by decide⟩
    (prefixPartial 13 102570) = some ⟨13, 2, 0, 305759, 102570, 1065, 16384⟩ := by
  decide +kernel

theorem context_13_102570_305759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102570 ⟨305759, by decide⟩ :=
  accepted_of_selected 13 102570 ⟨305759, by decide⟩ ⟨13, 2, 0, 305759, 102570, 1065, 16384⟩
    (by decide) selected_cut_11412

theorem selected_cut_11413 : selected 8 ⟨305768, by decide⟩
    (prefixPartial 13 102571) = some ⟨13, 2, 0, 305768, 102571, 901, 16384⟩ := by
  decide +kernel

theorem context_13_102571_305768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102571 ⟨305768, by decide⟩ :=
  accepted_of_selected 13 102571 ⟨305768, by decide⟩ ⟨13, 2, 0, 305768, 102571, 901, 16384⟩
    (by decide) selected_cut_11413

theorem unmarked_context_12_25642_305769 : frontier 9 ⟨305769, by decide⟩
    (prefixCache 12 25642) (prefixPartial 12 25642) = false := by
  decide +kernel

theorem node_context_12_25642_305769 : EJMOriginalGlobalDAGData.nodes 9 ⟨305769, by decide⟩ =
    .split (coordinate 12) (![⟨305722, by decide⟩,⟨305747, by decide⟩,⟨305759, by decide⟩,⟨305768, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25642_305769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25642 ⟨305769, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25642
    ⟨305769, by decide⟩ (by decide) (![⟨305722, by decide⟩,⟨305747, by decide⟩,⟨305759, by decide⟩,⟨305768, by decide⟩]) unmarked_context_12_25642_305769 node_context_12_25642_305769
  intro a
  fin_cases a
  · exact context_13_102568_305722
  · exact context_13_102569_305747
  · exact context_13_102570_305759
  · exact context_13_102571_305768

theorem selected_cut_11414 : selected 8 ⟨305779, by decide⟩
    (prefixPartial 13 102572) = some ⟨13, 2, 0, 305779, 102572, 657, 16384⟩ := by
  decide +kernel

theorem context_13_102572_305779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102572 ⟨305779, by decide⟩ :=
  accepted_of_selected 13 102572 ⟨305779, by decide⟩ ⟨13, 2, 0, 305779, 102572, 657, 16384⟩
    (by decide) selected_cut_11414

theorem selected_cut_11415 : selected 8 ⟨305818, by decide⟩
    (prefixPartial 13 102573) = some ⟨13, 2, 0, 305818, 102573, 2409, 16384⟩ := by
  decide +kernel

theorem context_13_102573_305818 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102573 ⟨305818, by decide⟩ :=
  accepted_of_selected 13 102573 ⟨305818, by decide⟩ ⟨13, 2, 0, 305818, 102573, 2409, 16384⟩
    (by decide) selected_cut_11415

theorem selected_cut_11416 : selected 8 ⟨305833, by decide⟩
    (prefixPartial 13 102574) = some ⟨13, 2, 0, 305833, 102574, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_102574_305833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102574 ⟨305833, by decide⟩ :=
  accepted_of_selected 13 102574 ⟨305833, by decide⟩ ⟨13, 2, 0, 305833, 102574, 1217, 16384⟩
    (by decide) selected_cut_11416

theorem selected_cut_11417 : selected 8 ⟨305841, by decide⟩
    (prefixPartial 13 102575) = some ⟨13, 2, 0, 305841, 102575, 841, 16384⟩ := by
  decide +kernel

theorem context_13_102575_305841 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102575 ⟨305841, by decide⟩ :=
  accepted_of_selected 13 102575 ⟨305841, by decide⟩ ⟨13, 2, 0, 305841, 102575, 841, 16384⟩
    (by decide) selected_cut_11417

theorem unmarked_context_12_25643_305842 : frontier 9 ⟨305842, by decide⟩
    (prefixCache 12 25643) (prefixPartial 12 25643) = false := by
  decide +kernel

theorem node_context_12_25643_305842 : EJMOriginalGlobalDAGData.nodes 9 ⟨305842, by decide⟩ =
    .split (coordinate 12) (![⟨305779, by decide⟩,⟨305818, by decide⟩,⟨305833, by decide⟩,⟨305841, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25643_305842 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25643 ⟨305842, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25643
    ⟨305842, by decide⟩ (by decide) (![⟨305779, by decide⟩,⟨305818, by decide⟩,⟨305833, by decide⟩,⟨305841, by decide⟩]) unmarked_context_12_25643_305842 node_context_12_25643_305842
  intro a
  fin_cases a
  · exact context_13_102572_305779
  · exact context_13_102573_305818
  · exact context_13_102574_305833
  · exact context_13_102575_305841

theorem unmarked_context_11_6410_305843 : frontier 10 ⟨305843, by decide⟩
    (prefixCache 11 6410) (prefixPartial 11 6410) = false := by
  decide +kernel

theorem node_context_11_6410_305843 : EJMOriginalGlobalDAGData.nodes 10 ⟨305843, by decide⟩ =
    .split (coordinate 11) (![⟨305645, by decide⟩,⟨305712, by decide⟩,⟨305769, by decide⟩,⟨305842, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_6410_305843 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 6410 ⟨305843, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 6410
    ⟨305843, by decide⟩ (by decide) (![⟨305645, by decide⟩,⟨305712, by decide⟩,⟨305769, by decide⟩,⟨305842, by decide⟩]) unmarked_context_11_6410_305843 node_context_11_6410_305843
  intro a
  fin_cases a
  · exact context_12_25640_305645
  · exact context_12_25641_305712
  · exact context_12_25642_305769
  · exact context_12_25643_305842

theorem selected_cut_11418 : selected 9 ⟨305896, by decide⟩
    (prefixPartial 12 25644) = some ⟨12, 2, 0, 305896, 25644, 3893, 65536⟩ := by
  decide +kernel

theorem context_12_25644_305896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25644 ⟨305896, by decide⟩ :=
  accepted_of_selected 12 25644 ⟨305896, by decide⟩ ⟨12, 2, 0, 305896, 25644, 3893, 65536⟩
    (by decide) selected_cut_11418

theorem selected_cut_11419 : selected 8 ⟨305905, by decide⟩
    (prefixPartial 13 102580) = some ⟨13, 2, 0, 305905, 102580, 689, 16384⟩ := by
  decide +kernel

theorem context_13_102580_305905 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102580 ⟨305905, by decide⟩ :=
  accepted_of_selected 13 102580 ⟨305905, by decide⟩ ⟨13, 2, 0, 305905, 102580, 689, 16384⟩
    (by decide) selected_cut_11419

theorem selected_cut_11420 : selected 8 ⟨305937, by decide⟩
    (prefixPartial 13 102581) = some ⟨13, 2, 0, 305937, 102581, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_102581_305937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102581 ⟨305937, by decide⟩ :=
  accepted_of_selected 13 102581 ⟨305937, by decide⟩ ⟨13, 2, 0, 305937, 102581, 2037, 16384⟩
    (by decide) selected_cut_11420

theorem selected_cut_11421 : selected 8 ⟨305953, by decide⟩
    (prefixPartial 13 102582) = some ⟨13, 2, 0, 305953, 102582, 1125, 16384⟩ := by
  decide +kernel

theorem context_13_102582_305953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102582 ⟨305953, by decide⟩ :=
  accepted_of_selected 13 102582 ⟨305953, by decide⟩ ⟨13, 2, 0, 305953, 102582, 1125, 16384⟩
    (by decide) selected_cut_11421

theorem selected_cut_11422 : selected 8 ⟨305960, by decide⟩
    (prefixPartial 13 102583) = some ⟨13, 2, 0, 305960, 102583, 729, 16384⟩ := by
  decide +kernel

theorem context_13_102583_305960 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102583 ⟨305960, by decide⟩ :=
  accepted_of_selected 13 102583 ⟨305960, by decide⟩ ⟨13, 2, 0, 305960, 102583, 729, 16384⟩
    (by decide) selected_cut_11422

theorem unmarked_context_12_25645_305961 : frontier 9 ⟨305961, by decide⟩
    (prefixCache 12 25645) (prefixPartial 12 25645) = false := by
  decide +kernel

theorem node_context_12_25645_305961 : EJMOriginalGlobalDAGData.nodes 9 ⟨305961, by decide⟩ =
    .split (coordinate 12) (![⟨305905, by decide⟩,⟨305937, by decide⟩,⟨305953, by decide⟩,⟨305960, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25645_305961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25645 ⟨305961, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25645
    ⟨305961, by decide⟩ (by decide) (![⟨305905, by decide⟩,⟨305937, by decide⟩,⟨305953, by decide⟩,⟨305960, by decide⟩]) unmarked_context_12_25645_305961 node_context_12_25645_305961
  intro a
  fin_cases a
  · exact context_13_102580_305905
  · exact context_13_102581_305937
  · exact context_13_102582_305953
  · exact context_13_102583_305960

theorem selected_cut_11423 : selected 8 ⟨305969, by decide⟩
    (prefixPartial 13 102584) = some ⟨13, 2, 0, 305969, 102584, 557, 16384⟩ := by
  decide +kernel

theorem context_13_102584_305969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102584 ⟨305969, by decide⟩ :=
  accepted_of_selected 13 102584 ⟨305969, by decide⟩ ⟨13, 2, 0, 305969, 102584, 557, 16384⟩
    (by decide) selected_cut_11423

theorem selected_cut_11424 : selected 8 ⟨305996, by decide⟩
    (prefixPartial 13 102585) = some ⟨13, 2, 0, 305996, 102585, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_102585_305996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102585 ⟨305996, by decide⟩ :=
  accepted_of_selected 13 102585 ⟨305996, by decide⟩ ⟨13, 2, 0, 305996, 102585, 2173, 16384⟩
    (by decide) selected_cut_11424

theorem selected_cut_11425 : selected 8 ⟨306008, by decide⟩
    (prefixPartial 13 102586) = some ⟨13, 2, 0, 306008, 102586, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_102586_306008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102586 ⟨306008, by decide⟩ :=
  accepted_of_selected 13 102586 ⟨306008, by decide⟩ ⟨13, 2, 0, 306008, 102586, 1097, 16384⟩
    (by decide) selected_cut_11425

theorem selected_cut_11426 : selected 8 ⟨306019, by decide⟩
    (prefixPartial 13 102587) = some ⟨13, 2, 0, 306019, 102587, 805, 16384⟩ := by
  decide +kernel

theorem context_13_102587_306019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 102587 ⟨306019, by decide⟩ :=
  accepted_of_selected 13 102587 ⟨306019, by decide⟩ ⟨13, 2, 0, 306019, 102587, 805, 16384⟩
    (by decide) selected_cut_11426

theorem unmarked_context_12_25646_306020 : frontier 9 ⟨306020, by decide⟩
    (prefixCache 12 25646) (prefixPartial 12 25646) = false := by
  decide +kernel

theorem node_context_12_25646_306020 : EJMOriginalGlobalDAGData.nodes 9 ⟨306020, by decide⟩ =
    .split (coordinate 12) (![⟨305969, by decide⟩,⟨305996, by decide⟩,⟨306008, by decide⟩,⟨306019, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_25646_306020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 25646 ⟨306020, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 25646
    ⟨306020, by decide⟩ (by decide) (![⟨305969, by decide⟩,⟨305996, by decide⟩,⟨306008, by decide⟩,⟨306019, by decide⟩]) unmarked_context_12_25646_306020 node_context_12_25646_306020
  intro a
  fin_cases a
  · exact context_13_102584_305969
  · exact context_13_102585_305996
  · exact context_13_102586_306008
  · exact context_13_102587_306019

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
