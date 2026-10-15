/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover326
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_31395 : selected 8 ⟨805916, by decide⟩
    (prefixPartial 13 424002) = some ⟨13, 2, 0, 805916, 424002, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_424002_805916 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424002 ⟨805916, by decide⟩ :=
  accepted_of_selected 13 424002 ⟨805916, by decide⟩ ⟨13, 2, 0, 805916, 424002, 1553, 16384⟩
    (by decide) selected_cut_31395

theorem selected_cut_31396 : selected 8 ⟨805925, by decide⟩
    (prefixPartial 13 424003) = some ⟨13, 2, 0, 805925, 424003, 949, 16384⟩ := by
  decide +kernel

theorem context_13_424003_805925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424003 ⟨805925, by decide⟩ :=
  accepted_of_selected 13 424003 ⟨805925, by decide⟩ ⟨13, 2, 0, 805925, 424003, 949, 16384⟩
    (by decide) selected_cut_31396

theorem unmarked_context_12_106000_805926 : frontier 9 ⟨805926, by decide⟩
    (prefixCache 12 106000) (prefixPartial 12 106000) = false := by
  decide +kernel

theorem node_context_12_106000_805926 : EJMOriginalGlobalDAGData.nodes 9 ⟨805926, by decide⟩ =
    .split (coordinate 12) (![⟨805863, by decide⟩,⟨805892, by decide⟩,⟨805916, by decide⟩,⟨805925, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106000_805926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106000 ⟨805926, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106000
    ⟨805926, by decide⟩ (by decide) (![⟨805863, by decide⟩,⟨805892, by decide⟩,⟨805916, by decide⟩,⟨805925, by decide⟩]) unmarked_context_12_106000_805926 node_context_12_106000_805926
  intro a
  fin_cases a
  · exact context_13_424000_805863
  · exact context_13_424001_805892
  · exact context_13_424002_805916
  · exact context_13_424003_805925

theorem selected_cut_31397 : selected 8 ⟨805978, by decide⟩
    (prefixPartial 13 424004) = some ⟨13, 2, 0, 805978, 424004, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_424004_805978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424004 ⟨805978, by decide⟩ :=
  accepted_of_selected 13 424004 ⟨805978, by decide⟩ ⟨13, 2, 0, 805978, 424004, 2645, 16384⟩
    (by decide) selected_cut_31397

theorem selected_cut_31398 : selected 8 ⟨806033, by decide⟩
    (prefixPartial 13 424005) = some ⟨13, 2, 0, 806033, 424005, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_424005_806033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424005 ⟨806033, by decide⟩ :=
  accepted_of_selected 13 424005 ⟨806033, by decide⟩ ⟨13, 2, 0, 806033, 424005, 2673, 16384⟩
    (by decide) selected_cut_31398

theorem selected_cut_31399 : selected 8 ⟨806066, by decide⟩
    (prefixPartial 13 424006) = some ⟨13, 2, 0, 806066, 424006, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_424006_806066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424006 ⟨806066, by decide⟩ :=
  accepted_of_selected 13 424006 ⟨806066, by decide⟩ ⟨13, 2, 0, 806066, 424006, 1689, 16384⟩
    (by decide) selected_cut_31399

theorem selected_cut_31400 : selected 8 ⟨806077, by decide⟩
    (prefixPartial 13 424007) = some ⟨13, 2, 0, 806077, 424007, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_424007_806077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424007 ⟨806077, by decide⟩ :=
  accepted_of_selected 13 424007 ⟨806077, by decide⟩ ⟨13, 2, 0, 806077, 424007, 1069, 16384⟩
    (by decide) selected_cut_31400

theorem unmarked_context_12_106001_806078 : frontier 9 ⟨806078, by decide⟩
    (prefixCache 12 106001) (prefixPartial 12 106001) = false := by
  decide +kernel

theorem node_context_12_106001_806078 : EJMOriginalGlobalDAGData.nodes 9 ⟨806078, by decide⟩ =
    .split (coordinate 12) (![⟨805978, by decide⟩,⟨806033, by decide⟩,⟨806066, by decide⟩,⟨806077, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106001_806078 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106001 ⟨806078, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106001
    ⟨806078, by decide⟩ (by decide) (![⟨805978, by decide⟩,⟨806033, by decide⟩,⟨806066, by decide⟩,⟨806077, by decide⟩]) unmarked_context_12_106001_806078 node_context_12_106001_806078
  intro a
  fin_cases a
  · exact context_13_424004_805978
  · exact context_13_424005_806033
  · exact context_13_424006_806066
  · exact context_13_424007_806077

theorem selected_cut_31401 : selected 8 ⟨806122, by decide⟩
    (prefixPartial 13 424008) = some ⟨13, 2, 0, 806122, 424008, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_424008_806122 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424008 ⟨806122, by decide⟩ :=
  accepted_of_selected 13 424008 ⟨806122, by decide⟩ ⟨13, 2, 0, 806122, 424008, 2073, 16384⟩
    (by decide) selected_cut_31401

theorem selected_cut_31402 : selected 8 ⟨806150, by decide⟩
    (prefixPartial 13 424009) = some ⟨13, 2, 0, 806150, 424009, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_424009_806150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424009 ⟨806150, by decide⟩ :=
  accepted_of_selected 13 424009 ⟨806150, by decide⟩ ⟨13, 2, 0, 806150, 424009, 2645, 16384⟩
    (by decide) selected_cut_31402

theorem selected_cut_31403 : selected 8 ⟨806171, by decide⟩
    (prefixPartial 13 424010) = some ⟨13, 2, 0, 806171, 424010, 1285, 16384⟩ := by
  decide +kernel

theorem context_13_424010_806171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424010 ⟨806171, by decide⟩ :=
  accepted_of_selected 13 424010 ⟨806171, by decide⟩ ⟨13, 2, 0, 806171, 424010, 1285, 16384⟩
    (by decide) selected_cut_31403

theorem selected_cut_31404 : selected 8 ⟨806178, by decide⟩
    (prefixPartial 13 424011) = some ⟨13, 2, 0, 806178, 424011, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_424011_806178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424011 ⟨806178, by decide⟩ :=
  accepted_of_selected 13 424011 ⟨806178, by decide⟩ ⟨13, 2, 0, 806178, 424011, 1081, 16384⟩
    (by decide) selected_cut_31404

theorem unmarked_context_12_106002_806179 : frontier 9 ⟨806179, by decide⟩
    (prefixCache 12 106002) (prefixPartial 12 106002) = false := by
  decide +kernel

theorem node_context_12_106002_806179 : EJMOriginalGlobalDAGData.nodes 9 ⟨806179, by decide⟩ =
    .split (coordinate 12) (![⟨806122, by decide⟩,⟨806150, by decide⟩,⟨806171, by decide⟩,⟨806178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106002_806179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106002 ⟨806179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106002
    ⟨806179, by decide⟩ (by decide) (![⟨806122, by decide⟩,⟨806150, by decide⟩,⟨806171, by decide⟩,⟨806178, by decide⟩]) unmarked_context_12_106002_806179 node_context_12_106002_806179
  intro a
  fin_cases a
  · exact context_13_424008_806122
  · exact context_13_424009_806150
  · exact context_13_424010_806171
  · exact context_13_424011_806178

theorem selected_cut_31405 : selected 8 ⟨806228, by decide⟩
    (prefixPartial 13 424012) = some ⟨13, 2, 0, 806228, 424012, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_424012_806228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424012 ⟨806228, by decide⟩ :=
  accepted_of_selected 13 424012 ⟨806228, by decide⟩ ⟨13, 2, 0, 806228, 424012, 2617, 16384⟩
    (by decide) selected_cut_31405

theorem selected_cut_31406 : selected 8 ⟨806282, by decide⟩
    (prefixPartial 13 424013) = some ⟨13, 2, 0, 806282, 424013, 3001, 16384⟩ := by
  decide +kernel

theorem context_13_424013_806282 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424013 ⟨806282, by decide⟩ :=
  accepted_of_selected 13 424013 ⟨806282, by decide⟩ ⟨13, 2, 0, 806282, 424013, 3001, 16384⟩
    (by decide) selected_cut_31406

theorem selected_cut_31407 : selected 8 ⟨806312, by decide⟩
    (prefixPartial 13 424014) = some ⟨13, 2, 0, 806312, 424014, 1841, 16384⟩ := by
  decide +kernel

theorem context_13_424014_806312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424014 ⟨806312, by decide⟩ :=
  accepted_of_selected 13 424014 ⟨806312, by decide⟩ ⟨13, 2, 0, 806312, 424014, 1841, 16384⟩
    (by decide) selected_cut_31407

theorem selected_cut_31408 : selected 8 ⟨806332, by decide⟩
    (prefixPartial 13 424015) = some ⟨13, 2, 0, 806332, 424015, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_424015_806332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424015 ⟨806332, by decide⟩ :=
  accepted_of_selected 13 424015 ⟨806332, by decide⟩ ⟨13, 2, 0, 806332, 424015, 1097, 16384⟩
    (by decide) selected_cut_31408

theorem unmarked_context_12_106003_806333 : frontier 9 ⟨806333, by decide⟩
    (prefixCache 12 106003) (prefixPartial 12 106003) = false := by
  decide +kernel

theorem node_context_12_106003_806333 : EJMOriginalGlobalDAGData.nodes 9 ⟨806333, by decide⟩ =
    .split (coordinate 12) (![⟨806228, by decide⟩,⟨806282, by decide⟩,⟨806312, by decide⟩,⟨806332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106003_806333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106003 ⟨806333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106003
    ⟨806333, by decide⟩ (by decide) (![⟨806228, by decide⟩,⟨806282, by decide⟩,⟨806312, by decide⟩,⟨806332, by decide⟩]) unmarked_context_12_106003_806333 node_context_12_106003_806333
  intro a
  fin_cases a
  · exact context_13_424012_806228
  · exact context_13_424013_806282
  · exact context_13_424014_806312
  · exact context_13_424015_806332

theorem unmarked_context_11_26500_806334 : frontier 10 ⟨806334, by decide⟩
    (prefixCache 11 26500) (prefixPartial 11 26500) = false := by
  decide +kernel

theorem node_context_11_26500_806334 : EJMOriginalGlobalDAGData.nodes 10 ⟨806334, by decide⟩ =
    .split (coordinate 11) (![⟨805926, by decide⟩,⟨806078, by decide⟩,⟨806179, by decide⟩,⟨806333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26500_806334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26500 ⟨806334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26500
    ⟨806334, by decide⟩ (by decide) (![⟨805926, by decide⟩,⟨806078, by decide⟩,⟨806179, by decide⟩,⟨806333, by decide⟩]) unmarked_context_11_26500_806334 node_context_11_26500_806334
  intro a
  fin_cases a
  · exact context_12_106000_805926
  · exact context_12_106001_806078
  · exact context_12_106002_806179
  · exact context_12_106003_806333

theorem selected_cut_31409 : selected 8 ⟨806371, by decide⟩
    (prefixPartial 13 424016) = some ⟨13, 2, 0, 806371, 424016, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_424016_806371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424016 ⟨806371, by decide⟩ :=
  accepted_of_selected 13 424016 ⟨806371, by decide⟩ ⟨13, 2, 0, 806371, 424016, 1929, 16384⟩
    (by decide) selected_cut_31409

theorem selected_cut_31410 : selected 8 ⟨806404, by decide⟩
    (prefixPartial 13 424017) = some ⟨13, 2, 0, 806404, 424017, 2517, 16384⟩ := by
  decide +kernel

theorem context_13_424017_806404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424017 ⟨806404, by decide⟩ :=
  accepted_of_selected 13 424017 ⟨806404, by decide⟩ ⟨13, 2, 0, 806404, 424017, 2517, 16384⟩
    (by decide) selected_cut_31410

theorem selected_cut_31411 : selected 8 ⟨806432, by decide⟩
    (prefixPartial 13 424018) = some ⟨13, 2, 0, 806432, 424018, 1617, 16384⟩ := by
  decide +kernel

theorem context_13_424018_806432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424018 ⟨806432, by decide⟩ :=
  accepted_of_selected 13 424018 ⟨806432, by decide⟩ ⟨13, 2, 0, 806432, 424018, 1617, 16384⟩
    (by decide) selected_cut_31411

theorem selected_cut_31412 : selected 8 ⟨806439, by decide⟩
    (prefixPartial 13 424019) = some ⟨13, 2, 0, 806439, 424019, 949, 16384⟩ := by
  decide +kernel

theorem context_13_424019_806439 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424019 ⟨806439, by decide⟩ :=
  accepted_of_selected 13 424019 ⟨806439, by decide⟩ ⟨13, 2, 0, 806439, 424019, 949, 16384⟩
    (by decide) selected_cut_31412

theorem unmarked_context_12_106004_806440 : frontier 9 ⟨806440, by decide⟩
    (prefixCache 12 106004) (prefixPartial 12 106004) = false := by
  decide +kernel

theorem node_context_12_106004_806440 : EJMOriginalGlobalDAGData.nodes 9 ⟨806440, by decide⟩ =
    .split (coordinate 12) (![⟨806371, by decide⟩,⟨806404, by decide⟩,⟨806432, by decide⟩,⟨806439, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106004_806440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106004 ⟨806440, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106004
    ⟨806440, by decide⟩ (by decide) (![⟨806371, by decide⟩,⟨806404, by decide⟩,⟨806432, by decide⟩,⟨806439, by decide⟩]) unmarked_context_12_106004_806440 node_context_12_106004_806440
  intro a
  fin_cases a
  · exact context_13_424016_806371
  · exact context_13_424017_806404
  · exact context_13_424018_806432
  · exact context_13_424019_806439

theorem selected_cut_31413 : selected 8 ⟨806481, by decide⟩
    (prefixPartial 13 424020) = some ⟨13, 2, 0, 806481, 424020, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_424020_806481 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424020 ⟨806481, by decide⟩ :=
  accepted_of_selected 13 424020 ⟨806481, by decide⟩ ⟨13, 2, 0, 806481, 424020, 2285, 16384⟩
    (by decide) selected_cut_31413

theorem selected_cut_31414 : selected 8 ⟨806517, by decide⟩
    (prefixPartial 13 424021) = some ⟨13, 2, 0, 806517, 424021, 2437, 16384⟩ := by
  decide +kernel

theorem context_13_424021_806517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424021 ⟨806517, by decide⟩ :=
  accepted_of_selected 13 424021 ⟨806517, by decide⟩ ⟨13, 2, 0, 806517, 424021, 2437, 16384⟩
    (by decide) selected_cut_31414

theorem selected_cut_31415 : selected 8 ⟨806543, by decide⟩
    (prefixPartial 13 424022) = some ⟨13, 2, 0, 806543, 424022, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_424022_806543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424022 ⟨806543, by decide⟩ :=
  accepted_of_selected 13 424022 ⟨806543, by decide⟩ ⟨13, 2, 0, 806543, 424022, 1537, 16384⟩
    (by decide) selected_cut_31415

theorem selected_cut_31416 : selected 8 ⟨806551, by decide⟩
    (prefixPartial 13 424023) = some ⟨13, 2, 0, 806551, 424023, 937, 16384⟩ := by
  decide +kernel

theorem context_13_424023_806551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424023 ⟨806551, by decide⟩ :=
  accepted_of_selected 13 424023 ⟨806551, by decide⟩ ⟨13, 2, 0, 806551, 424023, 937, 16384⟩
    (by decide) selected_cut_31416

theorem unmarked_context_12_106005_806552 : frontier 9 ⟨806552, by decide⟩
    (prefixCache 12 106005) (prefixPartial 12 106005) = false := by
  decide +kernel

theorem node_context_12_106005_806552 : EJMOriginalGlobalDAGData.nodes 9 ⟨806552, by decide⟩ =
    .split (coordinate 12) (![⟨806481, by decide⟩,⟨806517, by decide⟩,⟨806543, by decide⟩,⟨806551, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106005_806552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106005 ⟨806552, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106005
    ⟨806552, by decide⟩ (by decide) (![⟨806481, by decide⟩,⟨806517, by decide⟩,⟨806543, by decide⟩,⟨806551, by decide⟩]) unmarked_context_12_106005_806552 node_context_12_106005_806552
  intro a
  fin_cases a
  · exact context_13_424020_806481
  · exact context_13_424021_806517
  · exact context_13_424022_806543
  · exact context_13_424023_806551

theorem selected_cut_31417 : selected 8 ⟨806585, by decide⟩
    (prefixPartial 13 424024) = some ⟨13, 2, 0, 806585, 424024, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_424024_806585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424024 ⟨806585, by decide⟩ :=
  accepted_of_selected 13 424024 ⟨806585, by decide⟩ ⟨13, 2, 0, 806585, 424024, 1709, 16384⟩
    (by decide) selected_cut_31417

theorem selected_cut_31418 : selected 8 ⟨806613, by decide⟩
    (prefixPartial 13 424025) = some ⟨13, 2, 0, 806613, 424025, 2617, 16384⟩ := by
  decide +kernel

theorem context_13_424025_806613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424025 ⟨806613, by decide⟩ :=
  accepted_of_selected 13 424025 ⟨806613, by decide⟩ ⟨13, 2, 0, 806613, 424025, 2617, 16384⟩
    (by decide) selected_cut_31418

theorem selected_cut_31419 : selected 8 ⟨806632, by decide⟩
    (prefixPartial 13 424026) = some ⟨13, 2, 0, 806632, 424026, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_424026_806632 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424026 ⟨806632, by decide⟩ :=
  accepted_of_selected 13 424026 ⟨806632, by decide⟩ ⟨13, 2, 0, 806632, 424026, 1337, 16384⟩
    (by decide) selected_cut_31419

theorem selected_cut_31420 : selected 8 ⟨806638, by decide⟩
    (prefixPartial 13 424027) = some ⟨13, 2, 0, 806638, 424027, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_424027_806638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424027 ⟨806638, by decide⟩ :=
  accepted_of_selected 13 424027 ⟨806638, by decide⟩ ⟨13, 2, 0, 806638, 424027, 1005, 16384⟩
    (by decide) selected_cut_31420

theorem unmarked_context_12_106006_806639 : frontier 9 ⟨806639, by decide⟩
    (prefixCache 12 106006) (prefixPartial 12 106006) = false := by
  decide +kernel

theorem node_context_12_106006_806639 : EJMOriginalGlobalDAGData.nodes 9 ⟨806639, by decide⟩ =
    .split (coordinate 12) (![⟨806585, by decide⟩,⟨806613, by decide⟩,⟨806632, by decide⟩,⟨806638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106006_806639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106006 ⟨806639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106006
    ⟨806639, by decide⟩ (by decide) (![⟨806585, by decide⟩,⟨806613, by decide⟩,⟨806632, by decide⟩,⟨806638, by decide⟩]) unmarked_context_12_106006_806639 node_context_12_106006_806639
  intro a
  fin_cases a
  · exact context_13_424024_806585
  · exact context_13_424025_806613
  · exact context_13_424026_806632
  · exact context_13_424027_806638

theorem selected_cut_31421 : selected 8 ⟨806684, by decide⟩
    (prefixPartial 13 424028) = some ⟨13, 2, 0, 806684, 424028, 2217, 16384⟩ := by
  decide +kernel

theorem context_13_424028_806684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424028 ⟨806684, by decide⟩ :=
  accepted_of_selected 13 424028 ⟨806684, by decide⟩ ⟨13, 2, 0, 806684, 424028, 2217, 16384⟩
    (by decide) selected_cut_31421

theorem selected_cut_31422 : selected 8 ⟨806734, by decide⟩
    (prefixPartial 13 424029) = some ⟨13, 2, 0, 806734, 424029, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_424029_806734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424029 ⟨806734, by decide⟩ :=
  accepted_of_selected 13 424029 ⟨806734, by decide⟩ ⟨13, 2, 0, 806734, 424029, 2905, 16384⟩
    (by decide) selected_cut_31422

theorem selected_cut_31423 : selected 8 ⟨806776, by decide⟩
    (prefixPartial 13 424030) = some ⟨13, 2, 0, 806776, 424030, 1865, 16384⟩ := by
  decide +kernel

theorem context_13_424030_806776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424030 ⟨806776, by decide⟩ :=
  accepted_of_selected 13 424030 ⟨806776, by decide⟩ ⟨13, 2, 0, 806776, 424030, 1865, 16384⟩
    (by decide) selected_cut_31423

theorem selected_cut_31424 : selected 8 ⟨806787, by decide⟩
    (prefixPartial 13 424031) = some ⟨13, 2, 0, 806787, 424031, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_424031_806787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424031 ⟨806787, by decide⟩ :=
  accepted_of_selected 13 424031 ⟨806787, by decide⟩ ⟨13, 2, 0, 806787, 424031, 1057, 16384⟩
    (by decide) selected_cut_31424

theorem unmarked_context_12_106007_806788 : frontier 9 ⟨806788, by decide⟩
    (prefixCache 12 106007) (prefixPartial 12 106007) = false := by
  decide +kernel

theorem node_context_12_106007_806788 : EJMOriginalGlobalDAGData.nodes 9 ⟨806788, by decide⟩ =
    .split (coordinate 12) (![⟨806684, by decide⟩,⟨806734, by decide⟩,⟨806776, by decide⟩,⟨806787, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106007_806788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106007 ⟨806788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106007
    ⟨806788, by decide⟩ (by decide) (![⟨806684, by decide⟩,⟨806734, by decide⟩,⟨806776, by decide⟩,⟨806787, by decide⟩]) unmarked_context_12_106007_806788 node_context_12_106007_806788
  intro a
  fin_cases a
  · exact context_13_424028_806684
  · exact context_13_424029_806734
  · exact context_13_424030_806776
  · exact context_13_424031_806787

theorem unmarked_context_11_26501_806789 : frontier 10 ⟨806789, by decide⟩
    (prefixCache 11 26501) (prefixPartial 11 26501) = false := by
  decide +kernel

theorem node_context_11_26501_806789 : EJMOriginalGlobalDAGData.nodes 10 ⟨806789, by decide⟩ =
    .split (coordinate 11) (![⟨806440, by decide⟩,⟨806552, by decide⟩,⟨806639, by decide⟩,⟨806788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26501_806789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26501 ⟨806789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26501
    ⟨806789, by decide⟩ (by decide) (![⟨806440, by decide⟩,⟨806552, by decide⟩,⟨806639, by decide⟩,⟨806788, by decide⟩]) unmarked_context_11_26501_806789 node_context_11_26501_806789
  intro a
  fin_cases a
  · exact context_12_106004_806440
  · exact context_12_106005_806552
  · exact context_12_106006_806639
  · exact context_12_106007_806788

theorem selected_cut_31425 : selected 8 ⟨806821, by decide⟩
    (prefixPartial 13 424032) = some ⟨13, 2, 0, 806821, 424032, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_424032_806821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424032 ⟨806821, by decide⟩ :=
  accepted_of_selected 13 424032 ⟨806821, by decide⟩ ⟨13, 2, 0, 806821, 424032, 1793, 16384⟩
    (by decide) selected_cut_31425

theorem selected_cut_31426 : selected 8 ⟨806849, by decide⟩
    (prefixPartial 13 424033) = some ⟨13, 2, 0, 806849, 424033, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_424033_806849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424033 ⟨806849, by decide⟩ :=
  accepted_of_selected 13 424033 ⟨806849, by decide⟩ ⟨13, 2, 0, 806849, 424033, 2093, 16384⟩
    (by decide) selected_cut_31426

theorem selected_cut_31427 : selected 8 ⟨806871, by decide⟩
    (prefixPartial 13 424034) = some ⟨13, 2, 0, 806871, 424034, 1649, 16384⟩ := by
  decide +kernel

theorem context_13_424034_806871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424034 ⟨806871, by decide⟩ :=
  accepted_of_selected 13 424034 ⟨806871, by decide⟩ ⟨13, 2, 0, 806871, 424034, 1649, 16384⟩
    (by decide) selected_cut_31427

theorem selected_cut_31428 : selected 8 ⟨806881, by decide⟩
    (prefixPartial 13 424035) = some ⟨13, 2, 0, 806881, 424035, 845, 16384⟩ := by
  decide +kernel

theorem context_13_424035_806881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424035 ⟨806881, by decide⟩ :=
  accepted_of_selected 13 424035 ⟨806881, by decide⟩ ⟨13, 2, 0, 806881, 424035, 845, 16384⟩
    (by decide) selected_cut_31428

theorem unmarked_context_12_106008_806882 : frontier 9 ⟨806882, by decide⟩
    (prefixCache 12 106008) (prefixPartial 12 106008) = false := by
  decide +kernel

theorem node_context_12_106008_806882 : EJMOriginalGlobalDAGData.nodes 9 ⟨806882, by decide⟩ =
    .split (coordinate 12) (![⟨806821, by decide⟩,⟨806849, by decide⟩,⟨806871, by decide⟩,⟨806881, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106008_806882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106008 ⟨806882, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106008
    ⟨806882, by decide⟩ (by decide) (![⟨806821, by decide⟩,⟨806849, by decide⟩,⟨806871, by decide⟩,⟨806881, by decide⟩]) unmarked_context_12_106008_806882 node_context_12_106008_806882
  intro a
  fin_cases a
  · exact context_13_424032_806821
  · exact context_13_424033_806849
  · exact context_13_424034_806871
  · exact context_13_424035_806881

theorem selected_cut_31429 : selected 8 ⟨806922, by decide⟩
    (prefixPartial 13 424036) = some ⟨13, 2, 0, 806922, 424036, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_424036_806922 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424036 ⟨806922, by decide⟩ :=
  accepted_of_selected 13 424036 ⟨806922, by decide⟩ ⟨13, 2, 0, 806922, 424036, 1989, 16384⟩
    (by decide) selected_cut_31429

theorem selected_cut_31430 : selected 8 ⟨806955, by decide⟩
    (prefixPartial 13 424037) = some ⟨13, 2, 0, 806955, 424037, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_424037_806955 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424037 ⟨806955, by decide⟩ :=
  accepted_of_selected 13 424037 ⟨806955, by decide⟩ ⟨13, 2, 0, 806955, 424037, 2221, 16384⟩
    (by decide) selected_cut_31430

theorem selected_cut_31431 : selected 8 ⟨806986, by decide⟩
    (prefixPartial 13 424038) = some ⟨13, 2, 0, 806986, 424038, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_424038_806986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424038 ⟨806986, by decide⟩ :=
  accepted_of_selected 13 424038 ⟨806986, by decide⟩ ⟨13, 2, 0, 806986, 424038, 1609, 16384⟩
    (by decide) selected_cut_31431

theorem selected_cut_31432 : selected 8 ⟨806995, by decide⟩
    (prefixPartial 13 424039) = some ⟨13, 2, 0, 806995, 424039, 949, 16384⟩ := by
  decide +kernel

theorem context_13_424039_806995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424039 ⟨806995, by decide⟩ :=
  accepted_of_selected 13 424039 ⟨806995, by decide⟩ ⟨13, 2, 0, 806995, 424039, 949, 16384⟩
    (by decide) selected_cut_31432

theorem unmarked_context_12_106009_806996 : frontier 9 ⟨806996, by decide⟩
    (prefixCache 12 106009) (prefixPartial 12 106009) = false := by
  decide +kernel

theorem node_context_12_106009_806996 : EJMOriginalGlobalDAGData.nodes 9 ⟨806996, by decide⟩ =
    .split (coordinate 12) (![⟨806922, by decide⟩,⟨806955, by decide⟩,⟨806986, by decide⟩,⟨806995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106009_806996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106009 ⟨806996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106009
    ⟨806996, by decide⟩ (by decide) (![⟨806922, by decide⟩,⟨806955, by decide⟩,⟨806986, by decide⟩,⟨806995, by decide⟩]) unmarked_context_12_106009_806996 node_context_12_106009_806996
  intro a
  fin_cases a
  · exact context_13_424036_806922
  · exact context_13_424037_806955
  · exact context_13_424038_806986
  · exact context_13_424039_806995

theorem selected_cut_31433 : selected 9 ⟨806997, by decide⟩
    (prefixPartial 12 106010) = some ⟨12, 1, 0, 806997, 106010, 1, 65536⟩ := by
  decide +kernel

theorem context_12_106010_806997 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106010 ⟨806997, by decide⟩ :=
  accepted_of_selected 12 106010 ⟨806997, by decide⟩ ⟨12, 1, 0, 806997, 106010, 1, 65536⟩
    (by decide) selected_cut_31433

theorem selected_cut_31434 : selected 8 ⟨807035, by decide⟩
    (prefixPartial 13 424044) = some ⟨13, 2, 0, 807035, 424044, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_424044_807035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424044 ⟨807035, by decide⟩ :=
  accepted_of_selected 13 424044 ⟨807035, by decide⟩ ⟨13, 2, 0, 807035, 424044, 2097, 16384⟩
    (by decide) selected_cut_31434

theorem selected_cut_31435 : selected 8 ⟨807081, by decide⟩
    (prefixPartial 13 424045) = some ⟨13, 2, 0, 807081, 424045, 3025, 16384⟩ := by
  decide +kernel

theorem context_13_424045_807081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424045 ⟨807081, by decide⟩ :=
  accepted_of_selected 13 424045 ⟨807081, by decide⟩ ⟨13, 2, 0, 807081, 424045, 3025, 16384⟩
    (by decide) selected_cut_31435

theorem selected_cut_31436 : selected 8 ⟨807107, by decide⟩
    (prefixPartial 13 424046) = some ⟨13, 2, 0, 807107, 424046, 1717, 16384⟩ := by
  decide +kernel

theorem context_13_424046_807107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424046 ⟨807107, by decide⟩ :=
  accepted_of_selected 13 424046 ⟨807107, by decide⟩ ⟨13, 2, 0, 807107, 424046, 1717, 16384⟩
    (by decide) selected_cut_31436

theorem selected_cut_31437 : selected 8 ⟨807114, by decide⟩
    (prefixPartial 13 424047) = some ⟨13, 2, 0, 807114, 424047, 957, 16384⟩ := by
  decide +kernel

theorem context_13_424047_807114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424047 ⟨807114, by decide⟩ :=
  accepted_of_selected 13 424047 ⟨807114, by decide⟩ ⟨13, 2, 0, 807114, 424047, 957, 16384⟩
    (by decide) selected_cut_31437

theorem unmarked_context_12_106011_807115 : frontier 9 ⟨807115, by decide⟩
    (prefixCache 12 106011) (prefixPartial 12 106011) = false := by
  decide +kernel

theorem node_context_12_106011_807115 : EJMOriginalGlobalDAGData.nodes 9 ⟨807115, by decide⟩ =
    .split (coordinate 12) (![⟨807035, by decide⟩,⟨807081, by decide⟩,⟨807107, by decide⟩,⟨807114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106011_807115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106011 ⟨807115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106011
    ⟨807115, by decide⟩ (by decide) (![⟨807035, by decide⟩,⟨807081, by decide⟩,⟨807107, by decide⟩,⟨807114, by decide⟩]) unmarked_context_12_106011_807115 node_context_12_106011_807115
  intro a
  fin_cases a
  · exact context_13_424044_807035
  · exact context_13_424045_807081
  · exact context_13_424046_807107
  · exact context_13_424047_807114

theorem unmarked_context_11_26502_807116 : frontier 10 ⟨807116, by decide⟩
    (prefixCache 11 26502) (prefixPartial 11 26502) = false := by
  decide +kernel

theorem node_context_11_26502_807116 : EJMOriginalGlobalDAGData.nodes 10 ⟨807116, by decide⟩ =
    .split (coordinate 11) (![⟨806882, by decide⟩,⟨806996, by decide⟩,⟨806997, by decide⟩,⟨807115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26502_807116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26502 ⟨807116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26502
    ⟨807116, by decide⟩ (by decide) (![⟨806882, by decide⟩,⟨806996, by decide⟩,⟨806997, by decide⟩,⟨807115, by decide⟩]) unmarked_context_11_26502_807116 node_context_11_26502_807116
  intro a
  fin_cases a
  · exact context_12_106008_806882
  · exact context_12_106009_806996
  · exact context_12_106010_806997
  · exact context_12_106011_807115

theorem selected_cut_31438 : selected 8 ⟨807145, by decide⟩
    (prefixPartial 13 424048) = some ⟨13, 2, 0, 807145, 424048, 1521, 16384⟩ := by
  decide +kernel

theorem context_13_424048_807145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424048 ⟨807145, by decide⟩ :=
  accepted_of_selected 13 424048 ⟨807145, by decide⟩ ⟨13, 2, 0, 807145, 424048, 1521, 16384⟩
    (by decide) selected_cut_31438

theorem selected_cut_31439 : selected 8 ⟨807178, by decide⟩
    (prefixPartial 13 424049) = some ⟨13, 2, 0, 807178, 424049, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_424049_807178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424049 ⟨807178, by decide⟩ :=
  accepted_of_selected 13 424049 ⟨807178, by decide⟩ ⟨13, 2, 0, 807178, 424049, 2157, 16384⟩
    (by decide) selected_cut_31439

theorem selected_cut_31440 : selected 8 ⟨807198, by decide⟩
    (prefixPartial 13 424050) = some ⟨13, 2, 0, 807198, 424050, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_424050_807198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424050 ⟨807198, by decide⟩ :=
  accepted_of_selected 13 424050 ⟨807198, by decide⟩ ⟨13, 2, 0, 807198, 424050, 1601, 16384⟩
    (by decide) selected_cut_31440

theorem selected_cut_31441 : selected 8 ⟨807206, by decide⟩
    (prefixPartial 13 424051) = some ⟨13, 2, 0, 807206, 424051, 945, 16384⟩ := by
  decide +kernel

theorem context_13_424051_807206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424051 ⟨807206, by decide⟩ :=
  accepted_of_selected 13 424051 ⟨807206, by decide⟩ ⟨13, 2, 0, 807206, 424051, 945, 16384⟩
    (by decide) selected_cut_31441

theorem unmarked_context_12_106012_807207 : frontier 9 ⟨807207, by decide⟩
    (prefixCache 12 106012) (prefixPartial 12 106012) = false := by
  decide +kernel

theorem node_context_12_106012_807207 : EJMOriginalGlobalDAGData.nodes 9 ⟨807207, by decide⟩ =
    .split (coordinate 12) (![⟨807145, by decide⟩,⟨807178, by decide⟩,⟨807198, by decide⟩,⟨807206, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106012_807207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106012 ⟨807207, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106012
    ⟨807207, by decide⟩ (by decide) (![⟨807145, by decide⟩,⟨807178, by decide⟩,⟨807198, by decide⟩,⟨807206, by decide⟩]) unmarked_context_12_106012_807207 node_context_12_106012_807207
  intro a
  fin_cases a
  · exact context_13_424048_807145
  · exact context_13_424049_807178
  · exact context_13_424050_807198
  · exact context_13_424051_807206

theorem selected_cut_31442 : selected 8 ⟨807239, by decide⟩
    (prefixPartial 13 424052) = some ⟨13, 2, 0, 807239, 424052, 1761, 16384⟩ := by
  decide +kernel

theorem context_13_424052_807239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424052 ⟨807239, by decide⟩ :=
  accepted_of_selected 13 424052 ⟨807239, by decide⟩ ⟨13, 2, 0, 807239, 424052, 1761, 16384⟩
    (by decide) selected_cut_31442

theorem selected_cut_31443 : selected 8 ⟨807281, by decide⟩
    (prefixPartial 13 424053) = some ⟨13, 2, 0, 807281, 424053, 2221, 16384⟩ := by
  decide +kernel

theorem context_13_424053_807281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424053 ⟨807281, by decide⟩ :=
  accepted_of_selected 13 424053 ⟨807281, by decide⟩ ⟨13, 2, 0, 807281, 424053, 2221, 16384⟩
    (by decide) selected_cut_31443

theorem selected_cut_31444 : selected 8 ⟨807307, by decide⟩
    (prefixPartial 13 424054) = some ⟨13, 2, 0, 807307, 424054, 1553, 16384⟩ := by
  decide +kernel

theorem context_13_424054_807307 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424054 ⟨807307, by decide⟩ :=
  accepted_of_selected 13 424054 ⟨807307, by decide⟩ ⟨13, 2, 0, 807307, 424054, 1553, 16384⟩
    (by decide) selected_cut_31444

theorem selected_cut_31445 : selected 8 ⟨807320, by decide⟩
    (prefixPartial 13 424055) = some ⟨13, 2, 0, 807320, 424055, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_424055_807320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424055 ⟨807320, by decide⟩ :=
  accepted_of_selected 13 424055 ⟨807320, by decide⟩ ⟨13, 2, 0, 807320, 424055, 1001, 16384⟩
    (by decide) selected_cut_31445

theorem unmarked_context_12_106013_807321 : frontier 9 ⟨807321, by decide⟩
    (prefixCache 12 106013) (prefixPartial 12 106013) = false := by
  decide +kernel

theorem node_context_12_106013_807321 : EJMOriginalGlobalDAGData.nodes 9 ⟨807321, by decide⟩ =
    .split (coordinate 12) (![⟨807239, by decide⟩,⟨807281, by decide⟩,⟨807307, by decide⟩,⟨807320, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106013_807321 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106013 ⟨807321, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106013
    ⟨807321, by decide⟩ (by decide) (![⟨807239, by decide⟩,⟨807281, by decide⟩,⟨807307, by decide⟩,⟨807320, by decide⟩]) unmarked_context_12_106013_807321 node_context_12_106013_807321
  intro a
  fin_cases a
  · exact context_13_424052_807239
  · exact context_13_424053_807281
  · exact context_13_424054_807307
  · exact context_13_424055_807320

theorem selected_cut_31446 : selected 8 ⟨807344, by decide⟩
    (prefixPartial 13 424056) = some ⟨13, 2, 0, 807344, 424056, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_424056_807344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424056 ⟨807344, by decide⟩ :=
  accepted_of_selected 13 424056 ⟨807344, by decide⟩ ⟨13, 2, 0, 807344, 424056, 1409, 16384⟩
    (by decide) selected_cut_31446

theorem selected_cut_31447 : selected 8 ⟨807377, by decide⟩
    (prefixPartial 13 424057) = some ⟨13, 2, 0, 807377, 424057, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_424057_807377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424057 ⟨807377, by decide⟩ :=
  accepted_of_selected 13 424057 ⟨807377, by decide⟩ ⟨13, 2, 0, 807377, 424057, 2565, 16384⟩
    (by decide) selected_cut_31447

theorem selected_cut_31448 : selected 8 ⟨807396, by decide⟩
    (prefixPartial 13 424058) = some ⟨13, 2, 0, 807396, 424058, 1373, 16384⟩ := by
  decide +kernel

theorem context_13_424058_807396 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424058 ⟨807396, by decide⟩ :=
  accepted_of_selected 13 424058 ⟨807396, by decide⟩ ⟨13, 2, 0, 807396, 424058, 1373, 16384⟩
    (by decide) selected_cut_31448

theorem selected_cut_31449 : selected 8 ⟨807403, by decide⟩
    (prefixPartial 13 424059) = some ⟨13, 2, 0, 807403, 424059, 1005, 16384⟩ := by
  decide +kernel

theorem context_13_424059_807403 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424059 ⟨807403, by decide⟩ :=
  accepted_of_selected 13 424059 ⟨807403, by decide⟩ ⟨13, 2, 0, 807403, 424059, 1005, 16384⟩
    (by decide) selected_cut_31449

theorem unmarked_context_12_106014_807404 : frontier 9 ⟨807404, by decide⟩
    (prefixCache 12 106014) (prefixPartial 12 106014) = false := by
  decide +kernel

theorem node_context_12_106014_807404 : EJMOriginalGlobalDAGData.nodes 9 ⟨807404, by decide⟩ =
    .split (coordinate 12) (![⟨807344, by decide⟩,⟨807377, by decide⟩,⟨807396, by decide⟩,⟨807403, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106014_807404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106014 ⟨807404, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106014
    ⟨807404, by decide⟩ (by decide) (![⟨807344, by decide⟩,⟨807377, by decide⟩,⟨807396, by decide⟩,⟨807403, by decide⟩]) unmarked_context_12_106014_807404 node_context_12_106014_807404
  intro a
  fin_cases a
  · exact context_13_424056_807344
  · exact context_13_424057_807377
  · exact context_13_424058_807396
  · exact context_13_424059_807403

theorem selected_cut_31450 : selected 8 ⟨807427, by decide⟩
    (prefixPartial 13 424060) = some ⟨13, 2, 0, 807427, 424060, 1757, 16384⟩ := by
  decide +kernel

theorem context_13_424060_807427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424060 ⟨807427, by decide⟩ :=
  accepted_of_selected 13 424060 ⟨807427, by decide⟩ ⟨13, 2, 0, 807427, 424060, 1757, 16384⟩
    (by decide) selected_cut_31450

theorem selected_cut_31451 : selected 8 ⟨807464, by decide⟩
    (prefixPartial 13 424061) = some ⟨13, 2, 0, 807464, 424061, 2693, 16384⟩ := by
  decide +kernel

theorem context_13_424061_807464 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424061 ⟨807464, by decide⟩ :=
  accepted_of_selected 13 424061 ⟨807464, by decide⟩ ⟨13, 2, 0, 807464, 424061, 2693, 16384⟩
    (by decide) selected_cut_31451

theorem selected_cut_31452 : selected 8 ⟨807486, by decide⟩
    (prefixPartial 13 424062) = some ⟨13, 2, 0, 807486, 424062, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_424062_807486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424062 ⟨807486, by decide⟩ :=
  accepted_of_selected 13 424062 ⟨807486, by decide⟩ ⟨13, 2, 0, 807486, 424062, 1753, 16384⟩
    (by decide) selected_cut_31452

theorem selected_cut_31453 : selected 8 ⟨807496, by decide⟩
    (prefixPartial 13 424063) = some ⟨13, 2, 0, 807496, 424063, 1045, 16384⟩ := by
  decide +kernel

theorem context_13_424063_807496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424063 ⟨807496, by decide⟩ :=
  accepted_of_selected 13 424063 ⟨807496, by decide⟩ ⟨13, 2, 0, 807496, 424063, 1045, 16384⟩
    (by decide) selected_cut_31453

theorem unmarked_context_12_106015_807497 : frontier 9 ⟨807497, by decide⟩
    (prefixCache 12 106015) (prefixPartial 12 106015) = false := by
  decide +kernel

theorem node_context_12_106015_807497 : EJMOriginalGlobalDAGData.nodes 9 ⟨807497, by decide⟩ =
    .split (coordinate 12) (![⟨807427, by decide⟩,⟨807464, by decide⟩,⟨807486, by decide⟩,⟨807496, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106015_807497 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106015 ⟨807497, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106015
    ⟨807497, by decide⟩ (by decide) (![⟨807427, by decide⟩,⟨807464, by decide⟩,⟨807486, by decide⟩,⟨807496, by decide⟩]) unmarked_context_12_106015_807497 node_context_12_106015_807497
  intro a
  fin_cases a
  · exact context_13_424060_807427
  · exact context_13_424061_807464
  · exact context_13_424062_807486
  · exact context_13_424063_807496

theorem unmarked_context_11_26503_807498 : frontier 10 ⟨807498, by decide⟩
    (prefixCache 11 26503) (prefixPartial 11 26503) = false := by
  decide +kernel

theorem node_context_11_26503_807498 : EJMOriginalGlobalDAGData.nodes 10 ⟨807498, by decide⟩ =
    .split (coordinate 11) (![⟨807207, by decide⟩,⟨807321, by decide⟩,⟨807404, by decide⟩,⟨807497, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26503_807498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26503 ⟨807498, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26503
    ⟨807498, by decide⟩ (by decide) (![⟨807207, by decide⟩,⟨807321, by decide⟩,⟨807404, by decide⟩,⟨807497, by decide⟩]) unmarked_context_11_26503_807498 node_context_11_26503_807498
  intro a
  fin_cases a
  · exact context_12_106012_807207
  · exact context_12_106013_807321
  · exact context_12_106014_807404
  · exact context_12_106015_807497

theorem unmarked_context_10_6625_807499 : frontier 11 ⟨807499, by decide⟩
    (prefixCache 10 6625) (prefixPartial 10 6625) = false := by
  decide +kernel

theorem node_context_10_6625_807499 : EJMOriginalGlobalDAGData.nodes 11 ⟨807499, by decide⟩ =
    .split (coordinate 10) (![⟨806334, by decide⟩,⟨806789, by decide⟩,⟨807116, by decide⟩,⟨807498, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6625_807499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6625 ⟨807499, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6625
    ⟨807499, by decide⟩ (by decide) (![⟨806334, by decide⟩,⟨806789, by decide⟩,⟨807116, by decide⟩,⟨807498, by decide⟩]) unmarked_context_10_6625_807499 node_context_10_6625_807499
  intro a
  fin_cases a
  · exact context_11_26500_806334
  · exact context_11_26501_806789
  · exact context_11_26502_807116
  · exact context_11_26503_807498

theorem selected_cut_31454 : selected 8 ⟨807516, by decide⟩
    (prefixPartial 13 424064) = some ⟨13, 2, 0, 807516, 424064, 981, 16384⟩ := by
  decide +kernel

theorem context_13_424064_807516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424064 ⟨807516, by decide⟩ :=
  accepted_of_selected 13 424064 ⟨807516, by decide⟩ ⟨13, 2, 0, 807516, 424064, 981, 16384⟩
    (by decide) selected_cut_31454

theorem selected_cut_31455 : selected 8 ⟨807542, by decide⟩
    (prefixPartial 13 424065) = some ⟨13, 2, 0, 807542, 424065, 1997, 16384⟩ := by
  decide +kernel

theorem context_13_424065_807542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424065 ⟨807542, by decide⟩ :=
  accepted_of_selected 13 424065 ⟨807542, by decide⟩ ⟨13, 2, 0, 807542, 424065, 1997, 16384⟩
    (by decide) selected_cut_31455

theorem selected_cut_31456 : selected 8 ⟨807564, by decide⟩
    (prefixPartial 13 424066) = some ⟨13, 2, 0, 807564, 424066, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_424066_807564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424066 ⟨807564, by decide⟩ :=
  accepted_of_selected 13 424066 ⟨807564, by decide⟩ ⟨13, 2, 0, 807564, 424066, 1301, 16384⟩
    (by decide) selected_cut_31456

theorem selected_cut_31457 : selected 8 ⟨807577, by decide⟩
    (prefixPartial 13 424067) = some ⟨13, 2, 0, 807577, 424067, 737, 16384⟩ := by
  decide +kernel

theorem context_13_424067_807577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424067 ⟨807577, by decide⟩ :=
  accepted_of_selected 13 424067 ⟨807577, by decide⟩ ⟨13, 2, 0, 807577, 424067, 737, 16384⟩
    (by decide) selected_cut_31457

theorem unmarked_context_12_106016_807578 : frontier 9 ⟨807578, by decide⟩
    (prefixCache 12 106016) (prefixPartial 12 106016) = false := by
  decide +kernel

theorem node_context_12_106016_807578 : EJMOriginalGlobalDAGData.nodes 9 ⟨807578, by decide⟩ =
    .split (coordinate 12) (![⟨807516, by decide⟩,⟨807542, by decide⟩,⟨807564, by decide⟩,⟨807577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106016_807578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106016 ⟨807578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106016
    ⟨807578, by decide⟩ (by decide) (![⟨807516, by decide⟩,⟨807542, by decide⟩,⟨807564, by decide⟩,⟨807577, by decide⟩]) unmarked_context_12_106016_807578 node_context_12_106016_807578
  intro a
  fin_cases a
  · exact context_13_424064_807516
  · exact context_13_424065_807542
  · exact context_13_424066_807564
  · exact context_13_424067_807577

theorem selected_cut_31458 : selected 8 ⟨807606, by decide⟩
    (prefixPartial 13 424068) = some ⟨13, 2, 0, 807606, 424068, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_424068_807606 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424068 ⟨807606, by decide⟩ :=
  accepted_of_selected 13 424068 ⟨807606, by decide⟩ ⟨13, 2, 0, 807606, 424068, 1145, 16384⟩
    (by decide) selected_cut_31458

theorem selected_cut_31459 : selected 8 ⟨807662, by decide⟩
    (prefixPartial 13 424069) = some ⟨13, 2, 0, 807662, 424069, 2733, 16384⟩ := by
  decide +kernel

theorem context_13_424069_807662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424069 ⟨807662, by decide⟩ :=
  accepted_of_selected 13 424069 ⟨807662, by decide⟩ ⟨13, 2, 0, 807662, 424069, 2733, 16384⟩
    (by decide) selected_cut_31459

theorem selected_cut_31460 : selected 8 ⟨807689, by decide⟩
    (prefixPartial 13 424070) = some ⟨13, 2, 0, 807689, 424070, 1433, 16384⟩ := by
  decide +kernel

theorem context_13_424070_807689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424070 ⟨807689, by decide⟩ :=
  accepted_of_selected 13 424070 ⟨807689, by decide⟩ ⟨13, 2, 0, 807689, 424070, 1433, 16384⟩
    (by decide) selected_cut_31460

theorem selected_cut_31461 : selected 8 ⟨807698, by decide⟩
    (prefixPartial 13 424071) = some ⟨13, 2, 0, 807698, 424071, 821, 16384⟩ := by
  decide +kernel

theorem context_13_424071_807698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424071 ⟨807698, by decide⟩ :=
  accepted_of_selected 13 424071 ⟨807698, by decide⟩ ⟨13, 2, 0, 807698, 424071, 821, 16384⟩
    (by decide) selected_cut_31461

theorem unmarked_context_12_106017_807699 : frontier 9 ⟨807699, by decide⟩
    (prefixCache 12 106017) (prefixPartial 12 106017) = false := by
  decide +kernel

theorem node_context_12_106017_807699 : EJMOriginalGlobalDAGData.nodes 9 ⟨807699, by decide⟩ =
    .split (coordinate 12) (![⟨807606, by decide⟩,⟨807662, by decide⟩,⟨807689, by decide⟩,⟨807698, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106017_807699 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106017 ⟨807699, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106017
    ⟨807699, by decide⟩ (by decide) (![⟨807606, by decide⟩,⟨807662, by decide⟩,⟨807689, by decide⟩,⟨807698, by decide⟩]) unmarked_context_12_106017_807699 node_context_12_106017_807699
  intro a
  fin_cases a
  · exact context_13_424068_807606
  · exact context_13_424069_807662
  · exact context_13_424070_807689
  · exact context_13_424071_807698

theorem selected_cut_31462 : selected 8 ⟨807716, by decide⟩
    (prefixPartial 13 424072) = some ⟨13, 2, 0, 807716, 424072, 897, 16384⟩ := by
  decide +kernel

theorem context_13_424072_807716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424072 ⟨807716, by decide⟩ :=
  accepted_of_selected 13 424072 ⟨807716, by decide⟩ ⟨13, 2, 0, 807716, 424072, 897, 16384⟩
    (by decide) selected_cut_31462

theorem selected_cut_31463 : selected 8 ⟨807741, by decide⟩
    (prefixPartial 13 424073) = some ⟨13, 2, 0, 807741, 424073, 2233, 16384⟩ := by
  decide +kernel

theorem context_13_424073_807741 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424073 ⟨807741, by decide⟩ :=
  accepted_of_selected 13 424073 ⟨807741, by decide⟩ ⟨13, 2, 0, 807741, 424073, 2233, 16384⟩
    (by decide) selected_cut_31463

theorem selected_cut_31464 : selected 8 ⟨807760, by decide⟩
    (prefixPartial 13 424074) = some ⟨13, 2, 0, 807760, 424074, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_424074_807760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424074 ⟨807760, by decide⟩ :=
  accepted_of_selected 13 424074 ⟨807760, by decide⟩ ⟨13, 2, 0, 807760, 424074, 1161, 16384⟩
    (by decide) selected_cut_31464

theorem selected_cut_31465 : selected 8 ⟨807767, by decide⟩
    (prefixPartial 13 424075) = some ⟨13, 2, 0, 807767, 424075, 853, 16384⟩ := by
  decide +kernel

theorem context_13_424075_807767 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424075 ⟨807767, by decide⟩ :=
  accepted_of_selected 13 424075 ⟨807767, by decide⟩ ⟨13, 2, 0, 807767, 424075, 853, 16384⟩
    (by decide) selected_cut_31465

theorem unmarked_context_12_106018_807768 : frontier 9 ⟨807768, by decide⟩
    (prefixCache 12 106018) (prefixPartial 12 106018) = false := by
  decide +kernel

theorem node_context_12_106018_807768 : EJMOriginalGlobalDAGData.nodes 9 ⟨807768, by decide⟩ =
    .split (coordinate 12) (![⟨807716, by decide⟩,⟨807741, by decide⟩,⟨807760, by decide⟩,⟨807767, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106018_807768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106018 ⟨807768, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106018
    ⟨807768, by decide⟩ (by decide) (![⟨807716, by decide⟩,⟨807741, by decide⟩,⟨807760, by decide⟩,⟨807767, by decide⟩]) unmarked_context_12_106018_807768 node_context_12_106018_807768
  intro a
  fin_cases a
  · exact context_13_424072_807716
  · exact context_13_424073_807741
  · exact context_13_424074_807760
  · exact context_13_424075_807767

theorem selected_cut_31466 : selected 8 ⟨807795, by decide⟩
    (prefixPartial 13 424076) = some ⟨13, 2, 0, 807795, 424076, 1165, 16384⟩ := by
  decide +kernel

theorem context_13_424076_807795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424076 ⟨807795, by decide⟩ :=
  accepted_of_selected 13 424076 ⟨807795, by decide⟩ ⟨13, 2, 0, 807795, 424076, 1165, 16384⟩
    (by decide) selected_cut_31466

theorem selected_cut_31467 : selected 8 ⟨807846, by decide⟩
    (prefixPartial 13 424077) = some ⟨13, 2, 0, 807846, 424077, 2809, 16384⟩ := by
  decide +kernel

theorem context_13_424077_807846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424077 ⟨807846, by decide⟩ :=
  accepted_of_selected 13 424077 ⟨807846, by decide⟩ ⟨13, 2, 0, 807846, 424077, 2809, 16384⟩
    (by decide) selected_cut_31467

theorem selected_cut_31468 : selected 8 ⟨807874, by decide⟩
    (prefixPartial 13 424078) = some ⟨13, 2, 0, 807874, 424078, 1565, 16384⟩ := by
  decide +kernel

theorem context_13_424078_807874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424078 ⟨807874, by decide⟩ :=
  accepted_of_selected 13 424078 ⟨807874, by decide⟩ ⟨13, 2, 0, 807874, 424078, 1565, 16384⟩
    (by decide) selected_cut_31468

theorem selected_cut_31469 : selected 8 ⟨807879, by decide⟩
    (prefixPartial 13 424079) = some ⟨13, 2, 0, 807879, 424079, 913, 16384⟩ := by
  decide +kernel

theorem context_13_424079_807879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424079 ⟨807879, by decide⟩ :=
  accepted_of_selected 13 424079 ⟨807879, by decide⟩ ⟨13, 2, 0, 807879, 424079, 913, 16384⟩
    (by decide) selected_cut_31469

theorem unmarked_context_12_106019_807880 : frontier 9 ⟨807880, by decide⟩
    (prefixCache 12 106019) (prefixPartial 12 106019) = false := by
  decide +kernel

theorem node_context_12_106019_807880 : EJMOriginalGlobalDAGData.nodes 9 ⟨807880, by decide⟩ =
    .split (coordinate 12) (![⟨807795, by decide⟩,⟨807846, by decide⟩,⟨807874, by decide⟩,⟨807879, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106019_807880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106019 ⟨807880, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106019
    ⟨807880, by decide⟩ (by decide) (![⟨807795, by decide⟩,⟨807846, by decide⟩,⟨807874, by decide⟩,⟨807879, by decide⟩]) unmarked_context_12_106019_807880 node_context_12_106019_807880
  intro a
  fin_cases a
  · exact context_13_424076_807795
  · exact context_13_424077_807846
  · exact context_13_424078_807874
  · exact context_13_424079_807879

theorem unmarked_context_11_26504_807881 : frontier 10 ⟨807881, by decide⟩
    (prefixCache 11 26504) (prefixPartial 11 26504) = false := by
  decide +kernel

theorem node_context_11_26504_807881 : EJMOriginalGlobalDAGData.nodes 10 ⟨807881, by decide⟩ =
    .split (coordinate 11) (![⟨807578, by decide⟩,⟨807699, by decide⟩,⟨807768, by decide⟩,⟨807880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26504_807881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26504 ⟨807881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26504
    ⟨807881, by decide⟩ (by decide) (![⟨807578, by decide⟩,⟨807699, by decide⟩,⟨807768, by decide⟩,⟨807880, by decide⟩]) unmarked_context_11_26504_807881 node_context_11_26504_807881
  intro a
  fin_cases a
  · exact context_12_106016_807578
  · exact context_12_106017_807699
  · exact context_12_106018_807768
  · exact context_12_106019_807880

theorem selected_cut_31470 : selected 8 ⟨807900, by decide⟩
    (prefixPartial 13 424080) = some ⟨13, 2, 0, 807900, 424080, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_424080_807900 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424080 ⟨807900, by decide⟩ :=
  accepted_of_selected 13 424080 ⟨807900, by decide⟩ ⟨13, 2, 0, 807900, 424080, 1001, 16384⟩
    (by decide) selected_cut_31470

theorem selected_cut_31471 : selected 8 ⟨807941, by decide⟩
    (prefixPartial 13 424081) = some ⟨13, 2, 0, 807941, 424081, 2457, 16384⟩ := by
  decide +kernel

theorem context_13_424081_807941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424081 ⟨807941, by decide⟩ :=
  accepted_of_selected 13 424081 ⟨807941, by decide⟩ ⟨13, 2, 0, 807941, 424081, 2457, 16384⟩
    (by decide) selected_cut_31471

theorem selected_cut_31472 : selected 8 ⟨807973, by decide⟩
    (prefixPartial 13 424082) = some ⟨13, 2, 0, 807973, 424082, 1573, 16384⟩ := by
  decide +kernel

theorem context_13_424082_807973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424082 ⟨807973, by decide⟩ :=
  accepted_of_selected 13 424082 ⟨807973, by decide⟩ ⟨13, 2, 0, 807973, 424082, 1573, 16384⟩
    (by decide) selected_cut_31472

theorem selected_cut_31473 : selected 8 ⟨807982, by decide⟩
    (prefixPartial 13 424083) = some ⟨13, 2, 0, 807982, 424083, 869, 16384⟩ := by
  decide +kernel

theorem context_13_424083_807982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424083 ⟨807982, by decide⟩ :=
  accepted_of_selected 13 424083 ⟨807982, by decide⟩ ⟨13, 2, 0, 807982, 424083, 869, 16384⟩
    (by decide) selected_cut_31473

theorem unmarked_context_12_106020_807983 : frontier 9 ⟨807983, by decide⟩
    (prefixCache 12 106020) (prefixPartial 12 106020) = false := by
  decide +kernel

theorem node_context_12_106020_807983 : EJMOriginalGlobalDAGData.nodes 9 ⟨807983, by decide⟩ =
    .split (coordinate 12) (![⟨807900, by decide⟩,⟨807941, by decide⟩,⟨807973, by decide⟩,⟨807982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106020_807983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106020 ⟨807983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106020
    ⟨807983, by decide⟩ (by decide) (![⟨807900, by decide⟩,⟨807941, by decide⟩,⟨807973, by decide⟩,⟨807982, by decide⟩]) unmarked_context_12_106020_807983 node_context_12_106020_807983
  intro a
  fin_cases a
  · exact context_13_424080_807900
  · exact context_13_424081_807941
  · exact context_13_424082_807973
  · exact context_13_424083_807982

theorem selected_cut_31474 : selected 8 ⟨808009, by decide⟩
    (prefixPartial 13 424084) = some ⟨13, 2, 0, 808009, 424084, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_424084_808009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424084 ⟨808009, by decide⟩ :=
  accepted_of_selected 13 424084 ⟨808009, by decide⟩ ⟨13, 2, 0, 808009, 424084, 1117, 16384⟩
    (by decide) selected_cut_31474

theorem selected_cut_31475 : selected 8 ⟨808061, by decide⟩
    (prefixPartial 13 424085) = some ⟨13, 2, 0, 808061, 424085, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_424085_808061 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424085 ⟨808061, by decide⟩ :=
  accepted_of_selected 13 424085 ⟨808061, by decide⟩ ⟨13, 2, 0, 808061, 424085, 2689, 16384⟩
    (by decide) selected_cut_31475

theorem selected_cut_31476 : selected 8 ⟨808092, by decide⟩
    (prefixPartial 13 424086) = some ⟨13, 2, 0, 808092, 424086, 1441, 16384⟩ := by
  decide +kernel

theorem context_13_424086_808092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424086 ⟨808092, by decide⟩ :=
  accepted_of_selected 13 424086 ⟨808092, by decide⟩ ⟨13, 2, 0, 808092, 424086, 1441, 16384⟩
    (by decide) selected_cut_31476

theorem selected_cut_31477 : selected 8 ⟨808103, by decide⟩
    (prefixPartial 13 424087) = some ⟨13, 2, 0, 808103, 424087, 797, 16384⟩ := by
  decide +kernel

theorem context_13_424087_808103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424087 ⟨808103, by decide⟩ :=
  accepted_of_selected 13 424087 ⟨808103, by decide⟩ ⟨13, 2, 0, 808103, 424087, 797, 16384⟩
    (by decide) selected_cut_31477

theorem unmarked_context_12_106021_808104 : frontier 9 ⟨808104, by decide⟩
    (prefixCache 12 106021) (prefixPartial 12 106021) = false := by
  decide +kernel

theorem node_context_12_106021_808104 : EJMOriginalGlobalDAGData.nodes 9 ⟨808104, by decide⟩ =
    .split (coordinate 12) (![⟨808009, by decide⟩,⟨808061, by decide⟩,⟨808092, by decide⟩,⟨808103, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106021_808104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106021 ⟨808104, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106021
    ⟨808104, by decide⟩ (by decide) (![⟨808009, by decide⟩,⟨808061, by decide⟩,⟨808092, by decide⟩,⟨808103, by decide⟩]) unmarked_context_12_106021_808104 node_context_12_106021_808104
  intro a
  fin_cases a
  · exact context_13_424084_808009
  · exact context_13_424085_808061
  · exact context_13_424086_808092
  · exact context_13_424087_808103

theorem selected_cut_31478 : selected 8 ⟨808121, by decide⟩
    (prefixPartial 13 424088) = some ⟨13, 2, 0, 808121, 424088, 889, 16384⟩ := by
  decide +kernel

theorem context_13_424088_808121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424088 ⟨808121, by decide⟩ :=
  accepted_of_selected 13 424088 ⟨808121, by decide⟩ ⟨13, 2, 0, 808121, 424088, 889, 16384⟩
    (by decide) selected_cut_31478

theorem selected_cut_31479 : selected 8 ⟨808152, by decide⟩
    (prefixPartial 13 424089) = some ⟨13, 2, 0, 808152, 424089, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_424089_808152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424089 ⟨808152, by decide⟩ :=
  accepted_of_selected 13 424089 ⟨808152, by decide⟩ ⟨13, 2, 0, 808152, 424089, 2453, 16384⟩
    (by decide) selected_cut_31479

theorem selected_cut_31480 : selected 8 ⟨808174, by decide⟩
    (prefixPartial 13 424090) = some ⟨13, 2, 0, 808174, 424090, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_424090_808174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424090 ⟨808174, by decide⟩ :=
  accepted_of_selected 13 424090 ⟨808174, by decide⟩ ⟨13, 2, 0, 808174, 424090, 1325, 16384⟩
    (by decide) selected_cut_31480

theorem selected_cut_31481 : selected 8 ⟨808182, by decide⟩
    (prefixPartial 13 424091) = some ⟨13, 2, 0, 808182, 424091, 905, 16384⟩ := by
  decide +kernel

theorem context_13_424091_808182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424091 ⟨808182, by decide⟩ :=
  accepted_of_selected 13 424091 ⟨808182, by decide⟩ ⟨13, 2, 0, 808182, 424091, 905, 16384⟩
    (by decide) selected_cut_31481

theorem unmarked_context_12_106022_808183 : frontier 9 ⟨808183, by decide⟩
    (prefixCache 12 106022) (prefixPartial 12 106022) = false := by
  decide +kernel

theorem node_context_12_106022_808183 : EJMOriginalGlobalDAGData.nodes 9 ⟨808183, by decide⟩ =
    .split (coordinate 12) (![⟨808121, by decide⟩,⟨808152, by decide⟩,⟨808174, by decide⟩,⟨808182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106022_808183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106022 ⟨808183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106022
    ⟨808183, by decide⟩ (by decide) (![⟨808121, by decide⟩,⟨808152, by decide⟩,⟨808174, by decide⟩,⟨808182, by decide⟩]) unmarked_context_12_106022_808183 node_context_12_106022_808183
  intro a
  fin_cases a
  · exact context_13_424088_808121
  · exact context_13_424089_808152
  · exact context_13_424090_808174
  · exact context_13_424091_808182

theorem selected_cut_31482 : selected 8 ⟨808207, by decide⟩
    (prefixPartial 13 424092) = some ⟨13, 2, 0, 808207, 424092, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_424092_808207 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424092 ⟨808207, by decide⟩ :=
  accepted_of_selected 13 424092 ⟨808207, by decide⟩ ⟨13, 2, 0, 808207, 424092, 1101, 16384⟩
    (by decide) selected_cut_31482

theorem selected_cut_31483 : selected 8 ⟨808261, by decide⟩
    (prefixPartial 13 424093) = some ⟨13, 2, 0, 808261, 424093, 3021, 16384⟩ := by
  decide +kernel

theorem context_13_424093_808261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424093 ⟨808261, by decide⟩ :=
  accepted_of_selected 13 424093 ⟨808261, by decide⟩ ⟨13, 2, 0, 808261, 424093, 3021, 16384⟩
    (by decide) selected_cut_31483

theorem selected_cut_31484 : selected 8 ⟨808311, by decide⟩
    (prefixPartial 13 424094) = some ⟨13, 2, 0, 808311, 424094, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_424094_808311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424094 ⟨808311, by decide⟩ :=
  accepted_of_selected 13 424094 ⟨808311, by decide⟩ ⟨13, 2, 0, 808311, 424094, 1833, 16384⟩
    (by decide) selected_cut_31484

theorem selected_cut_31485 : selected 8 ⟨808325, by decide⟩
    (prefixPartial 13 424095) = some ⟨13, 2, 0, 808325, 424095, 985, 16384⟩ := by
  decide +kernel

theorem context_13_424095_808325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424095 ⟨808325, by decide⟩ :=
  accepted_of_selected 13 424095 ⟨808325, by decide⟩ ⟨13, 2, 0, 808325, 424095, 985, 16384⟩
    (by decide) selected_cut_31485

theorem unmarked_context_12_106023_808326 : frontier 9 ⟨808326, by decide⟩
    (prefixCache 12 106023) (prefixPartial 12 106023) = false := by
  decide +kernel

theorem node_context_12_106023_808326 : EJMOriginalGlobalDAGData.nodes 9 ⟨808326, by decide⟩ =
    .split (coordinate 12) (![⟨808207, by decide⟩,⟨808261, by decide⟩,⟨808311, by decide⟩,⟨808325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106023_808326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106023 ⟨808326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106023
    ⟨808326, by decide⟩ (by decide) (![⟨808207, by decide⟩,⟨808261, by decide⟩,⟨808311, by decide⟩,⟨808325, by decide⟩]) unmarked_context_12_106023_808326 node_context_12_106023_808326
  intro a
  fin_cases a
  · exact context_13_424092_808207
  · exact context_13_424093_808261
  · exact context_13_424094_808311
  · exact context_13_424095_808325

theorem unmarked_context_11_26505_808327 : frontier 10 ⟨808327, by decide⟩
    (prefixCache 11 26505) (prefixPartial 11 26505) = false := by
  decide +kernel

theorem node_context_11_26505_808327 : EJMOriginalGlobalDAGData.nodes 10 ⟨808327, by decide⟩ =
    .split (coordinate 11) (![⟨807983, by decide⟩,⟨808104, by decide⟩,⟨808183, by decide⟩,⟨808326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_26505_808327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 26505 ⟨808327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 26505
    ⟨808327, by decide⟩ (by decide) (![⟨807983, by decide⟩,⟨808104, by decide⟩,⟨808183, by decide⟩,⟨808326, by decide⟩]) unmarked_context_11_26505_808327 node_context_11_26505_808327
  intro a
  fin_cases a
  · exact context_12_106020_807983
  · exact context_12_106021_808104
  · exact context_12_106022_808183
  · exact context_12_106023_808326

theorem selected_cut_31486 : selected 8 ⟨808342, by decide⟩
    (prefixPartial 13 424096) = some ⟨13, 2, 0, 808342, 424096, 817, 16384⟩ := by
  decide +kernel

theorem context_13_424096_808342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424096 ⟨808342, by decide⟩ :=
  accepted_of_selected 13 424096 ⟨808342, by decide⟩ ⟨13, 2, 0, 808342, 424096, 817, 16384⟩
    (by decide) selected_cut_31486

theorem selected_cut_31487 : selected 8 ⟨808371, by decide⟩
    (prefixPartial 13 424097) = some ⟨13, 2, 0, 808371, 424097, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_424097_808371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424097 ⟨808371, by decide⟩ :=
  accepted_of_selected 13 424097 ⟨808371, by decide⟩ ⟨13, 2, 0, 808371, 424097, 1901, 16384⟩
    (by decide) selected_cut_31487

theorem selected_cut_31488 : selected 8 ⟨808395, by decide⟩
    (prefixPartial 13 424098) = some ⟨13, 2, 0, 808395, 424098, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_424098_808395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424098 ⟨808395, by decide⟩ :=
  accepted_of_selected 13 424098 ⟨808395, by decide⟩ ⟨13, 2, 0, 808395, 424098, 1537, 16384⟩
    (by decide) selected_cut_31488

theorem selected_cut_31489 : selected 8 ⟨808406, by decide⟩
    (prefixPartial 13 424099) = some ⟨13, 2, 0, 808406, 424099, 813, 16384⟩ := by
  decide +kernel

theorem context_13_424099_808406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424099 ⟨808406, by decide⟩ :=
  accepted_of_selected 13 424099 ⟨808406, by decide⟩ ⟨13, 2, 0, 808406, 424099, 813, 16384⟩
    (by decide) selected_cut_31489

theorem unmarked_context_12_106024_808407 : frontier 9 ⟨808407, by decide⟩
    (prefixCache 12 106024) (prefixPartial 12 106024) = false := by
  decide +kernel

theorem node_context_12_106024_808407 : EJMOriginalGlobalDAGData.nodes 9 ⟨808407, by decide⟩ =
    .split (coordinate 12) (![⟨808342, by decide⟩,⟨808371, by decide⟩,⟨808395, by decide⟩,⟨808406, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_106024_808407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 106024 ⟨808407, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 106024
    ⟨808407, by decide⟩ (by decide) (![⟨808342, by decide⟩,⟨808371, by decide⟩,⟨808395, by decide⟩,⟨808406, by decide⟩]) unmarked_context_12_106024_808407 node_context_12_106024_808407
  intro a
  fin_cases a
  · exact context_13_424096_808342
  · exact context_13_424097_808371
  · exact context_13_424098_808395
  · exact context_13_424099_808406

theorem selected_cut_31490 : selected 8 ⟨808426, by decide⟩
    (prefixPartial 13 424100) = some ⟨13, 2, 0, 808426, 424100, 849, 16384⟩ := by
  decide +kernel

theorem context_13_424100_808426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424100 ⟨808426, by decide⟩ :=
  accepted_of_selected 13 424100 ⟨808426, by decide⟩ ⟨13, 2, 0, 808426, 424100, 849, 16384⟩
    (by decide) selected_cut_31490

theorem selected_cut_31491 : selected 8 ⟨808471, by decide⟩
    (prefixPartial 13 424101) = some ⟨13, 2, 0, 808471, 424101, 2361, 16384⟩ := by
  decide +kernel

theorem context_13_424101_808471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 424101 ⟨808471, by decide⟩ :=
  accepted_of_selected 13 424101 ⟨808471, by decide⟩ ⟨13, 2, 0, 808471, 424101, 2361, 16384⟩
    (by decide) selected_cut_31491

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
