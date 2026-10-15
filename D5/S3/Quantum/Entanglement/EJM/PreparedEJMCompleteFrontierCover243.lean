/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover242
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_23331 : selected 8 ⟨590679, by decide⟩
    (prefixPartial 13 305352) = some ⟨13, 2, 0, 590679, 305352, 585, 16384⟩ := by
  decide +kernel

theorem context_13_305352_590679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305352 ⟨590679, by decide⟩ :=
  accepted_of_selected 13 305352 ⟨590679, by decide⟩ ⟨13, 2, 0, 590679, 305352, 585, 16384⟩
    (by decide) selected_cut_23331

theorem selected_cut_23332 : selected 8 ⟨590709, by decide⟩
    (prefixPartial 13 305353) = some ⟨13, 2, 0, 590709, 305353, 2093, 16384⟩ := by
  decide +kernel

theorem context_13_305353_590709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305353 ⟨590709, by decide⟩ :=
  accepted_of_selected 13 305353 ⟨590709, by decide⟩ ⟨13, 2, 0, 590709, 305353, 2093, 16384⟩
    (by decide) selected_cut_23332

theorem selected_cut_23333 : selected 8 ⟨590727, by decide⟩
    (prefixPartial 13 305354) = some ⟨13, 2, 0, 590727, 305354, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_305354_590727 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305354 ⟨590727, by decide⟩ :=
  accepted_of_selected 13 305354 ⟨590727, by decide⟩ ⟨13, 2, 0, 590727, 305354, 1245, 16384⟩
    (by decide) selected_cut_23333

theorem selected_cut_23334 : selected 8 ⟨590733, by decide⟩
    (prefixPartial 13 305355) = some ⟨13, 2, 0, 590733, 305355, 893, 16384⟩ := by
  decide +kernel

theorem context_13_305355_590733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305355 ⟨590733, by decide⟩ :=
  accepted_of_selected 13 305355 ⟨590733, by decide⟩ ⟨13, 2, 0, 590733, 305355, 893, 16384⟩
    (by decide) selected_cut_23334

theorem unmarked_context_12_76338_590734 : frontier 9 ⟨590734, by decide⟩
    (prefixCache 12 76338) (prefixPartial 12 76338) = false := by
  decide +kernel

theorem node_context_12_76338_590734 : EJMOriginalGlobalDAGData.nodes 9 ⟨590734, by decide⟩ =
    .split (coordinate 12) (![⟨590679, by decide⟩,⟨590709, by decide⟩,⟨590727, by decide⟩,⟨590733, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76338_590734 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76338 ⟨590734, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76338
    ⟨590734, by decide⟩ (by decide) (![⟨590679, by decide⟩,⟨590709, by decide⟩,⟨590727, by decide⟩,⟨590733, by decide⟩]) unmarked_context_12_76338_590734 node_context_12_76338_590734
  intro a
  fin_cases a
  · exact context_13_305352_590679
  · exact context_13_305353_590709
  · exact context_13_305354_590727
  · exact context_13_305355_590733

theorem selected_cut_23335 : selected 8 ⟨590748, by decide⟩
    (prefixPartial 13 305356) = some ⟨13, 2, 0, 590748, 305356, 665, 16384⟩ := by
  decide +kernel

theorem context_13_305356_590748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305356 ⟨590748, by decide⟩ :=
  accepted_of_selected 13 305356 ⟨590748, by decide⟩ ⟨13, 2, 0, 590748, 305356, 665, 16384⟩
    (by decide) selected_cut_23335

theorem selected_cut_23336 : selected 8 ⟨590788, by decide⟩
    (prefixPartial 13 305357) = some ⟨13, 2, 0, 590788, 305357, 2425, 16384⟩ := by
  decide +kernel

theorem context_13_305357_590788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305357 ⟨590788, by decide⟩ :=
  accepted_of_selected 13 305357 ⟨590788, by decide⟩ ⟨13, 2, 0, 590788, 305357, 2425, 16384⟩
    (by decide) selected_cut_23336

theorem selected_cut_23337 : selected 8 ⟨590812, by decide⟩
    (prefixPartial 13 305358) = some ⟨13, 2, 0, 590812, 305358, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_305358_590812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305358 ⟨590812, by decide⟩ :=
  accepted_of_selected 13 305358 ⟨590812, by decide⟩ ⟨13, 2, 0, 590812, 305358, 1381, 16384⟩
    (by decide) selected_cut_23337

theorem selected_cut_23338 : selected 8 ⟨590822, by decide⟩
    (prefixPartial 13 305359) = some ⟨13, 2, 0, 590822, 305359, 865, 16384⟩ := by
  decide +kernel

theorem context_13_305359_590822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305359 ⟨590822, by decide⟩ :=
  accepted_of_selected 13 305359 ⟨590822, by decide⟩ ⟨13, 2, 0, 590822, 305359, 865, 16384⟩
    (by decide) selected_cut_23338

theorem unmarked_context_12_76339_590823 : frontier 9 ⟨590823, by decide⟩
    (prefixCache 12 76339) (prefixPartial 12 76339) = false := by
  decide +kernel

theorem node_context_12_76339_590823 : EJMOriginalGlobalDAGData.nodes 9 ⟨590823, by decide⟩ =
    .split (coordinate 12) (![⟨590748, by decide⟩,⟨590788, by decide⟩,⟨590812, by decide⟩,⟨590822, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76339_590823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76339 ⟨590823, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76339
    ⟨590823, by decide⟩ (by decide) (![⟨590748, by decide⟩,⟨590788, by decide⟩,⟨590812, by decide⟩,⟨590822, by decide⟩]) unmarked_context_12_76339_590823 node_context_12_76339_590823
  intro a
  fin_cases a
  · exact context_13_305356_590748
  · exact context_13_305357_590788
  · exact context_13_305358_590812
  · exact context_13_305359_590822

theorem unmarked_context_11_19084_590824 : frontier 10 ⟨590824, by decide⟩
    (prefixCache 11 19084) (prefixPartial 11 19084) = false := by
  decide +kernel

theorem node_context_11_19084_590824 : EJMOriginalGlobalDAGData.nodes 10 ⟨590824, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨590668, by decide⟩,⟨590734, by decide⟩,⟨590823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19084_590824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19084 ⟨590824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19084
    ⟨590824, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨590668, by decide⟩,⟨590734, by decide⟩,⟨590823, by decide⟩]) unmarked_context_11_19084_590824 node_context_11_19084_590824
  intro a
  fin_cases a
  · exact context_12_76336_445562
  · exact context_12_76337_590668
  · exact context_12_76338_590734
  · exact context_12_76339_590823

theorem selected_cut_23339 : selected 8 ⟨590849, by decide⟩
    (prefixPartial 13 305360) = some ⟨13, 2, 0, 590849, 305360, 821, 16384⟩ := by
  decide +kernel

theorem context_13_305360_590849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305360 ⟨590849, by decide⟩ :=
  accepted_of_selected 13 305360 ⟨590849, by decide⟩ ⟨13, 2, 0, 590849, 305360, 821, 16384⟩
    (by decide) selected_cut_23339

theorem selected_cut_23340 : selected 8 ⟨590908, by decide⟩
    (prefixPartial 13 305361) = some ⟨13, 2, 0, 590908, 305361, 3317, 16384⟩ := by
  decide +kernel

theorem context_13_305361_590908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305361 ⟨590908, by decide⟩ :=
  accepted_of_selected 13 305361 ⟨590908, by decide⟩ ⟨13, 2, 0, 590908, 305361, 3317, 16384⟩
    (by decide) selected_cut_23340

theorem selected_cut_23341 : selected 8 ⟨590932, by decide⟩
    (prefixPartial 13 305362) = some ⟨13, 2, 0, 590932, 305362, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_305362_590932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305362 ⟨590932, by decide⟩ :=
  accepted_of_selected 13 305362 ⟨590932, by decide⟩ ⟨13, 2, 0, 590932, 305362, 1869, 16384⟩
    (by decide) selected_cut_23341

theorem selected_cut_23342 : selected 8 ⟨590953, by decide⟩
    (prefixPartial 13 305363) = some ⟨13, 2, 0, 590953, 305363, 1213, 16384⟩ := by
  decide +kernel

theorem context_13_305363_590953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305363 ⟨590953, by decide⟩ :=
  accepted_of_selected 13 305363 ⟨590953, by decide⟩ ⟨13, 2, 0, 590953, 305363, 1213, 16384⟩
    (by decide) selected_cut_23342

theorem unmarked_context_12_76340_590954 : frontier 9 ⟨590954, by decide⟩
    (prefixCache 12 76340) (prefixPartial 12 76340) = false := by
  decide +kernel

theorem node_context_12_76340_590954 : EJMOriginalGlobalDAGData.nodes 9 ⟨590954, by decide⟩ =
    .split (coordinate 12) (![⟨590849, by decide⟩,⟨590908, by decide⟩,⟨590932, by decide⟩,⟨590953, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76340_590954 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76340 ⟨590954, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76340
    ⟨590954, by decide⟩ (by decide) (![⟨590849, by decide⟩,⟨590908, by decide⟩,⟨590932, by decide⟩,⟨590953, by decide⟩]) unmarked_context_12_76340_590954 node_context_12_76340_590954
  intro a
  fin_cases a
  · exact context_13_305360_590849
  · exact context_13_305361_590908
  · exact context_13_305362_590932
  · exact context_13_305363_590953

theorem selected_cut_23343 : selected 8 ⟨590974, by decide⟩
    (prefixPartial 13 305364) = some ⟨13, 2, 0, 590974, 305364, 609, 16384⟩ := by
  decide +kernel

theorem context_13_305364_590974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305364 ⟨590974, by decide⟩ :=
  accepted_of_selected 13 305364 ⟨590974, by decide⟩ ⟨13, 2, 0, 590974, 305364, 609, 16384⟩
    (by decide) selected_cut_23343

theorem selected_cut_23344 : selected 8 ⟨591000, by decide⟩
    (prefixPartial 13 305365) = some ⟨13, 2, 0, 591000, 305365, 2169, 16384⟩ := by
  decide +kernel

theorem context_13_305365_591000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305365 ⟨591000, by decide⟩ :=
  accepted_of_selected 13 305365 ⟨591000, by decide⟩ ⟨13, 2, 0, 591000, 305365, 2169, 16384⟩
    (by decide) selected_cut_23344

theorem selected_cut_23345 : selected 8 ⟨591014, by decide⟩
    (prefixPartial 13 305366) = some ⟨13, 2, 0, 591014, 305366, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_305366_591014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305366 ⟨591014, by decide⟩ :=
  accepted_of_selected 13 305366 ⟨591014, by decide⟩ ⟨13, 2, 0, 591014, 305366, 1205, 16384⟩
    (by decide) selected_cut_23345

theorem selected_cut_23346 : selected 8 ⟨591025, by decide⟩
    (prefixPartial 13 305367) = some ⟨13, 2, 0, 591025, 305367, 1097, 16384⟩ := by
  decide +kernel

theorem context_13_305367_591025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305367 ⟨591025, by decide⟩ :=
  accepted_of_selected 13 305367 ⟨591025, by decide⟩ ⟨13, 2, 0, 591025, 305367, 1097, 16384⟩
    (by decide) selected_cut_23346

theorem unmarked_context_12_76341_591026 : frontier 9 ⟨591026, by decide⟩
    (prefixCache 12 76341) (prefixPartial 12 76341) = false := by
  decide +kernel

theorem node_context_12_76341_591026 : EJMOriginalGlobalDAGData.nodes 9 ⟨591026, by decide⟩ =
    .split (coordinate 12) (![⟨590974, by decide⟩,⟨591000, by decide⟩,⟨591014, by decide⟩,⟨591025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76341_591026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76341 ⟨591026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76341
    ⟨591026, by decide⟩ (by decide) (![⟨590974, by decide⟩,⟨591000, by decide⟩,⟨591014, by decide⟩,⟨591025, by decide⟩]) unmarked_context_12_76341_591026 node_context_12_76341_591026
  intro a
  fin_cases a
  · exact context_13_305364_590974
  · exact context_13_305365_591000
  · exact context_13_305366_591014
  · exact context_13_305367_591025

theorem selected_cut_23347 : selected 8 ⟨591039, by decide⟩
    (prefixPartial 13 305368) = some ⟨13, 2, 0, 591039, 305368, 461, 16384⟩ := by
  decide +kernel

theorem context_13_305368_591039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305368 ⟨591039, by decide⟩ :=
  accepted_of_selected 13 305368 ⟨591039, by decide⟩ ⟨13, 2, 0, 591039, 305368, 461, 16384⟩
    (by decide) selected_cut_23347

theorem selected_cut_23348 : selected 8 ⟨591063, by decide⟩
    (prefixPartial 13 305369) = some ⟨13, 2, 0, 591063, 305369, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_305369_591063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305369 ⟨591063, by decide⟩ :=
  accepted_of_selected 13 305369 ⟨591063, by decide⟩ ⟨13, 2, 0, 591063, 305369, 2197, 16384⟩
    (by decide) selected_cut_23348

theorem selected_cut_23349 : selected 8 ⟨591084, by decide⟩
    (prefixPartial 13 305370) = some ⟨13, 2, 0, 591084, 305370, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_305370_591084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305370 ⟨591084, by decide⟩ :=
  accepted_of_selected 13 305370 ⟨591084, by decide⟩ ⟨13, 2, 0, 591084, 305370, 1321, 16384⟩
    (by decide) selected_cut_23349

theorem selected_cut_23350 : selected 8 ⟨591091, by decide⟩
    (prefixPartial 13 305371) = some ⟨13, 2, 0, 591091, 305371, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_305371_591091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305371 ⟨591091, by decide⟩ :=
  accepted_of_selected 13 305371 ⟨591091, by decide⟩ ⟨13, 2, 0, 591091, 305371, 1009, 16384⟩
    (by decide) selected_cut_23350

theorem unmarked_context_12_76342_591092 : frontier 9 ⟨591092, by decide⟩
    (prefixCache 12 76342) (prefixPartial 12 76342) = false := by
  decide +kernel

theorem node_context_12_76342_591092 : EJMOriginalGlobalDAGData.nodes 9 ⟨591092, by decide⟩ =
    .split (coordinate 12) (![⟨591039, by decide⟩,⟨591063, by decide⟩,⟨591084, by decide⟩,⟨591091, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76342_591092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76342 ⟨591092, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76342
    ⟨591092, by decide⟩ (by decide) (![⟨591039, by decide⟩,⟨591063, by decide⟩,⟨591084, by decide⟩,⟨591091, by decide⟩]) unmarked_context_12_76342_591092 node_context_12_76342_591092
  intro a
  fin_cases a
  · exact context_13_305368_591039
  · exact context_13_305369_591063
  · exact context_13_305370_591084
  · exact context_13_305371_591091

theorem selected_cut_23351 : selected 8 ⟨591106, by decide⟩
    (prefixPartial 13 305372) = some ⟨13, 2, 0, 591106, 305372, 517, 16384⟩ := by
  decide +kernel

theorem context_13_305372_591106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305372 ⟨591106, by decide⟩ :=
  accepted_of_selected 13 305372 ⟨591106, by decide⟩ ⟨13, 2, 0, 591106, 305372, 517, 16384⟩
    (by decide) selected_cut_23351

theorem selected_cut_23352 : selected 8 ⟨591140, by decide⟩
    (prefixPartial 13 305373) = some ⟨13, 2, 0, 591140, 305373, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_305373_591140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305373 ⟨591140, by decide⟩ :=
  accepted_of_selected 13 305373 ⟨591140, by decide⟩ ⟨13, 2, 0, 591140, 305373, 2301, 16384⟩
    (by decide) selected_cut_23352

theorem selected_cut_23353 : selected 8 ⟨591163, by decide⟩
    (prefixPartial 13 305374) = some ⟨13, 2, 0, 591163, 305374, 1469, 16384⟩ := by
  decide +kernel

theorem context_13_305374_591163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305374 ⟨591163, by decide⟩ :=
  accepted_of_selected 13 305374 ⟨591163, by decide⟩ ⟨13, 2, 0, 591163, 305374, 1469, 16384⟩
    (by decide) selected_cut_23353

theorem selected_cut_23354 : selected 8 ⟨591172, by decide⟩
    (prefixPartial 13 305375) = some ⟨13, 2, 0, 591172, 305375, 965, 16384⟩ := by
  decide +kernel

theorem context_13_305375_591172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305375 ⟨591172, by decide⟩ :=
  accepted_of_selected 13 305375 ⟨591172, by decide⟩ ⟨13, 2, 0, 591172, 305375, 965, 16384⟩
    (by decide) selected_cut_23354

theorem unmarked_context_12_76343_591173 : frontier 9 ⟨591173, by decide⟩
    (prefixCache 12 76343) (prefixPartial 12 76343) = false := by
  decide +kernel

theorem node_context_12_76343_591173 : EJMOriginalGlobalDAGData.nodes 9 ⟨591173, by decide⟩ =
    .split (coordinate 12) (![⟨591106, by decide⟩,⟨591140, by decide⟩,⟨591163, by decide⟩,⟨591172, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76343_591173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76343 ⟨591173, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76343
    ⟨591173, by decide⟩ (by decide) (![⟨591106, by decide⟩,⟨591140, by decide⟩,⟨591163, by decide⟩,⟨591172, by decide⟩]) unmarked_context_12_76343_591173 node_context_12_76343_591173
  intro a
  fin_cases a
  · exact context_13_305372_591106
  · exact context_13_305373_591140
  · exact context_13_305374_591163
  · exact context_13_305375_591172

theorem unmarked_context_11_19085_591174 : frontier 10 ⟨591174, by decide⟩
    (prefixCache 11 19085) (prefixPartial 11 19085) = false := by
  decide +kernel

theorem node_context_11_19085_591174 : EJMOriginalGlobalDAGData.nodes 10 ⟨591174, by decide⟩ =
    .split (coordinate 11) (![⟨590954, by decide⟩,⟨591026, by decide⟩,⟨591092, by decide⟩,⟨591173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19085_591174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19085 ⟨591174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19085
    ⟨591174, by decide⟩ (by decide) (![⟨590954, by decide⟩,⟨591026, by decide⟩,⟨591092, by decide⟩,⟨591173, by decide⟩]) unmarked_context_11_19085_591174 node_context_11_19085_591174
  intro a
  fin_cases a
  · exact context_12_76340_590954
  · exact context_12_76341_591026
  · exact context_12_76342_591092
  · exact context_12_76343_591173

theorem selected_cut_23355 : selected 9 ⟨591270, by decide⟩
    (prefixPartial 12 76344) = some ⟨12, 2, 0, 591270, 76344, 3437, 65536⟩ := by
  decide +kernel

theorem context_12_76344_591270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76344 ⟨591270, by decide⟩ :=
  accepted_of_selected 12 76344 ⟨591270, by decide⟩ ⟨12, 2, 0, 591270, 76344, 3437, 65536⟩
    (by decide) selected_cut_23355

theorem selected_cut_23356 : selected 8 ⟨591277, by decide⟩
    (prefixPartial 13 305380) = some ⟨13, 2, 0, 591277, 305380, 361, 16384⟩ := by
  decide +kernel

theorem context_13_305380_591277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305380 ⟨591277, by decide⟩ :=
  accepted_of_selected 13 305380 ⟨591277, by decide⟩ ⟨13, 2, 0, 591277, 305380, 361, 16384⟩
    (by decide) selected_cut_23356

theorem selected_cut_23357 : selected 8 ⟨591303, by decide⟩
    (prefixPartial 13 305381) = some ⟨13, 2, 0, 591303, 305381, 1941, 16384⟩ := by
  decide +kernel

theorem context_13_305381_591303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305381 ⟨591303, by decide⟩ :=
  accepted_of_selected 13 305381 ⟨591303, by decide⟩ ⟨13, 2, 0, 591303, 305381, 1941, 16384⟩
    (by decide) selected_cut_23357

theorem selected_cut_23358 : selected 8 ⟨591323, by decide⟩
    (prefixPartial 13 305382) = some ⟨13, 2, 0, 591323, 305382, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_305382_591323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305382 ⟨591323, by decide⟩ :=
  accepted_of_selected 13 305382 ⟨591323, by decide⟩ ⟨13, 2, 0, 591323, 305382, 1117, 16384⟩
    (by decide) selected_cut_23358

theorem selected_cut_23359 : selected 8 ⟨591333, by decide⟩
    (prefixPartial 13 305383) = some ⟨13, 2, 0, 591333, 305383, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_305383_591333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305383 ⟨591333, by decide⟩ :=
  accepted_of_selected 13 305383 ⟨591333, by decide⟩ ⟨13, 2, 0, 591333, 305383, 1041, 16384⟩
    (by decide) selected_cut_23359

theorem unmarked_context_12_76345_591334 : frontier 9 ⟨591334, by decide⟩
    (prefixCache 12 76345) (prefixPartial 12 76345) = false := by
  decide +kernel

theorem node_context_12_76345_591334 : EJMOriginalGlobalDAGData.nodes 9 ⟨591334, by decide⟩ =
    .split (coordinate 12) (![⟨591277, by decide⟩,⟨591303, by decide⟩,⟨591323, by decide⟩,⟨591333, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76345_591334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76345 ⟨591334, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76345
    ⟨591334, by decide⟩ (by decide) (![⟨591277, by decide⟩,⟨591303, by decide⟩,⟨591323, by decide⟩,⟨591333, by decide⟩]) unmarked_context_12_76345_591334 node_context_12_76345_591334
  intro a
  fin_cases a
  · exact context_13_305380_591277
  · exact context_13_305381_591303
  · exact context_13_305382_591323
  · exact context_13_305383_591333

theorem selected_cut_23360 : selected 9 ⟨591450, by decide⟩
    (prefixPartial 12 76346) = some ⟨12, 2, 0, 591450, 76346, 3713, 65536⟩ := by
  decide +kernel

theorem context_12_76346_591450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76346 ⟨591450, by decide⟩ :=
  accepted_of_selected 12 76346 ⟨591450, by decide⟩ ⟨12, 2, 0, 591450, 76346, 3713, 65536⟩
    (by decide) selected_cut_23360

theorem selected_cut_23361 : selected 8 ⟨591454, by decide⟩
    (prefixPartial 13 305388) = some ⟨13, 2, 0, 591454, 305388, 189, 16384⟩ := by
  decide +kernel

theorem context_13_305388_591454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305388 ⟨591454, by decide⟩ :=
  accepted_of_selected 13 305388 ⟨591454, by decide⟩ ⟨13, 2, 0, 591454, 305388, 189, 16384⟩
    (by decide) selected_cut_23361

theorem selected_cut_23362 : selected 8 ⟨591486, by decide⟩
    (prefixPartial 13 305389) = some ⟨13, 2, 0, 591486, 305389, 2109, 16384⟩ := by
  decide +kernel

theorem context_13_305389_591486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305389 ⟨591486, by decide⟩ :=
  accepted_of_selected 13 305389 ⟨591486, by decide⟩ ⟨13, 2, 0, 591486, 305389, 2109, 16384⟩
    (by decide) selected_cut_23362

theorem selected_cut_23363 : selected 8 ⟨591507, by decide⟩
    (prefixPartial 13 305390) = some ⟨13, 2, 0, 591507, 305390, 1161, 16384⟩ := by
  decide +kernel

theorem context_13_305390_591507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305390 ⟨591507, by decide⟩ :=
  accepted_of_selected 13 305390 ⟨591507, by decide⟩ ⟨13, 2, 0, 591507, 305390, 1161, 16384⟩
    (by decide) selected_cut_23363

theorem selected_cut_23364 : selected 8 ⟨591518, by decide⟩
    (prefixPartial 13 305391) = some ⟨13, 2, 0, 591518, 305391, 749, 16384⟩ := by
  decide +kernel

theorem context_13_305391_591518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305391 ⟨591518, by decide⟩ :=
  accepted_of_selected 13 305391 ⟨591518, by decide⟩ ⟨13, 2, 0, 591518, 305391, 749, 16384⟩
    (by decide) selected_cut_23364

theorem unmarked_context_12_76347_591519 : frontier 9 ⟨591519, by decide⟩
    (prefixCache 12 76347) (prefixPartial 12 76347) = false := by
  decide +kernel

theorem node_context_12_76347_591519 : EJMOriginalGlobalDAGData.nodes 9 ⟨591519, by decide⟩ =
    .split (coordinate 12) (![⟨591454, by decide⟩,⟨591486, by decide⟩,⟨591507, by decide⟩,⟨591518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76347_591519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76347 ⟨591519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76347
    ⟨591519, by decide⟩ (by decide) (![⟨591454, by decide⟩,⟨591486, by decide⟩,⟨591507, by decide⟩,⟨591518, by decide⟩]) unmarked_context_12_76347_591519 node_context_12_76347_591519
  intro a
  fin_cases a
  · exact context_13_305388_591454
  · exact context_13_305389_591486
  · exact context_13_305390_591507
  · exact context_13_305391_591518

theorem unmarked_context_11_19086_591520 : frontier 10 ⟨591520, by decide⟩
    (prefixCache 11 19086) (prefixPartial 11 19086) = false := by
  decide +kernel

theorem node_context_11_19086_591520 : EJMOriginalGlobalDAGData.nodes 10 ⟨591520, by decide⟩ =
    .split (coordinate 11) (![⟨591270, by decide⟩,⟨591334, by decide⟩,⟨591450, by decide⟩,⟨591519, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19086_591520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19086 ⟨591520, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19086
    ⟨591520, by decide⟩ (by decide) (![⟨591270, by decide⟩,⟨591334, by decide⟩,⟨591450, by decide⟩,⟨591519, by decide⟩]) unmarked_context_11_19086_591520 node_context_11_19086_591520
  intro a
  fin_cases a
  · exact context_12_76344_591270
  · exact context_12_76345_591334
  · exact context_12_76346_591450
  · exact context_12_76347_591519

theorem selected_cut_23365 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 76348) = some ⟨12, 1, 0, 445562, 76348, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76348_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76348 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 76348 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 76348, 1, 65536⟩
    (by decide) selected_cut_23365

theorem selected_cut_23366 : selected 8 ⟨591524, by decide⟩
    (prefixPartial 13 305396) = some ⟨13, 2, 0, 591524, 305396, 181, 16384⟩ := by
  decide +kernel

theorem context_13_305396_591524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305396 ⟨591524, by decide⟩ :=
  accepted_of_selected 13 305396 ⟨591524, by decide⟩ ⟨13, 2, 0, 591524, 305396, 181, 16384⟩
    (by decide) selected_cut_23366

theorem selected_cut_23367 : selected 8 ⟨591561, by decide⟩
    (prefixPartial 13 305397) = some ⟨13, 2, 0, 591561, 305397, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_305397_591561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305397 ⟨591561, by decide⟩ :=
  accepted_of_selected 13 305397 ⟨591561, by decide⟩ ⟨13, 2, 0, 591561, 305397, 2613, 16384⟩
    (by decide) selected_cut_23367

theorem selected_cut_23368 : selected 8 ⟨591575, by decide⟩
    (prefixPartial 13 305398) = some ⟨13, 2, 0, 591575, 305398, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_305398_591575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305398 ⟨591575, by decide⟩ :=
  accepted_of_selected 13 305398 ⟨591575, by decide⟩ ⟨13, 2, 0, 591575, 305398, 1221, 16384⟩
    (by decide) selected_cut_23368

theorem selected_cut_23369 : selected 8 ⟨591582, by decide⟩
    (prefixPartial 13 305399) = some ⟨13, 2, 0, 591582, 305399, 989, 16384⟩ := by
  decide +kernel

theorem context_13_305399_591582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305399 ⟨591582, by decide⟩ :=
  accepted_of_selected 13 305399 ⟨591582, by decide⟩ ⟨13, 2, 0, 591582, 305399, 989, 16384⟩
    (by decide) selected_cut_23369

theorem unmarked_context_12_76349_591583 : frontier 9 ⟨591583, by decide⟩
    (prefixCache 12 76349) (prefixPartial 12 76349) = false := by
  decide +kernel

theorem node_context_12_76349_591583 : EJMOriginalGlobalDAGData.nodes 9 ⟨591583, by decide⟩ =
    .split (coordinate 12) (![⟨591524, by decide⟩,⟨591561, by decide⟩,⟨591575, by decide⟩,⟨591582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76349_591583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76349 ⟨591583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76349
    ⟨591583, by decide⟩ (by decide) (![⟨591524, by decide⟩,⟨591561, by decide⟩,⟨591575, by decide⟩,⟨591582, by decide⟩]) unmarked_context_12_76349_591583 node_context_12_76349_591583
  intro a
  fin_cases a
  · exact context_13_305396_591524
  · exact context_13_305397_591561
  · exact context_13_305398_591575
  · exact context_13_305399_591582

theorem selected_cut_23370 : selected 8 ⟨591586, by decide⟩
    (prefixPartial 13 305400) = some ⟨13, 2, 0, 591586, 305400, 105, 16384⟩ := by
  decide +kernel

theorem context_13_305400_591586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305400 ⟨591586, by decide⟩ :=
  accepted_of_selected 13 305400 ⟨591586, by decide⟩ ⟨13, 2, 0, 591586, 305400, 105, 16384⟩
    (by decide) selected_cut_23370

theorem selected_cut_23371 : selected 8 ⟨591617, by decide⟩
    (prefixPartial 13 305401) = some ⟨13, 2, 0, 591617, 305401, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_305401_591617 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305401 ⟨591617, by decide⟩ :=
  accepted_of_selected 13 305401 ⟨591617, by decide⟩ ⟨13, 2, 0, 591617, 305401, 2505, 16384⟩
    (by decide) selected_cut_23371

theorem selected_cut_23372 : selected 8 ⟨591636, by decide⟩
    (prefixPartial 13 305402) = some ⟨13, 2, 0, 591636, 305402, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_305402_591636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305402 ⟨591636, by decide⟩ :=
  accepted_of_selected 13 305402 ⟨591636, by decide⟩ ⟨13, 2, 0, 591636, 305402, 1277, 16384⟩
    (by decide) selected_cut_23372

theorem selected_cut_23373 : selected 8 ⟨591644, by decide⟩
    (prefixPartial 13 305403) = some ⟨13, 2, 0, 591644, 305403, 917, 16384⟩ := by
  decide +kernel

theorem context_13_305403_591644 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305403 ⟨591644, by decide⟩ :=
  accepted_of_selected 13 305403 ⟨591644, by decide⟩ ⟨13, 2, 0, 591644, 305403, 917, 16384⟩
    (by decide) selected_cut_23373

theorem unmarked_context_12_76350_591645 : frontier 9 ⟨591645, by decide⟩
    (prefixCache 12 76350) (prefixPartial 12 76350) = false := by
  decide +kernel

theorem node_context_12_76350_591645 : EJMOriginalGlobalDAGData.nodes 9 ⟨591645, by decide⟩ =
    .split (coordinate 12) (![⟨591586, by decide⟩,⟨591617, by decide⟩,⟨591636, by decide⟩,⟨591644, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76350_591645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76350 ⟨591645, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76350
    ⟨591645, by decide⟩ (by decide) (![⟨591586, by decide⟩,⟨591617, by decide⟩,⟨591636, by decide⟩,⟨591644, by decide⟩]) unmarked_context_12_76350_591645 node_context_12_76350_591645
  intro a
  fin_cases a
  · exact context_13_305400_591586
  · exact context_13_305401_591617
  · exact context_13_305402_591636
  · exact context_13_305403_591644

theorem selected_cut_23374 : selected 8 ⟨591648, by decide⟩
    (prefixPartial 13 305404) = some ⟨13, 2, 0, 591648, 305404, 69, 16384⟩ := by
  decide +kernel

theorem context_13_305404_591648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305404 ⟨591648, by decide⟩ :=
  accepted_of_selected 13 305404 ⟨591648, by decide⟩ ⟨13, 2, 0, 591648, 305404, 69, 16384⟩
    (by decide) selected_cut_23374

theorem selected_cut_23375 : selected 8 ⟨591685, by decide⟩
    (prefixPartial 13 305405) = some ⟨13, 2, 0, 591685, 305405, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_305405_591685 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305405 ⟨591685, by decide⟩ :=
  accepted_of_selected 13 305405 ⟨591685, by decide⟩ ⟨13, 2, 0, 591685, 305405, 2577, 16384⟩
    (by decide) selected_cut_23375

theorem selected_cut_23376 : selected 8 ⟨591702, by decide⟩
    (prefixPartial 13 305406) = some ⟨13, 2, 0, 591702, 305406, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_305406_591702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305406 ⟨591702, by decide⟩ :=
  accepted_of_selected 13 305406 ⟨591702, by decide⟩ ⟨13, 2, 0, 591702, 305406, 1461, 16384⟩
    (by decide) selected_cut_23376

theorem selected_cut_23377 : selected 8 ⟨591709, by decide⟩
    (prefixPartial 13 305407) = some ⟨13, 2, 0, 591709, 305407, 877, 16384⟩ := by
  decide +kernel

theorem context_13_305407_591709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305407 ⟨591709, by decide⟩ :=
  accepted_of_selected 13 305407 ⟨591709, by decide⟩ ⟨13, 2, 0, 591709, 305407, 877, 16384⟩
    (by decide) selected_cut_23377

theorem unmarked_context_12_76351_591710 : frontier 9 ⟨591710, by decide⟩
    (prefixCache 12 76351) (prefixPartial 12 76351) = false := by
  decide +kernel

theorem node_context_12_76351_591710 : EJMOriginalGlobalDAGData.nodes 9 ⟨591710, by decide⟩ =
    .split (coordinate 12) (![⟨591648, by decide⟩,⟨591685, by decide⟩,⟨591702, by decide⟩,⟨591709, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76351_591710 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76351 ⟨591710, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76351
    ⟨591710, by decide⟩ (by decide) (![⟨591648, by decide⟩,⟨591685, by decide⟩,⟨591702, by decide⟩,⟨591709, by decide⟩]) unmarked_context_12_76351_591710 node_context_12_76351_591710
  intro a
  fin_cases a
  · exact context_13_305404_591648
  · exact context_13_305405_591685
  · exact context_13_305406_591702
  · exact context_13_305407_591709

theorem unmarked_context_11_19087_591711 : frontier 10 ⟨591711, by decide⟩
    (prefixCache 11 19087) (prefixPartial 11 19087) = false := by
  decide +kernel

theorem node_context_11_19087_591711 : EJMOriginalGlobalDAGData.nodes 10 ⟨591711, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨591583, by decide⟩,⟨591645, by decide⟩,⟨591710, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19087_591711 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19087 ⟨591711, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19087
    ⟨591711, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨591583, by decide⟩,⟨591645, by decide⟩,⟨591710, by decide⟩]) unmarked_context_11_19087_591711 node_context_11_19087_591711
  intro a
  fin_cases a
  · exact context_12_76348_445562
  · exact context_12_76349_591583
  · exact context_12_76350_591645
  · exact context_12_76351_591710

theorem unmarked_context_10_4771_591712 : frontier 11 ⟨591712, by decide⟩
    (prefixCache 10 4771) (prefixPartial 10 4771) = false := by
  decide +kernel

theorem node_context_10_4771_591712 : EJMOriginalGlobalDAGData.nodes 11 ⟨591712, by decide⟩ =
    .split (coordinate 10) (![⟨590824, by decide⟩,⟨591174, by decide⟩,⟨591520, by decide⟩,⟨591711, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4771_591712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4771 ⟨591712, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4771
    ⟨591712, by decide⟩ (by decide) (![⟨590824, by decide⟩,⟨591174, by decide⟩,⟨591520, by decide⟩,⟨591711, by decide⟩]) unmarked_context_10_4771_591712 node_context_10_4771_591712
  intro a
  fin_cases a
  · exact context_11_19084_590824
  · exact context_11_19085_591174
  · exact context_11_19086_591520
  · exact context_11_19087_591711

theorem unmarked_context_9_1192_591713 : frontier 12 ⟨591713, by decide⟩
    (prefixCache 9 1192) (prefixPartial 9 1192) = false := by
  decide +kernel

theorem node_context_9_1192_591713 : EJMOriginalGlobalDAGData.nodes 12 ⟨591713, by decide⟩ =
    .split (coordinate 9) (![⟨587825, by decide⟩,⟨589650, by decide⟩,⟨590585, by decide⟩,⟨591712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1192_591713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1192 ⟨591713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1192
    ⟨591713, by decide⟩ (by decide) (![⟨587825, by decide⟩,⟨589650, by decide⟩,⟨590585, by decide⟩,⟨591712, by decide⟩]) unmarked_context_9_1192_591713 node_context_9_1192_591713
  intro a
  fin_cases a
  · exact context_10_4768_587825
  · exact context_10_4769_589650
  · exact context_10_4770_590585
  · exact context_10_4771_591712

theorem selected_cut_23378 : selected 9 ⟨591763, by decide⟩
    (prefixPartial 12 76352) = some ⟨12, 2, 0, 591763, 76352, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_76352_591763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76352 ⟨591763, by decide⟩ :=
  accepted_of_selected 12 76352 ⟨591763, by decide⟩ ⟨12, 2, 0, 591763, 76352, 3857, 65536⟩
    (by decide) selected_cut_23378

theorem selected_cut_23379 : selected 9 ⟨591809, by decide⟩
    (prefixPartial 12 76353) = some ⟨12, 2, 0, 591809, 76353, 3989, 65536⟩ := by
  decide +kernel

theorem context_12_76353_591809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76353 ⟨591809, by decide⟩ :=
  accepted_of_selected 12 76353 ⟨591809, by decide⟩ ⟨12, 2, 0, 591809, 76353, 3989, 65536⟩
    (by decide) selected_cut_23379

theorem selected_cut_23380 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 305416) = some ⟨13, 1, 0, 3444, 305416, 1, 16384⟩ := by
  decide +kernel

theorem context_13_305416_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305416 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 305416 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 305416, 1, 16384⟩
    (by decide) selected_cut_23380

theorem selected_cut_23381 : selected 8 ⟨591838, by decide⟩
    (prefixPartial 13 305417) = some ⟨13, 2, 0, 591838, 305417, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_305417_591838 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305417 ⟨591838, by decide⟩ :=
  accepted_of_selected 13 305417 ⟨591838, by decide⟩ ⟨13, 2, 0, 591838, 305417, 2153, 16384⟩
    (by decide) selected_cut_23381

theorem selected_cut_23382 : selected 8 ⟨591857, by decide⟩
    (prefixPartial 13 305418) = some ⟨13, 2, 0, 591857, 305418, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_305418_591857 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305418 ⟨591857, by decide⟩ :=
  accepted_of_selected 13 305418 ⟨591857, by decide⟩ ⟨13, 2, 0, 591857, 305418, 1077, 16384⟩
    (by decide) selected_cut_23382

theorem selected_cut_23383 : selected 8 ⟨591864, by decide⟩
    (prefixPartial 13 305419) = some ⟨13, 2, 0, 591864, 305419, 873, 16384⟩ := by
  decide +kernel

theorem context_13_305419_591864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305419 ⟨591864, by decide⟩ :=
  accepted_of_selected 13 305419 ⟨591864, by decide⟩ ⟨13, 2, 0, 591864, 305419, 873, 16384⟩
    (by decide) selected_cut_23383

theorem unmarked_context_12_76354_591865 : frontier 9 ⟨591865, by decide⟩
    (prefixCache 12 76354) (prefixPartial 12 76354) = false := by
  decide +kernel

theorem node_context_12_76354_591865 : EJMOriginalGlobalDAGData.nodes 9 ⟨591865, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨591838, by decide⟩,⟨591857, by decide⟩,⟨591864, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76354_591865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76354 ⟨591865, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76354
    ⟨591865, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨591838, by decide⟩,⟨591857, by decide⟩,⟨591864, by decide⟩]) unmarked_context_12_76354_591865 node_context_12_76354_591865
  intro a
  fin_cases a
  · exact context_13_305416_3444
  · exact context_13_305417_591838
  · exact context_13_305418_591857
  · exact context_13_305419_591864

theorem selected_cut_23384 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 305420) = some ⟨13, 1, 0, 3444, 305420, 1, 16384⟩ := by
  decide +kernel

theorem context_13_305420_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305420 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 305420 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 305420, 1, 16384⟩
    (by decide) selected_cut_23384

theorem selected_cut_23385 : selected 8 ⟨591897, by decide⟩
    (prefixPartial 13 305421) = some ⟨13, 2, 0, 591897, 305421, 2637, 16384⟩ := by
  decide +kernel

theorem context_13_305421_591897 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305421 ⟨591897, by decide⟩ :=
  accepted_of_selected 13 305421 ⟨591897, by decide⟩ ⟨13, 2, 0, 591897, 305421, 2637, 16384⟩
    (by decide) selected_cut_23385

theorem selected_cut_23386 : selected 8 ⟨591914, by decide⟩
    (prefixPartial 13 305422) = some ⟨13, 2, 0, 591914, 305422, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_305422_591914 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305422 ⟨591914, by decide⟩ :=
  accepted_of_selected 13 305422 ⟨591914, by decide⟩ ⟨13, 2, 0, 591914, 305422, 1221, 16384⟩
    (by decide) selected_cut_23386

theorem selected_cut_23387 : selected 8 ⟨591923, by decide⟩
    (prefixPartial 13 305423) = some ⟨13, 2, 0, 591923, 305423, 905, 16384⟩ := by
  decide +kernel

theorem context_13_305423_591923 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305423 ⟨591923, by decide⟩ :=
  accepted_of_selected 13 305423 ⟨591923, by decide⟩ ⟨13, 2, 0, 591923, 305423, 905, 16384⟩
    (by decide) selected_cut_23387

theorem unmarked_context_12_76355_591924 : frontier 9 ⟨591924, by decide⟩
    (prefixCache 12 76355) (prefixPartial 12 76355) = false := by
  decide +kernel

theorem node_context_12_76355_591924 : EJMOriginalGlobalDAGData.nodes 9 ⟨591924, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨591897, by decide⟩,⟨591914, by decide⟩,⟨591923, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76355_591924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76355 ⟨591924, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76355
    ⟨591924, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨591897, by decide⟩,⟨591914, by decide⟩,⟨591923, by decide⟩]) unmarked_context_12_76355_591924 node_context_12_76355_591924
  intro a
  fin_cases a
  · exact context_13_305420_3444
  · exact context_13_305421_591897
  · exact context_13_305422_591914
  · exact context_13_305423_591923

theorem unmarked_context_11_19088_591925 : frontier 10 ⟨591925, by decide⟩
    (prefixCache 11 19088) (prefixPartial 11 19088) = false := by
  decide +kernel

theorem node_context_11_19088_591925 : EJMOriginalGlobalDAGData.nodes 10 ⟨591925, by decide⟩ =
    .split (coordinate 11) (![⟨591763, by decide⟩,⟨591809, by decide⟩,⟨591865, by decide⟩,⟨591924, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19088_591925 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19088 ⟨591925, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19088
    ⟨591925, by decide⟩ (by decide) (![⟨591763, by decide⟩,⟨591809, by decide⟩,⟨591865, by decide⟩,⟨591924, by decide⟩]) unmarked_context_11_19088_591925 node_context_11_19088_591925
  intro a
  fin_cases a
  · exact context_12_76352_591763
  · exact context_12_76353_591809
  · exact context_12_76354_591865
  · exact context_12_76355_591924

theorem selected_cut_23388 : selected 9 ⟨591969, by decide⟩
    (prefixPartial 12 76356) = some ⟨12, 2, 0, 591969, 76356, 3657, 65536⟩ := by
  decide +kernel

theorem context_12_76356_591969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76356 ⟨591969, by decide⟩ :=
  accepted_of_selected 12 76356 ⟨591969, by decide⟩ ⟨12, 2, 0, 591969, 76356, 3657, 65536⟩
    (by decide) selected_cut_23388

theorem selected_cut_23389 : selected 9 ⟨592017, by decide⟩
    (prefixPartial 12 76357) = some ⟨12, 2, 0, 592017, 76357, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_76357_592017 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76357 ⟨592017, by decide⟩ :=
  accepted_of_selected 12 76357 ⟨592017, by decide⟩ ⟨12, 2, 0, 592017, 76357, 3365, 65536⟩
    (by decide) selected_cut_23389

theorem selected_cut_23390 : selected 9 ⟨592070, by decide⟩
    (prefixPartial 12 76358) = some ⟨12, 2, 0, 592070, 76358, 3857, 65536⟩ := by
  decide +kernel

theorem context_12_76358_592070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76358 ⟨592070, by decide⟩ :=
  accepted_of_selected 12 76358 ⟨592070, by decide⟩ ⟨12, 2, 0, 592070, 76358, 3857, 65536⟩
    (by decide) selected_cut_23390

theorem selected_cut_23391 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 305436) = some ⟨13, 1, 0, 3444, 305436, 1, 16384⟩ := by
  decide +kernel

theorem context_13_305436_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305436 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 305436 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 305436, 1, 16384⟩
    (by decide) selected_cut_23391

theorem selected_cut_23392 : selected 8 ⟨592103, by decide⟩
    (prefixPartial 13 305437) = some ⟨13, 2, 0, 592103, 305437, 2057, 16384⟩ := by
  decide +kernel

theorem context_13_305437_592103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305437 ⟨592103, by decide⟩ :=
  accepted_of_selected 13 305437 ⟨592103, by decide⟩ ⟨13, 2, 0, 592103, 305437, 2057, 16384⟩
    (by decide) selected_cut_23392

theorem selected_cut_23393 : selected 8 ⟨592127, by decide⟩
    (prefixPartial 13 305438) = some ⟨13, 2, 0, 592127, 305438, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_305438_592127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305438 ⟨592127, by decide⟩ :=
  accepted_of_selected 13 305438 ⟨592127, by decide⟩ ⟨13, 2, 0, 592127, 305438, 1361, 16384⟩
    (by decide) selected_cut_23393

theorem selected_cut_23394 : selected 8 ⟨592137, by decide⟩
    (prefixPartial 13 305439) = some ⟨13, 2, 0, 592137, 305439, 901, 16384⟩ := by
  decide +kernel

theorem context_13_305439_592137 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305439 ⟨592137, by decide⟩ :=
  accepted_of_selected 13 305439 ⟨592137, by decide⟩ ⟨13, 2, 0, 592137, 305439, 901, 16384⟩
    (by decide) selected_cut_23394

theorem unmarked_context_12_76359_592138 : frontier 9 ⟨592138, by decide⟩
    (prefixCache 12 76359) (prefixPartial 12 76359) = false := by
  decide +kernel

theorem node_context_12_76359_592138 : EJMOriginalGlobalDAGData.nodes 9 ⟨592138, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨592103, by decide⟩,⟨592127, by decide⟩,⟨592137, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76359_592138 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76359 ⟨592138, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76359
    ⟨592138, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨592103, by decide⟩,⟨592127, by decide⟩,⟨592137, by decide⟩]) unmarked_context_12_76359_592138 node_context_12_76359_592138
  intro a
  fin_cases a
  · exact context_13_305436_3444
  · exact context_13_305437_592103
  · exact context_13_305438_592127
  · exact context_13_305439_592137

theorem unmarked_context_11_19089_592139 : frontier 10 ⟨592139, by decide⟩
    (prefixCache 11 19089) (prefixPartial 11 19089) = false := by
  decide +kernel

theorem node_context_11_19089_592139 : EJMOriginalGlobalDAGData.nodes 10 ⟨592139, by decide⟩ =
    .split (coordinate 11) (![⟨591969, by decide⟩,⟨592017, by decide⟩,⟨592070, by decide⟩,⟨592138, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19089_592139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19089 ⟨592139, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19089
    ⟨592139, by decide⟩ (by decide) (![⟨591969, by decide⟩,⟨592017, by decide⟩,⟨592070, by decide⟩,⟨592138, by decide⟩]) unmarked_context_11_19089_592139 node_context_11_19089_592139
  intro a
  fin_cases a
  · exact context_12_76356_591969
  · exact context_12_76357_592017
  · exact context_12_76358_592070
  · exact context_12_76359_592138

theorem selected_cut_23395 : selected 9 ⟨592179, by decide⟩
    (prefixPartial 12 76360) = some ⟨12, 2, 0, 592179, 76360, 3245, 65536⟩ := by
  decide +kernel

theorem context_12_76360_592179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76360 ⟨592179, by decide⟩ :=
  accepted_of_selected 12 76360 ⟨592179, by decide⟩ ⟨12, 2, 0, 592179, 76360, 3245, 65536⟩
    (by decide) selected_cut_23395

theorem selected_cut_23396 : selected 9 ⟨592222, by decide⟩
    (prefixPartial 12 76361) = some ⟨12, 2, 0, 592222, 76361, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_76361_592222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76361 ⟨592222, by decide⟩ :=
  accepted_of_selected 12 76361 ⟨592222, by decide⟩ ⟨12, 2, 0, 592222, 76361, 3193, 65536⟩
    (by decide) selected_cut_23396

theorem selected_cut_23397 : selected 9 ⟨592223, by decide⟩
    (prefixPartial 12 76362) = some ⟨12, 1, 0, 592223, 76362, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76362_592223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76362 ⟨592223, by decide⟩ :=
  accepted_of_selected 12 76362 ⟨592223, by decide⟩ ⟨12, 1, 0, 592223, 76362, 1, 65536⟩
    (by decide) selected_cut_23397

theorem selected_cut_23398 : selected 9 ⟨592269, by decide⟩
    (prefixPartial 12 76363) = some ⟨12, 2, 0, 592269, 76363, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_76363_592269 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76363 ⟨592269, by decide⟩ :=
  accepted_of_selected 12 76363 ⟨592269, by decide⟩ ⟨12, 2, 0, 592269, 76363, 3745, 65536⟩
    (by decide) selected_cut_23398

theorem unmarked_context_11_19090_592270 : frontier 10 ⟨592270, by decide⟩
    (prefixCache 11 19090) (prefixPartial 11 19090) = false := by
  decide +kernel

theorem node_context_11_19090_592270 : EJMOriginalGlobalDAGData.nodes 10 ⟨592270, by decide⟩ =
    .split (coordinate 11) (![⟨592179, by decide⟩,⟨592222, by decide⟩,⟨592223, by decide⟩,⟨592269, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19090_592270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19090 ⟨592270, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19090
    ⟨592270, by decide⟩ (by decide) (![⟨592179, by decide⟩,⟨592222, by decide⟩,⟨592223, by decide⟩,⟨592269, by decide⟩]) unmarked_context_11_19090_592270 node_context_11_19090_592270
  intro a
  fin_cases a
  · exact context_12_76360_592179
  · exact context_12_76361_592222
  · exact context_12_76362_592223
  · exact context_12_76363_592269

theorem selected_cut_23399 : selected 9 ⟨592309, by decide⟩
    (prefixPartial 12 76364) = some ⟨12, 2, 0, 592309, 76364, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_76364_592309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76364 ⟨592309, by decide⟩ :=
  accepted_of_selected 12 76364 ⟨592309, by decide⟩ ⟨12, 2, 0, 592309, 76364, 3621, 65536⟩
    (by decide) selected_cut_23399

theorem selected_cut_23400 : selected 9 ⟨592348, by decide⟩
    (prefixPartial 12 76365) = some ⟨12, 2, 0, 592348, 76365, 3561, 65536⟩ := by
  decide +kernel

theorem context_12_76365_592348 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76365 ⟨592348, by decide⟩ :=
  accepted_of_selected 12 76365 ⟨592348, by decide⟩ ⟨12, 2, 0, 592348, 76365, 3561, 65536⟩
    (by decide) selected_cut_23400

theorem selected_cut_23401 : selected 9 ⟨592410, by decide⟩
    (prefixPartial 12 76366) = some ⟨12, 2, 0, 592410, 76366, 3885, 65536⟩ := by
  decide +kernel

theorem context_12_76366_592410 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76366 ⟨592410, by decide⟩ :=
  accepted_of_selected 12 76366 ⟨592410, by decide⟩ ⟨12, 2, 0, 592410, 76366, 3885, 65536⟩
    (by decide) selected_cut_23401

theorem selected_cut_23402 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 305468) = some ⟨13, 1, 0, 3444, 305468, 1, 16384⟩ := by
  decide +kernel

theorem context_13_305468_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305468 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 305468 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 305468, 1, 16384⟩
    (by decide) selected_cut_23402

theorem selected_cut_23403 : selected 8 ⟨592431, by decide⟩
    (prefixPartial 13 305469) = some ⟨13, 2, 0, 592431, 305469, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_305469_592431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305469 ⟨592431, by decide⟩ :=
  accepted_of_selected 13 305469 ⟨592431, by decide⟩ ⟨13, 2, 0, 592431, 305469, 1929, 16384⟩
    (by decide) selected_cut_23403

theorem selected_cut_23404 : selected 8 ⟨592449, by decide⟩
    (prefixPartial 13 305470) = some ⟨13, 2, 0, 592449, 305470, 1305, 16384⟩ := by
  decide +kernel

theorem context_13_305470_592449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305470 ⟨592449, by decide⟩ :=
  accepted_of_selected 13 305470 ⟨592449, by decide⟩ ⟨13, 2, 0, 592449, 305470, 1305, 16384⟩
    (by decide) selected_cut_23404

theorem selected_cut_23405 : selected 8 ⟨592457, by decide⟩
    (prefixPartial 13 305471) = some ⟨13, 2, 0, 592457, 305471, 985, 16384⟩ := by
  decide +kernel

theorem context_13_305471_592457 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305471 ⟨592457, by decide⟩ :=
  accepted_of_selected 13 305471 ⟨592457, by decide⟩ ⟨13, 2, 0, 592457, 305471, 985, 16384⟩
    (by decide) selected_cut_23405

theorem unmarked_context_12_76367_592458 : frontier 9 ⟨592458, by decide⟩
    (prefixCache 12 76367) (prefixPartial 12 76367) = false := by
  decide +kernel

theorem node_context_12_76367_592458 : EJMOriginalGlobalDAGData.nodes 9 ⟨592458, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨592431, by decide⟩,⟨592449, by decide⟩,⟨592457, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76367_592458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76367 ⟨592458, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76367
    ⟨592458, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨592431, by decide⟩,⟨592449, by decide⟩,⟨592457, by decide⟩]) unmarked_context_12_76367_592458 node_context_12_76367_592458
  intro a
  fin_cases a
  · exact context_13_305468_3444
  · exact context_13_305469_592431
  · exact context_13_305470_592449
  · exact context_13_305471_592457

theorem unmarked_context_11_19091_592459 : frontier 10 ⟨592459, by decide⟩
    (prefixCache 11 19091) (prefixPartial 11 19091) = false := by
  decide +kernel

theorem node_context_11_19091_592459 : EJMOriginalGlobalDAGData.nodes 10 ⟨592459, by decide⟩ =
    .split (coordinate 11) (![⟨592309, by decide⟩,⟨592348, by decide⟩,⟨592410, by decide⟩,⟨592458, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19091_592459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19091 ⟨592459, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19091
    ⟨592459, by decide⟩ (by decide) (![⟨592309, by decide⟩,⟨592348, by decide⟩,⟨592410, by decide⟩,⟨592458, by decide⟩]) unmarked_context_11_19091_592459 node_context_11_19091_592459
  intro a
  fin_cases a
  · exact context_12_76364_592309
  · exact context_12_76365_592348
  · exact context_12_76366_592410
  · exact context_12_76367_592458

theorem unmarked_context_10_4772_592460 : frontier 11 ⟨592460, by decide⟩
    (prefixCache 10 4772) (prefixPartial 10 4772) = false := by
  decide +kernel

theorem node_context_10_4772_592460 : EJMOriginalGlobalDAGData.nodes 11 ⟨592460, by decide⟩ =
    .split (coordinate 10) (![⟨591925, by decide⟩,⟨592139, by decide⟩,⟨592270, by decide⟩,⟨592459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4772_592460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4772 ⟨592460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4772
    ⟨592460, by decide⟩ (by decide) (![⟨591925, by decide⟩,⟨592139, by decide⟩,⟨592270, by decide⟩,⟨592459, by decide⟩]) unmarked_context_10_4772_592460 node_context_10_4772_592460
  intro a
  fin_cases a
  · exact context_11_19088_591925
  · exact context_11_19089_592139
  · exact context_11_19090_592270
  · exact context_11_19091_592459

theorem selected_cut_23406 : selected 9 ⟨592511, by decide⟩
    (prefixPartial 12 76368) = some ⟨12, 2, 0, 592511, 76368, 3801, 65536⟩ := by
  decide +kernel

theorem context_12_76368_592511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76368 ⟨592511, by decide⟩ :=
  accepted_of_selected 12 76368 ⟨592511, by decide⟩ ⟨12, 2, 0, 592511, 76368, 3801, 65536⟩
    (by decide) selected_cut_23406

theorem selected_cut_23407 : selected 9 ⟨592562, by decide⟩
    (prefixPartial 12 76369) = some ⟨12, 2, 0, 592562, 76369, 3929, 65536⟩ := by
  decide +kernel

theorem context_12_76369_592562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76369 ⟨592562, by decide⟩ :=
  accepted_of_selected 12 76369 ⟨592562, by decide⟩ ⟨12, 2, 0, 592562, 76369, 3929, 65536⟩
    (by decide) selected_cut_23407

theorem selected_cut_23408 : selected 9 ⟨592612, by decide⟩
    (prefixPartial 12 76370) = some ⟨12, 2, 0, 592612, 76370, 3889, 65536⟩ := by
  decide +kernel

theorem context_12_76370_592612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76370 ⟨592612, by decide⟩ :=
  accepted_of_selected 12 76370 ⟨592612, by decide⟩ ⟨12, 2, 0, 592612, 76370, 3889, 65536⟩
    (by decide) selected_cut_23408

theorem selected_cut_23409 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 305484) = some ⟨13, 1, 0, 3444, 305484, 1, 16384⟩ := by
  decide +kernel

theorem context_13_305484_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305484 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 305484 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 305484, 1, 16384⟩
    (by decide) selected_cut_23409

theorem selected_cut_23410 : selected 8 ⟨592635, by decide⟩
    (prefixPartial 13 305485) = some ⟨13, 2, 0, 592635, 305485, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_305485_592635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305485 ⟨592635, by decide⟩ :=
  accepted_of_selected 13 305485 ⟨592635, by decide⟩ ⟨13, 2, 0, 592635, 305485, 2121, 16384⟩
    (by decide) selected_cut_23410

theorem selected_cut_23411 : selected 8 ⟨592662, by decide⟩
    (prefixPartial 13 305486) = some ⟨13, 2, 0, 592662, 305486, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_305486_592662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305486 ⟨592662, by decide⟩ :=
  accepted_of_selected 13 305486 ⟨592662, by decide⟩ ⟨13, 2, 0, 592662, 305486, 1685, 16384⟩
    (by decide) selected_cut_23411

theorem selected_cut_23412 : selected 8 ⟨592674, by decide⟩
    (prefixPartial 13 305487) = some ⟨13, 2, 0, 592674, 305487, 901, 16384⟩ := by
  decide +kernel

theorem context_13_305487_592674 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305487 ⟨592674, by decide⟩ :=
  accepted_of_selected 13 305487 ⟨592674, by decide⟩ ⟨13, 2, 0, 592674, 305487, 901, 16384⟩
    (by decide) selected_cut_23412

theorem unmarked_context_12_76371_592675 : frontier 9 ⟨592675, by decide⟩
    (prefixCache 12 76371) (prefixPartial 12 76371) = false := by
  decide +kernel

theorem node_context_12_76371_592675 : EJMOriginalGlobalDAGData.nodes 9 ⟨592675, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨592635, by decide⟩,⟨592662, by decide⟩,⟨592674, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76371_592675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76371 ⟨592675, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76371
    ⟨592675, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨592635, by decide⟩,⟨592662, by decide⟩,⟨592674, by decide⟩]) unmarked_context_12_76371_592675 node_context_12_76371_592675
  intro a
  fin_cases a
  · exact context_13_305484_3444
  · exact context_13_305485_592635
  · exact context_13_305486_592662
  · exact context_13_305487_592674

theorem unmarked_context_11_19092_592676 : frontier 10 ⟨592676, by decide⟩
    (prefixCache 11 19092) (prefixPartial 11 19092) = false := by
  decide +kernel

theorem node_context_11_19092_592676 : EJMOriginalGlobalDAGData.nodes 10 ⟨592676, by decide⟩ =
    .split (coordinate 11) (![⟨592511, by decide⟩,⟨592562, by decide⟩,⟨592612, by decide⟩,⟨592675, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19092_592676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19092 ⟨592676, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19092
    ⟨592676, by decide⟩ (by decide) (![⟨592511, by decide⟩,⟨592562, by decide⟩,⟨592612, by decide⟩,⟨592675, by decide⟩]) unmarked_context_11_19092_592676 node_context_11_19092_592676
  intro a
  fin_cases a
  · exact context_12_76368_592511
  · exact context_12_76369_592562
  · exact context_12_76370_592612
  · exact context_12_76371_592675

theorem selected_cut_23413 : selected 9 ⟨592723, by decide⟩
    (prefixPartial 12 76372) = some ⟨12, 2, 0, 592723, 76372, 3789, 65536⟩ := by
  decide +kernel

theorem context_12_76372_592723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76372 ⟨592723, by decide⟩ :=
  accepted_of_selected 12 76372 ⟨592723, by decide⟩ ⟨12, 2, 0, 592723, 76372, 3789, 65536⟩
    (by decide) selected_cut_23413

theorem selected_cut_23414 : selected 9 ⟨592764, by decide⟩
    (prefixPartial 12 76373) = some ⟨12, 2, 0, 592764, 76373, 3497, 65536⟩ := by
  decide +kernel

theorem context_12_76373_592764 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76373 ⟨592764, by decide⟩ :=
  accepted_of_selected 12 76373 ⟨592764, by decide⟩ ⟨12, 2, 0, 592764, 76373, 3497, 65536⟩
    (by decide) selected_cut_23414

theorem selected_cut_23415 : selected 9 ⟨592824, by decide⟩
    (prefixPartial 12 76374) = some ⟨12, 2, 0, 592824, 76374, 3937, 65536⟩ := by
  decide +kernel

theorem context_12_76374_592824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76374 ⟨592824, by decide⟩ :=
  accepted_of_selected 12 76374 ⟨592824, by decide⟩ ⟨12, 2, 0, 592824, 76374, 3937, 65536⟩
    (by decide) selected_cut_23415

theorem selected_cut_23416 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 305500) = some ⟨13, 1, 0, 3444, 305500, 1, 16384⟩ := by
  decide +kernel

theorem context_13_305500_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305500 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 305500 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 305500, 1, 16384⟩
    (by decide) selected_cut_23416

theorem selected_cut_23417 : selected 8 ⟨592850, by decide⟩
    (prefixPartial 13 305501) = some ⟨13, 2, 0, 592850, 305501, 1801, 16384⟩ := by
  decide +kernel

theorem context_13_305501_592850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305501 ⟨592850, by decide⟩ :=
  accepted_of_selected 13 305501 ⟨592850, by decide⟩ ⟨13, 2, 0, 592850, 305501, 1801, 16384⟩
    (by decide) selected_cut_23417

theorem selected_cut_23418 : selected 8 ⟨592875, by decide⟩
    (prefixPartial 13 305502) = some ⟨13, 2, 0, 592875, 305502, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_305502_592875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305502 ⟨592875, by decide⟩ :=
  accepted_of_selected 13 305502 ⟨592875, by decide⟩ ⟨13, 2, 0, 592875, 305502, 1901, 16384⟩
    (by decide) selected_cut_23418

theorem selected_cut_23419 : selected 8 ⟨592888, by decide⟩
    (prefixPartial 13 305503) = some ⟨13, 2, 0, 592888, 305503, 989, 16384⟩ := by
  decide +kernel

theorem context_13_305503_592888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 305503 ⟨592888, by decide⟩ :=
  accepted_of_selected 13 305503 ⟨592888, by decide⟩ ⟨13, 2, 0, 592888, 305503, 989, 16384⟩
    (by decide) selected_cut_23419

theorem unmarked_context_12_76375_592889 : frontier 9 ⟨592889, by decide⟩
    (prefixCache 12 76375) (prefixPartial 12 76375) = false := by
  decide +kernel

theorem node_context_12_76375_592889 : EJMOriginalGlobalDAGData.nodes 9 ⟨592889, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨592850, by decide⟩,⟨592875, by decide⟩,⟨592888, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_76375_592889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76375 ⟨592889, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 76375
    ⟨592889, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨592850, by decide⟩,⟨592875, by decide⟩,⟨592888, by decide⟩]) unmarked_context_12_76375_592889 node_context_12_76375_592889
  intro a
  fin_cases a
  · exact context_13_305500_3444
  · exact context_13_305501_592850
  · exact context_13_305502_592875
  · exact context_13_305503_592888

theorem unmarked_context_11_19093_592890 : frontier 10 ⟨592890, by decide⟩
    (prefixCache 11 19093) (prefixPartial 11 19093) = false := by
  decide +kernel

theorem node_context_11_19093_592890 : EJMOriginalGlobalDAGData.nodes 10 ⟨592890, by decide⟩ =
    .split (coordinate 11) (![⟨592723, by decide⟩,⟨592764, by decide⟩,⟨592824, by decide⟩,⟨592889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19093_592890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19093 ⟨592890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19093
    ⟨592890, by decide⟩ (by decide) (![⟨592723, by decide⟩,⟨592764, by decide⟩,⟨592824, by decide⟩,⟨592889, by decide⟩]) unmarked_context_11_19093_592890 node_context_11_19093_592890
  intro a
  fin_cases a
  · exact context_12_76372_592723
  · exact context_12_76373_592764
  · exact context_12_76374_592824
  · exact context_12_76375_592889

theorem selected_cut_23420 : selected 9 ⟨592930, by decide⟩
    (prefixPartial 12 76376) = some ⟨12, 2, 0, 592930, 76376, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_76376_592930 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76376 ⟨592930, by decide⟩ :=
  accepted_of_selected 12 76376 ⟨592930, by decide⟩ ⟨12, 2, 0, 592930, 76376, 3229, 65536⟩
    (by decide) selected_cut_23420

theorem selected_cut_23421 : selected 9 ⟨592977, by decide⟩
    (prefixPartial 12 76377) = some ⟨12, 2, 0, 592977, 76377, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_76377_592977 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76377 ⟨592977, by decide⟩ :=
  accepted_of_selected 12 76377 ⟨592977, by decide⟩ ⟨12, 2, 0, 592977, 76377, 3217, 65536⟩
    (by decide) selected_cut_23421

theorem selected_cut_23422 : selected 9 ⟨212113, by decide⟩
    (prefixPartial 12 76378) = some ⟨12, 1, 0, 212113, 76378, 1, 65536⟩ := by
  decide +kernel

theorem context_12_76378_212113 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76378 ⟨212113, by decide⟩ :=
  accepted_of_selected 12 76378 ⟨212113, by decide⟩ ⟨12, 1, 0, 212113, 76378, 1, 65536⟩
    (by decide) selected_cut_23422

theorem selected_cut_23423 : selected 9 ⟨593033, by decide⟩
    (prefixPartial 12 76379) = some ⟨12, 2, 0, 593033, 76379, 3653, 65536⟩ := by
  decide +kernel

theorem context_12_76379_593033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76379 ⟨593033, by decide⟩ :=
  accepted_of_selected 12 76379 ⟨593033, by decide⟩ ⟨12, 2, 0, 593033, 76379, 3653, 65536⟩
    (by decide) selected_cut_23423

theorem unmarked_context_11_19094_593034 : frontier 10 ⟨593034, by decide⟩
    (prefixCache 11 19094) (prefixPartial 11 19094) = false := by
  decide +kernel

theorem node_context_11_19094_593034 : EJMOriginalGlobalDAGData.nodes 10 ⟨593034, by decide⟩ =
    .split (coordinate 11) (![⟨592930, by decide⟩,⟨592977, by decide⟩,⟨212113, by decide⟩,⟨593033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19094_593034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19094 ⟨593034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19094
    ⟨593034, by decide⟩ (by decide) (![⟨592930, by decide⟩,⟨592977, by decide⟩,⟨212113, by decide⟩,⟨593033, by decide⟩]) unmarked_context_11_19094_593034 node_context_11_19094_593034
  intro a
  fin_cases a
  · exact context_12_76376_592930
  · exact context_12_76377_592977
  · exact context_12_76378_212113
  · exact context_12_76379_593033

theorem selected_cut_23424 : selected 9 ⟨593082, by decide⟩
    (prefixPartial 12 76380) = some ⟨12, 2, 0, 593082, 76380, 3529, 65536⟩ := by
  decide +kernel

theorem context_12_76380_593082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76380 ⟨593082, by decide⟩ :=
  accepted_of_selected 12 76380 ⟨593082, by decide⟩ ⟨12, 2, 0, 593082, 76380, 3529, 65536⟩
    (by decide) selected_cut_23424

theorem selected_cut_23425 : selected 9 ⟨593130, by decide⟩
    (prefixPartial 12 76381) = some ⟨12, 2, 0, 593130, 76381, 3369, 65536⟩ := by
  decide +kernel

theorem context_12_76381_593130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76381 ⟨593130, by decide⟩ :=
  accepted_of_selected 12 76381 ⟨593130, by decide⟩ ⟨12, 2, 0, 593130, 76381, 3369, 65536⟩
    (by decide) selected_cut_23425

theorem selected_cut_23426 : selected 9 ⟨593186, by decide⟩
    (prefixPartial 12 76382) = some ⟨12, 2, 0, 593186, 76382, 3445, 65536⟩ := by
  decide +kernel

theorem context_12_76382_593186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76382 ⟨593186, by decide⟩ :=
  accepted_of_selected 12 76382 ⟨593186, by decide⟩ ⟨12, 2, 0, 593186, 76382, 3445, 65536⟩
    (by decide) selected_cut_23426

theorem selected_cut_23427 : selected 9 ⟨593242, by decide⟩
    (prefixPartial 12 76383) = some ⟨12, 2, 0, 593242, 76383, 4089, 65536⟩ := by
  decide +kernel

theorem context_12_76383_593242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 76383 ⟨593242, by decide⟩ :=
  accepted_of_selected 12 76383 ⟨593242, by decide⟩ ⟨12, 2, 0, 593242, 76383, 4089, 65536⟩
    (by decide) selected_cut_23427

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
