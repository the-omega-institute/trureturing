/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover348
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_33508 : selected 8 ⟨862723, by decide⟩
    (prefixPartial 13 441421) = some ⟨13, 2, 0, 862723, 441421, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_441421_862723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441421 ⟨862723, by decide⟩ :=
  accepted_of_selected 13 441421 ⟨862723, by decide⟩ ⟨13, 2, 0, 862723, 441421, 2613, 16384⟩
    (by decide) selected_cut_33508

theorem selected_cut_33509 : selected 8 ⟨862770, by decide⟩
    (prefixPartial 13 441422) = some ⟨13, 2, 0, 862770, 441422, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_441422_862770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441422 ⟨862770, by decide⟩ :=
  accepted_of_selected 13 441422 ⟨862770, by decide⟩ ⟨13, 2, 0, 862770, 441422, 1677, 16384⟩
    (by decide) selected_cut_33509

theorem selected_cut_33510 : selected 8 ⟨862776, by decide⟩
    (prefixPartial 13 441423) = some ⟨13, 2, 0, 862776, 441423, 593, 16384⟩ := by
  decide +kernel

theorem context_13_441423_862776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441423 ⟨862776, by decide⟩ :=
  accepted_of_selected 13 441423 ⟨862776, by decide⟩ ⟨13, 2, 0, 862776, 441423, 593, 16384⟩
    (by decide) selected_cut_33510

theorem unmarked_context_12_110355_862777 : frontier 9 ⟨862777, by decide⟩
    (prefixCache 12 110355) (prefixPartial 12 110355) = false := by
  decide +kernel

theorem node_context_12_110355_862777 : EJMOriginalGlobalDAGData.nodes 9 ⟨862777, by decide⟩ =
    .split (coordinate 12) (![⟨862694, by decide⟩,⟨862723, by decide⟩,⟨862770, by decide⟩,⟨862776, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110355_862777 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110355 ⟨862777, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110355
    ⟨862777, by decide⟩ (by decide) (![⟨862694, by decide⟩,⟨862723, by decide⟩,⟨862770, by decide⟩,⟨862776, by decide⟩]) unmarked_context_12_110355_862777 node_context_12_110355_862777
  intro a
  fin_cases a
  · exact context_13_441420_862694
  · exact context_13_441421_862723
  · exact context_13_441422_862770
  · exact context_13_441423_862776

theorem unmarked_context_11_27588_862778 : frontier 10 ⟨862778, by decide⟩
    (prefixCache 11 27588) (prefixPartial 11 27588) = false := by
  decide +kernel

theorem node_context_11_27588_862778 : EJMOriginalGlobalDAGData.nodes 10 ⟨862778, by decide⟩ =
    .split (coordinate 11) (![⟨862337, by decide⟩,⟨862505, by decide⟩,⟨862650, by decide⟩,⟨862777, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27588_862778 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27588 ⟨862778, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27588
    ⟨862778, by decide⟩ (by decide) (![⟨862337, by decide⟩,⟨862505, by decide⟩,⟨862650, by decide⟩,⟨862777, by decide⟩]) unmarked_context_11_27588_862778 node_context_11_27588_862778
  intro a
  fin_cases a
  · exact context_12_110352_862337
  · exact context_12_110353_862505
  · exact context_12_110354_862650
  · exact context_12_110355_862777

theorem selected_cut_33511 : selected 8 ⟨862820, by decide⟩
    (prefixPartial 13 441424) = some ⟨13, 2, 0, 862820, 441424, 2073, 16384⟩ := by
  decide +kernel

theorem context_13_441424_862820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441424 ⟨862820, by decide⟩ :=
  accepted_of_selected 13 441424 ⟨862820, by decide⟩ ⟨13, 2, 0, 862820, 441424, 2073, 16384⟩
    (by decide) selected_cut_33511

theorem selected_cut_33512 : selected 8 ⟨862851, by decide⟩
    (prefixPartial 13 441425) = some ⟨13, 2, 0, 862851, 441425, 2565, 16384⟩ := by
  decide +kernel

theorem context_13_441425_862851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441425 ⟨862851, by decide⟩ :=
  accepted_of_selected 13 441425 ⟨862851, by decide⟩ ⟨13, 2, 0, 862851, 441425, 2565, 16384⟩
    (by decide) selected_cut_33512

theorem selected_cut_33513 : selected 8 ⟨862885, by decide⟩
    (prefixPartial 13 441426) = some ⟨13, 2, 0, 862885, 441426, 1585, 16384⟩ := by
  decide +kernel

theorem context_13_441426_862885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441426 ⟨862885, by decide⟩ :=
  accepted_of_selected 13 441426 ⟨862885, by decide⟩ ⟨13, 2, 0, 862885, 441426, 1585, 16384⟩
    (by decide) selected_cut_33513

theorem selected_cut_33514 : selected 8 ⟨862892, by decide⟩
    (prefixPartial 13 441427) = some ⟨13, 2, 0, 862892, 441427, 753, 16384⟩ := by
  decide +kernel

theorem context_13_441427_862892 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441427 ⟨862892, by decide⟩ :=
  accepted_of_selected 13 441427 ⟨862892, by decide⟩ ⟨13, 2, 0, 862892, 441427, 753, 16384⟩
    (by decide) selected_cut_33514

theorem unmarked_context_12_110356_862893 : frontier 9 ⟨862893, by decide⟩
    (prefixCache 12 110356) (prefixPartial 12 110356) = false := by
  decide +kernel

theorem node_context_12_110356_862893 : EJMOriginalGlobalDAGData.nodes 9 ⟨862893, by decide⟩ =
    .split (coordinate 12) (![⟨862820, by decide⟩,⟨862851, by decide⟩,⟨862885, by decide⟩,⟨862892, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110356_862893 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110356 ⟨862893, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110356
    ⟨862893, by decide⟩ (by decide) (![⟨862820, by decide⟩,⟨862851, by decide⟩,⟨862885, by decide⟩,⟨862892, by decide⟩]) unmarked_context_12_110356_862893 node_context_12_110356_862893
  intro a
  fin_cases a
  · exact context_13_441424_862820
  · exact context_13_441425_862851
  · exact context_13_441426_862885
  · exact context_13_441427_862892

theorem selected_cut_33515 : selected 8 ⟨862944, by decide⟩
    (prefixPartial 13 441428) = some ⟨13, 2, 0, 862944, 441428, 2645, 16384⟩ := by
  decide +kernel

theorem context_13_441428_862944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441428 ⟨862944, by decide⟩ :=
  accepted_of_selected 13 441428 ⟨862944, by decide⟩ ⟨13, 2, 0, 862944, 441428, 2645, 16384⟩
    (by decide) selected_cut_33515

theorem selected_cut_33516 : selected 8 ⟨862971, by decide⟩
    (prefixPartial 13 441429) = some ⟨13, 2, 0, 862971, 441429, 2461, 16384⟩ := by
  decide +kernel

theorem context_13_441429_862971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441429 ⟨862971, by decide⟩ :=
  accepted_of_selected 13 441429 ⟨862971, by decide⟩ ⟨13, 2, 0, 862971, 441429, 2461, 16384⟩
    (by decide) selected_cut_33516

theorem selected_cut_33517 : selected 8 ⟨863037, by decide⟩
    (prefixPartial 13 441430) = some ⟨13, 2, 0, 863037, 441430, 1937, 16384⟩ := by
  decide +kernel

theorem context_13_441430_863037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441430 ⟨863037, by decide⟩ :=
  accepted_of_selected 13 441430 ⟨863037, by decide⟩ ⟨13, 2, 0, 863037, 441430, 1937, 16384⟩
    (by decide) selected_cut_33517

theorem selected_cut_33518 : selected 8 ⟨863041, by decide⟩
    (prefixPartial 13 441431) = some ⟨13, 2, 0, 863041, 441431, 649, 16384⟩ := by
  decide +kernel

theorem context_13_441431_863041 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441431 ⟨863041, by decide⟩ :=
  accepted_of_selected 13 441431 ⟨863041, by decide⟩ ⟨13, 2, 0, 863041, 441431, 649, 16384⟩
    (by decide) selected_cut_33518

theorem unmarked_context_12_110357_863042 : frontier 9 ⟨863042, by decide⟩
    (prefixCache 12 110357) (prefixPartial 12 110357) = false := by
  decide +kernel

theorem node_context_12_110357_863042 : EJMOriginalGlobalDAGData.nodes 9 ⟨863042, by decide⟩ =
    .split (coordinate 12) (![⟨862944, by decide⟩,⟨862971, by decide⟩,⟨863037, by decide⟩,⟨863041, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110357_863042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110357 ⟨863042, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110357
    ⟨863042, by decide⟩ (by decide) (![⟨862944, by decide⟩,⟨862971, by decide⟩,⟨863037, by decide⟩,⟨863041, by decide⟩]) unmarked_context_12_110357_863042 node_context_12_110357_863042
  intro a
  fin_cases a
  · exact context_13_441428_862944
  · exact context_13_441429_862971
  · exact context_13_441430_863037
  · exact context_13_441431_863041

theorem selected_cut_33519 : selected 8 ⟨863080, by decide⟩
    (prefixPartial 13 441432) = some ⟨13, 2, 0, 863080, 441432, 2161, 16384⟩ := by
  decide +kernel

theorem context_13_441432_863080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441432 ⟨863080, by decide⟩ :=
  accepted_of_selected 13 441432 ⟨863080, by decide⟩ ⟨13, 2, 0, 863080, 441432, 2161, 16384⟩
    (by decide) selected_cut_33519

theorem selected_cut_33520 : selected 8 ⟨863109, by decide⟩
    (prefixPartial 13 441433) = some ⟨13, 2, 0, 863109, 441433, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_441433_863109 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441433 ⟨863109, by decide⟩ :=
  accepted_of_selected 13 441433 ⟨863109, by decide⟩ ⟨13, 2, 0, 863109, 441433, 2429, 16384⟩
    (by decide) selected_cut_33520

theorem selected_cut_33521 : selected 8 ⟨863140, by decide⟩
    (prefixPartial 13 441434) = some ⟨13, 2, 0, 863140, 441434, 1453, 16384⟩ := by
  decide +kernel

theorem context_13_441434_863140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441434 ⟨863140, by decide⟩ :=
  accepted_of_selected 13 441434 ⟨863140, by decide⟩ ⟨13, 2, 0, 863140, 441434, 1453, 16384⟩
    (by decide) selected_cut_33521

theorem selected_cut_33522 : selected 8 ⟨863145, by decide⟩
    (prefixPartial 13 441435) = some ⟨13, 2, 0, 863145, 441435, 697, 16384⟩ := by
  decide +kernel

theorem context_13_441435_863145 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441435 ⟨863145, by decide⟩ :=
  accepted_of_selected 13 441435 ⟨863145, by decide⟩ ⟨13, 2, 0, 863145, 441435, 697, 16384⟩
    (by decide) selected_cut_33522

theorem unmarked_context_12_110358_863146 : frontier 9 ⟨863146, by decide⟩
    (prefixCache 12 110358) (prefixPartial 12 110358) = false := by
  decide +kernel

theorem node_context_12_110358_863146 : EJMOriginalGlobalDAGData.nodes 9 ⟨863146, by decide⟩ =
    .split (coordinate 12) (![⟨863080, by decide⟩,⟨863109, by decide⟩,⟨863140, by decide⟩,⟨863145, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110358_863146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110358 ⟨863146, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110358
    ⟨863146, by decide⟩ (by decide) (![⟨863080, by decide⟩,⟨863109, by decide⟩,⟨863140, by decide⟩,⟨863145, by decide⟩]) unmarked_context_12_110358_863146 node_context_12_110358_863146
  intro a
  fin_cases a
  · exact context_13_441432_863080
  · exact context_13_441433_863109
  · exact context_13_441434_863140
  · exact context_13_441435_863145

theorem selected_cut_33523 : selected 8 ⟨863195, by decide⟩
    (prefixPartial 13 441436) = some ⟨13, 2, 0, 863195, 441436, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_441436_863195 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441436 ⟨863195, by decide⟩ :=
  accepted_of_selected 13 441436 ⟨863195, by decide⟩ ⟨13, 2, 0, 863195, 441436, 2297, 16384⟩
    (by decide) selected_cut_33523

theorem selected_cut_33524 : selected 8 ⟨863230, by decide⟩
    (prefixPartial 13 441437) = some ⟨13, 2, 0, 863230, 441437, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_441437_863230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441437 ⟨863230, by decide⟩ :=
  accepted_of_selected 13 441437 ⟨863230, by decide⟩ ⟨13, 2, 0, 863230, 441437, 2553, 16384⟩
    (by decide) selected_cut_33524

theorem selected_cut_33525 : selected 8 ⟨863280, by decide⟩
    (prefixPartial 13 441438) = some ⟨13, 2, 0, 863280, 441438, 1901, 16384⟩ := by
  decide +kernel

theorem context_13_441438_863280 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441438 ⟨863280, by decide⟩ :=
  accepted_of_selected 13 441438 ⟨863280, by decide⟩ ⟨13, 2, 0, 863280, 441438, 1901, 16384⟩
    (by decide) selected_cut_33525

theorem selected_cut_33526 : selected 8 ⟨863283, by decide⟩
    (prefixPartial 13 441439) = some ⟨13, 2, 0, 863283, 441439, 625, 16384⟩ := by
  decide +kernel

theorem context_13_441439_863283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441439 ⟨863283, by decide⟩ :=
  accepted_of_selected 13 441439 ⟨863283, by decide⟩ ⟨13, 2, 0, 863283, 441439, 625, 16384⟩
    (by decide) selected_cut_33526

theorem unmarked_context_12_110359_863284 : frontier 9 ⟨863284, by decide⟩
    (prefixCache 12 110359) (prefixPartial 12 110359) = false := by
  decide +kernel

theorem node_context_12_110359_863284 : EJMOriginalGlobalDAGData.nodes 9 ⟨863284, by decide⟩ =
    .split (coordinate 12) (![⟨863195, by decide⟩,⟨863230, by decide⟩,⟨863280, by decide⟩,⟨863283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110359_863284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110359 ⟨863284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110359
    ⟨863284, by decide⟩ (by decide) (![⟨863195, by decide⟩,⟨863230, by decide⟩,⟨863280, by decide⟩,⟨863283, by decide⟩]) unmarked_context_12_110359_863284 node_context_12_110359_863284
  intro a
  fin_cases a
  · exact context_13_441436_863195
  · exact context_13_441437_863230
  · exact context_13_441438_863280
  · exact context_13_441439_863283

theorem unmarked_context_11_27589_863285 : frontier 10 ⟨863285, by decide⟩
    (prefixCache 11 27589) (prefixPartial 11 27589) = false := by
  decide +kernel

theorem node_context_11_27589_863285 : EJMOriginalGlobalDAGData.nodes 10 ⟨863285, by decide⟩ =
    .split (coordinate 11) (![⟨862893, by decide⟩,⟨863042, by decide⟩,⟨863146, by decide⟩,⟨863284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27589_863285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27589 ⟨863285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27589
    ⟨863285, by decide⟩ (by decide) (![⟨862893, by decide⟩,⟨863042, by decide⟩,⟨863146, by decide⟩,⟨863284, by decide⟩]) unmarked_context_11_27589_863285 node_context_11_27589_863285
  intro a
  fin_cases a
  · exact context_12_110356_862893
  · exact context_12_110357_863042
  · exact context_12_110358_863146
  · exact context_12_110359_863284

theorem selected_cut_33527 : selected 8 ⟨863322, by decide⟩
    (prefixPartial 13 441440) = some ⟨13, 2, 0, 863322, 441440, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_441440_863322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441440 ⟨863322, by decide⟩ :=
  accepted_of_selected 13 441440 ⟨863322, by decide⟩ ⟨13, 2, 0, 863322, 441440, 1957, 16384⟩
    (by decide) selected_cut_33527

theorem selected_cut_33528 : selected 8 ⟨863363, by decide⟩
    (prefixPartial 13 441441) = some ⟨13, 2, 0, 863363, 441441, 2505, 16384⟩ := by
  decide +kernel

theorem context_13_441441_863363 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441441 ⟨863363, by decide⟩ :=
  accepted_of_selected 13 441441 ⟨863363, by decide⟩ ⟨13, 2, 0, 863363, 441441, 2505, 16384⟩
    (by decide) selected_cut_33528

theorem selected_cut_33529 : selected 8 ⟨863420, by decide⟩
    (prefixPartial 13 441442) = some ⟨13, 2, 0, 863420, 441442, 1689, 16384⟩ := by
  decide +kernel

theorem context_13_441442_863420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441442 ⟨863420, by decide⟩ :=
  accepted_of_selected 13 441442 ⟨863420, by decide⟩ ⟨13, 2, 0, 863420, 441442, 1689, 16384⟩
    (by decide) selected_cut_33529

theorem selected_cut_33530 : selected 8 ⟨863427, by decide⟩
    (prefixPartial 13 441443) = some ⟨13, 2, 0, 863427, 441443, 617, 16384⟩ := by
  decide +kernel

theorem context_13_441443_863427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441443 ⟨863427, by decide⟩ :=
  accepted_of_selected 13 441443 ⟨863427, by decide⟩ ⟨13, 2, 0, 863427, 441443, 617, 16384⟩
    (by decide) selected_cut_33530

theorem unmarked_context_12_110360_863428 : frontier 9 ⟨863428, by decide⟩
    (prefixCache 12 110360) (prefixPartial 12 110360) = false := by
  decide +kernel

theorem node_context_12_110360_863428 : EJMOriginalGlobalDAGData.nodes 9 ⟨863428, by decide⟩ =
    .split (coordinate 12) (![⟨863322, by decide⟩,⟨863363, by decide⟩,⟨863420, by decide⟩,⟨863427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110360_863428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110360 ⟨863428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110360
    ⟨863428, by decide⟩ (by decide) (![⟨863322, by decide⟩,⟨863363, by decide⟩,⟨863420, by decide⟩,⟨863427, by decide⟩]) unmarked_context_12_110360_863428 node_context_12_110360_863428
  intro a
  fin_cases a
  · exact context_13_441440_863322
  · exact context_13_441441_863363
  · exact context_13_441442_863420
  · exact context_13_441443_863427

theorem selected_cut_33531 : selected 8 ⟨863476, by decide⟩
    (prefixPartial 13 441444) = some ⟨13, 2, 0, 863476, 441444, 2433, 16384⟩ := by
  decide +kernel

theorem context_13_441444_863476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441444 ⟨863476, by decide⟩ :=
  accepted_of_selected 13 441444 ⟨863476, by decide⟩ ⟨13, 2, 0, 863476, 441444, 2433, 16384⟩
    (by decide) selected_cut_33531

theorem selected_cut_33532 : selected 8 ⟨863512, by decide⟩
    (prefixPartial 13 441445) = some ⟨13, 2, 0, 863512, 441445, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_441445_863512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441445 ⟨863512, by decide⟩ :=
  accepted_of_selected 13 441445 ⟨863512, by decide⟩ ⟨13, 2, 0, 863512, 441445, 2469, 16384⟩
    (by decide) selected_cut_33532

theorem selected_cut_33533 : selected 8 ⟨863572, by decide⟩
    (prefixPartial 13 441446) = some ⟨13, 2, 0, 863572, 441446, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_441446_863572 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441446 ⟨863572, by decide⟩ :=
  accepted_of_selected 13 441446 ⟨863572, by decide⟩ ⟨13, 2, 0, 863572, 441446, 1977, 16384⟩
    (by decide) selected_cut_33533

theorem selected_cut_33534 : selected 8 ⟨863581, by decide⟩
    (prefixPartial 13 441447) = some ⟨13, 2, 0, 863581, 441447, 581, 16384⟩ := by
  decide +kernel

theorem context_13_441447_863581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441447 ⟨863581, by decide⟩ :=
  accepted_of_selected 13 441447 ⟨863581, by decide⟩ ⟨13, 2, 0, 863581, 441447, 581, 16384⟩
    (by decide) selected_cut_33534

theorem unmarked_context_12_110361_863582 : frontier 9 ⟨863582, by decide⟩
    (prefixCache 12 110361) (prefixPartial 12 110361) = false := by
  decide +kernel

theorem node_context_12_110361_863582 : EJMOriginalGlobalDAGData.nodes 9 ⟨863582, by decide⟩ =
    .split (coordinate 12) (![⟨863476, by decide⟩,⟨863512, by decide⟩,⟨863572, by decide⟩,⟨863581, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110361_863582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110361 ⟨863582, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110361
    ⟨863582, by decide⟩ (by decide) (![⟨863476, by decide⟩,⟨863512, by decide⟩,⟨863572, by decide⟩,⟨863581, by decide⟩]) unmarked_context_12_110361_863582 node_context_12_110361_863582
  intro a
  fin_cases a
  · exact context_13_441444_863476
  · exact context_13_441445_863512
  · exact context_13_441446_863572
  · exact context_13_441447_863581

theorem selected_cut_33535 : selected 8 ⟨863613, by decide⟩
    (prefixPartial 13 441448) = some ⟨13, 2, 0, 863613, 441448, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_441448_863613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441448 ⟨863613, by decide⟩ :=
  accepted_of_selected 13 441448 ⟨863613, by decide⟩ ⟨13, 2, 0, 863613, 441448, 1721, 16384⟩
    (by decide) selected_cut_33535

theorem selected_cut_33536 : selected 8 ⟨863648, by decide⟩
    (prefixPartial 13 441449) = some ⟨13, 2, 0, 863648, 441449, 2393, 16384⟩ := by
  decide +kernel

theorem context_13_441449_863648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441449 ⟨863648, by decide⟩ :=
  accepted_of_selected 13 441449 ⟨863648, by decide⟩ ⟨13, 2, 0, 863648, 441449, 2393, 16384⟩
    (by decide) selected_cut_33536

theorem selected_cut_33537 : selected 8 ⟨863675, by decide⟩
    (prefixPartial 13 441450) = some ⟨13, 2, 0, 863675, 441450, 1437, 16384⟩ := by
  decide +kernel

theorem context_13_441450_863675 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441450 ⟨863675, by decide⟩ :=
  accepted_of_selected 13 441450 ⟨863675, by decide⟩ ⟨13, 2, 0, 863675, 441450, 1437, 16384⟩
    (by decide) selected_cut_33537

theorem selected_cut_33538 : selected 8 ⟨863680, by decide⟩
    (prefixPartial 13 441451) = some ⟨13, 2, 0, 863680, 441451, 517, 16384⟩ := by
  decide +kernel

theorem context_13_441451_863680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441451 ⟨863680, by decide⟩ :=
  accepted_of_selected 13 441451 ⟨863680, by decide⟩ ⟨13, 2, 0, 863680, 441451, 517, 16384⟩
    (by decide) selected_cut_33538

theorem unmarked_context_12_110362_863681 : frontier 9 ⟨863681, by decide⟩
    (prefixCache 12 110362) (prefixPartial 12 110362) = false := by
  decide +kernel

theorem node_context_12_110362_863681 : EJMOriginalGlobalDAGData.nodes 9 ⟨863681, by decide⟩ =
    .split (coordinate 12) (![⟨863613, by decide⟩,⟨863648, by decide⟩,⟨863675, by decide⟩,⟨863680, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110362_863681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110362 ⟨863681, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110362
    ⟨863681, by decide⟩ (by decide) (![⟨863613, by decide⟩,⟨863648, by decide⟩,⟨863675, by decide⟩,⟨863680, by decide⟩]) unmarked_context_12_110362_863681 node_context_12_110362_863681
  intro a
  fin_cases a
  · exact context_13_441448_863613
  · exact context_13_441449_863648
  · exact context_13_441450_863675
  · exact context_13_441451_863680

theorem selected_cut_33539 : selected 8 ⟨863718, by decide⟩
    (prefixPartial 13 441452) = some ⟨13, 2, 0, 863718, 441452, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_441452_863718 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441452 ⟨863718, by decide⟩ :=
  accepted_of_selected 13 441452 ⟨863718, by decide⟩ ⟨13, 2, 0, 863718, 441452, 1957, 16384⟩
    (by decide) selected_cut_33539

theorem selected_cut_33540 : selected 8 ⟨863759, by decide⟩
    (prefixPartial 13 441453) = some ⟨13, 2, 0, 863759, 441453, 2677, 16384⟩ := by
  decide +kernel

theorem context_13_441453_863759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441453 ⟨863759, by decide⟩ :=
  accepted_of_selected 13 441453 ⟨863759, by decide⟩ ⟨13, 2, 0, 863759, 441453, 2677, 16384⟩
    (by decide) selected_cut_33540

theorem selected_cut_33541 : selected 8 ⟨863800, by decide⟩
    (prefixPartial 13 441454) = some ⟨13, 2, 0, 863800, 441454, 1793, 16384⟩ := by
  decide +kernel

theorem context_13_441454_863800 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441454 ⟨863800, by decide⟩ :=
  accepted_of_selected 13 441454 ⟨863800, by decide⟩ ⟨13, 2, 0, 863800, 441454, 1793, 16384⟩
    (by decide) selected_cut_33541

theorem selected_cut_33542 : selected 8 ⟨863805, by decide⟩
    (prefixPartial 13 441455) = some ⟨13, 2, 0, 863805, 441455, 541, 16384⟩ := by
  decide +kernel

theorem context_13_441455_863805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441455 ⟨863805, by decide⟩ :=
  accepted_of_selected 13 441455 ⟨863805, by decide⟩ ⟨13, 2, 0, 863805, 441455, 541, 16384⟩
    (by decide) selected_cut_33542

theorem unmarked_context_12_110363_863806 : frontier 9 ⟨863806, by decide⟩
    (prefixCache 12 110363) (prefixPartial 12 110363) = false := by
  decide +kernel

theorem node_context_12_110363_863806 : EJMOriginalGlobalDAGData.nodes 9 ⟨863806, by decide⟩ =
    .split (coordinate 12) (![⟨863718, by decide⟩,⟨863759, by decide⟩,⟨863800, by decide⟩,⟨863805, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110363_863806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110363 ⟨863806, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110363
    ⟨863806, by decide⟩ (by decide) (![⟨863718, by decide⟩,⟨863759, by decide⟩,⟨863800, by decide⟩,⟨863805, by decide⟩]) unmarked_context_12_110363_863806 node_context_12_110363_863806
  intro a
  fin_cases a
  · exact context_13_441452_863718
  · exact context_13_441453_863759
  · exact context_13_441454_863800
  · exact context_13_441455_863805

theorem unmarked_context_11_27590_863807 : frontier 10 ⟨863807, by decide⟩
    (prefixCache 11 27590) (prefixPartial 11 27590) = false := by
  decide +kernel

theorem node_context_11_27590_863807 : EJMOriginalGlobalDAGData.nodes 10 ⟨863807, by decide⟩ =
    .split (coordinate 11) (![⟨863428, by decide⟩,⟨863582, by decide⟩,⟨863681, by decide⟩,⟨863806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27590_863807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27590 ⟨863807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27590
    ⟨863807, by decide⟩ (by decide) (![⟨863428, by decide⟩,⟨863582, by decide⟩,⟨863681, by decide⟩,⟨863806, by decide⟩]) unmarked_context_11_27590_863807 node_context_11_27590_863807
  intro a
  fin_cases a
  · exact context_12_110360_863428
  · exact context_12_110361_863582
  · exact context_12_110362_863681
  · exact context_12_110363_863806

theorem selected_cut_33543 : selected 8 ⟨863828, by decide⟩
    (prefixPartial 13 441456) = some ⟨13, 2, 0, 863828, 441456, 1529, 16384⟩ := by
  decide +kernel

theorem context_13_441456_863828 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441456 ⟨863828, by decide⟩ :=
  accepted_of_selected 13 441456 ⟨863828, by decide⟩ ⟨13, 2, 0, 863828, 441456, 1529, 16384⟩
    (by decide) selected_cut_33543

theorem selected_cut_33544 : selected 8 ⟨863850, by decide⟩
    (prefixPartial 13 441457) = some ⟨13, 2, 0, 863850, 441457, 2301, 16384⟩ := by
  decide +kernel

theorem context_13_441457_863850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441457 ⟨863850, by decide⟩ :=
  accepted_of_selected 13 441457 ⟨863850, by decide⟩ ⟨13, 2, 0, 863850, 441457, 2301, 16384⟩
    (by decide) selected_cut_33544

theorem selected_cut_33545 : selected 8 ⟨863877, by decide⟩
    (prefixPartial 13 441458) = some ⟨13, 2, 0, 863877, 441458, 1409, 16384⟩ := by
  decide +kernel

theorem context_13_441458_863877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441458 ⟨863877, by decide⟩ :=
  accepted_of_selected 13 441458 ⟨863877, by decide⟩ ⟨13, 2, 0, 863877, 441458, 1409, 16384⟩
    (by decide) selected_cut_33545

theorem selected_cut_33546 : selected 8 ⟨863882, by decide⟩
    (prefixPartial 13 441459) = some ⟨13, 2, 0, 863882, 441459, 693, 16384⟩ := by
  decide +kernel

theorem context_13_441459_863882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441459 ⟨863882, by decide⟩ :=
  accepted_of_selected 13 441459 ⟨863882, by decide⟩ ⟨13, 2, 0, 863882, 441459, 693, 16384⟩
    (by decide) selected_cut_33546

theorem unmarked_context_12_110364_863883 : frontier 9 ⟨863883, by decide⟩
    (prefixCache 12 110364) (prefixPartial 12 110364) = false := by
  decide +kernel

theorem node_context_12_110364_863883 : EJMOriginalGlobalDAGData.nodes 9 ⟨863883, by decide⟩ =
    .split (coordinate 12) (![⟨863828, by decide⟩,⟨863850, by decide⟩,⟨863877, by decide⟩,⟨863882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110364_863883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110364 ⟨863883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110364
    ⟨863883, by decide⟩ (by decide) (![⟨863828, by decide⟩,⟨863850, by decide⟩,⟨863877, by decide⟩,⟨863882, by decide⟩]) unmarked_context_12_110364_863883 node_context_12_110364_863883
  intro a
  fin_cases a
  · exact context_13_441456_863828
  · exact context_13_441457_863850
  · exact context_13_441458_863877
  · exact context_13_441459_863882

theorem selected_cut_33547 : selected 8 ⟨863918, by decide⟩
    (prefixPartial 13 441460) = some ⟨13, 2, 0, 863918, 441460, 1993, 16384⟩ := by
  decide +kernel

theorem context_13_441460_863918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441460 ⟨863918, by decide⟩ :=
  accepted_of_selected 13 441460 ⟨863918, by decide⟩ ⟨13, 2, 0, 863918, 441460, 1993, 16384⟩
    (by decide) selected_cut_33547

theorem selected_cut_33548 : selected 8 ⟨863944, by decide⟩
    (prefixPartial 13 441461) = some ⟨13, 2, 0, 863944, 441461, 2453, 16384⟩ := by
  decide +kernel

theorem context_13_441461_863944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441461 ⟨863944, by decide⟩ :=
  accepted_of_selected 13 441461 ⟨863944, by decide⟩ ⟨13, 2, 0, 863944, 441461, 2453, 16384⟩
    (by decide) selected_cut_33548

theorem selected_cut_33549 : selected 8 ⟨863994, by decide⟩
    (prefixPartial 13 441462) = some ⟨13, 2, 0, 863994, 441462, 1869, 16384⟩ := by
  decide +kernel

theorem context_13_441462_863994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441462 ⟨863994, by decide⟩ :=
  accepted_of_selected 13 441462 ⟨863994, by decide⟩ ⟨13, 2, 0, 863994, 441462, 1869, 16384⟩
    (by decide) selected_cut_33549

theorem selected_cut_33550 : selected 8 ⟨863999, by decide⟩
    (prefixPartial 13 441463) = some ⟨13, 2, 0, 863999, 441463, 665, 16384⟩ := by
  decide +kernel

theorem context_13_441463_863999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441463 ⟨863999, by decide⟩ :=
  accepted_of_selected 13 441463 ⟨863999, by decide⟩ ⟨13, 2, 0, 863999, 441463, 665, 16384⟩
    (by decide) selected_cut_33550

theorem unmarked_context_12_110365_864000 : frontier 9 ⟨864000, by decide⟩
    (prefixCache 12 110365) (prefixPartial 12 110365) = false := by
  decide +kernel

theorem node_context_12_110365_864000 : EJMOriginalGlobalDAGData.nodes 9 ⟨864000, by decide⟩ =
    .split (coordinate 12) (![⟨863918, by decide⟩,⟨863944, by decide⟩,⟨863994, by decide⟩,⟨863999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110365_864000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110365 ⟨864000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110365
    ⟨864000, by decide⟩ (by decide) (![⟨863918, by decide⟩,⟨863944, by decide⟩,⟨863994, by decide⟩,⟨863999, by decide⟩]) unmarked_context_12_110365_864000 node_context_12_110365_864000
  intro a
  fin_cases a
  · exact context_13_441460_863918
  · exact context_13_441461_863944
  · exact context_13_441462_863994
  · exact context_13_441463_863999

theorem selected_cut_33551 : selected 8 ⟨864027, by decide⟩
    (prefixPartial 13 441464) = some ⟨13, 2, 0, 864027, 441464, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_441464_864027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441464 ⟨864027, by decide⟩ :=
  accepted_of_selected 13 441464 ⟨864027, by decide⟩ ⟨13, 2, 0, 864027, 441464, 1425, 16384⟩
    (by decide) selected_cut_33551

theorem selected_cut_33552 : selected 8 ⟨864054, by decide⟩
    (prefixPartial 13 441465) = some ⟨13, 2, 0, 864054, 441465, 2357, 16384⟩ := by
  decide +kernel

theorem context_13_441465_864054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441465 ⟨864054, by decide⟩ :=
  accepted_of_selected 13 441465 ⟨864054, by decide⟩ ⟨13, 2, 0, 864054, 441465, 2357, 16384⟩
    (by decide) selected_cut_33552

theorem selected_cut_33553 : selected 8 ⟨864081, by decide⟩
    (prefixPartial 13 441466) = some ⟨13, 2, 0, 864081, 441466, 1241, 16384⟩ := by
  decide +kernel

theorem context_13_441466_864081 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441466 ⟨864081, by decide⟩ :=
  accepted_of_selected 13 441466 ⟨864081, by decide⟩ ⟨13, 2, 0, 864081, 441466, 1241, 16384⟩
    (by decide) selected_cut_33553

theorem selected_cut_33554 : selected 8 ⟨864088, by decide⟩
    (prefixPartial 13 441467) = some ⟨13, 2, 0, 864088, 441467, 633, 16384⟩ := by
  decide +kernel

theorem context_13_441467_864088 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441467 ⟨864088, by decide⟩ :=
  accepted_of_selected 13 441467 ⟨864088, by decide⟩ ⟨13, 2, 0, 864088, 441467, 633, 16384⟩
    (by decide) selected_cut_33554

theorem unmarked_context_12_110366_864089 : frontier 9 ⟨864089, by decide⟩
    (prefixCache 12 110366) (prefixPartial 12 110366) = false := by
  decide +kernel

theorem node_context_12_110366_864089 : EJMOriginalGlobalDAGData.nodes 9 ⟨864089, by decide⟩ =
    .split (coordinate 12) (![⟨864027, by decide⟩,⟨864054, by decide⟩,⟨864081, by decide⟩,⟨864088, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110366_864089 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110366 ⟨864089, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110366
    ⟨864089, by decide⟩ (by decide) (![⟨864027, by decide⟩,⟨864054, by decide⟩,⟨864081, by decide⟩,⟨864088, by decide⟩]) unmarked_context_12_110366_864089 node_context_12_110366_864089
  intro a
  fin_cases a
  · exact context_13_441464_864027
  · exact context_13_441465_864054
  · exact context_13_441466_864081
  · exact context_13_441467_864088

theorem selected_cut_33555 : selected 9 ⟨757807, by decide⟩
    (prefixPartial 12 110367) = some ⟨12, 1, 0, 757807, 110367, 1, 65536⟩ := by
  decide +kernel

theorem context_12_110367_757807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110367 ⟨757807, by decide⟩ :=
  accepted_of_selected 12 110367 ⟨757807, by decide⟩ ⟨12, 1, 0, 757807, 110367, 1, 65536⟩
    (by decide) selected_cut_33555

theorem unmarked_context_11_27591_864090 : frontier 10 ⟨864090, by decide⟩
    (prefixCache 11 27591) (prefixPartial 11 27591) = false := by
  decide +kernel

theorem node_context_11_27591_864090 : EJMOriginalGlobalDAGData.nodes 10 ⟨864090, by decide⟩ =
    .split (coordinate 11) (![⟨863883, by decide⟩,⟨864000, by decide⟩,⟨864089, by decide⟩,⟨757807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27591_864090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27591 ⟨864090, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27591
    ⟨864090, by decide⟩ (by decide) (![⟨863883, by decide⟩,⟨864000, by decide⟩,⟨864089, by decide⟩,⟨757807, by decide⟩]) unmarked_context_11_27591_864090 node_context_11_27591_864090
  intro a
  fin_cases a
  · exact context_12_110364_863883
  · exact context_12_110365_864000
  · exact context_12_110366_864089
  · exact context_12_110367_757807

theorem unmarked_context_10_6897_864091 : frontier 11 ⟨864091, by decide⟩
    (prefixCache 10 6897) (prefixPartial 10 6897) = false := by
  decide +kernel

theorem node_context_10_6897_864091 : EJMOriginalGlobalDAGData.nodes 11 ⟨864091, by decide⟩ =
    .split (coordinate 10) (![⟨862778, by decide⟩,⟨863285, by decide⟩,⟨863807, by decide⟩,⟨864090, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_6897_864091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 6897 ⟨864091, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 6897
    ⟨864091, by decide⟩ (by decide) (![⟨862778, by decide⟩,⟨863285, by decide⟩,⟨863807, by decide⟩,⟨864090, by decide⟩]) unmarked_context_10_6897_864091 node_context_10_6897_864091
  intro a
  fin_cases a
  · exact context_11_27588_862778
  · exact context_11_27589_863285
  · exact context_11_27590_863807
  · exact context_11_27591_864090

theorem selected_cut_33556 : selected 8 ⟨864119, by decide⟩
    (prefixPartial 13 441472) = some ⟨13, 2, 0, 864119, 441472, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_441472_864119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441472 ⟨864119, by decide⟩ :=
  accepted_of_selected 13 441472 ⟨864119, by decide⟩ ⟨13, 2, 0, 864119, 441472, 1737, 16384⟩
    (by decide) selected_cut_33556

theorem selected_cut_33557 : selected 8 ⟨864169, by decide⟩
    (prefixPartial 13 441473) = some ⟨13, 2, 0, 864169, 441473, 3033, 16384⟩ := by
  decide +kernel

theorem context_13_441473_864169 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441473 ⟨864169, by decide⟩ :=
  accepted_of_selected 13 441473 ⟨864169, by decide⟩ ⟨13, 2, 0, 864169, 441473, 3033, 16384⟩
    (by decide) selected_cut_33557

theorem selected_cut_33558 : selected 8 ⟨864197, by decide⟩
    (prefixPartial 13 441474) = some ⟨13, 2, 0, 864197, 441474, 1301, 16384⟩ := by
  decide +kernel

theorem context_13_441474_864197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441474 ⟨864197, by decide⟩ :=
  accepted_of_selected 13 441474 ⟨864197, by decide⟩ ⟨13, 2, 0, 864197, 441474, 1301, 16384⟩
    (by decide) selected_cut_33558

theorem selected_cut_33559 : selected 8 ⟨864201, by decide⟩
    (prefixPartial 13 441475) = some ⟨13, 2, 0, 864201, 441475, 617, 16384⟩ := by
  decide +kernel

theorem context_13_441475_864201 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441475 ⟨864201, by decide⟩ :=
  accepted_of_selected 13 441475 ⟨864201, by decide⟩ ⟨13, 2, 0, 864201, 441475, 617, 16384⟩
    (by decide) selected_cut_33559

theorem unmarked_context_12_110368_864202 : frontier 9 ⟨864202, by decide⟩
    (prefixCache 12 110368) (prefixPartial 12 110368) = false := by
  decide +kernel

theorem node_context_12_110368_864202 : EJMOriginalGlobalDAGData.nodes 9 ⟨864202, by decide⟩ =
    .split (coordinate 12) (![⟨864119, by decide⟩,⟨864169, by decide⟩,⟨864197, by decide⟩,⟨864201, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110368_864202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110368 ⟨864202, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110368
    ⟨864202, by decide⟩ (by decide) (![⟨864119, by decide⟩,⟨864169, by decide⟩,⟨864197, by decide⟩,⟨864201, by decide⟩]) unmarked_context_12_110368_864202 node_context_12_110368_864202
  intro a
  fin_cases a
  · exact context_13_441472_864119
  · exact context_13_441473_864169
  · exact context_13_441474_864197
  · exact context_13_441475_864201

theorem selected_cut_33560 : selected 8 ⟨864237, by decide⟩
    (prefixPartial 13 441476) = some ⟨13, 2, 0, 864237, 441476, 1953, 16384⟩ := by
  decide +kernel

theorem context_13_441476_864237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441476 ⟨864237, by decide⟩ :=
  accepted_of_selected 13 441476 ⟨864237, by decide⟩ ⟨13, 2, 0, 864237, 441476, 1953, 16384⟩
    (by decide) selected_cut_33560

theorem selected_cut_33561 : selected 8 ⟨864304, by decide⟩
    (prefixPartial 13 441477) = some ⟨13, 2, 0, 864304, 441477, 3193, 16384⟩ := by
  decide +kernel

theorem context_13_441477_864304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441477 ⟨864304, by decide⟩ :=
  accepted_of_selected 13 441477 ⟨864304, by decide⟩ ⟨13, 2, 0, 864304, 441477, 3193, 16384⟩
    (by decide) selected_cut_33561

theorem selected_cut_33562 : selected 8 ⟨864334, by decide⟩
    (prefixPartial 13 441478) = some ⟨13, 2, 0, 864334, 441478, 1557, 16384⟩ := by
  decide +kernel

theorem context_13_441478_864334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441478 ⟨864334, by decide⟩ :=
  accepted_of_selected 13 441478 ⟨864334, by decide⟩ ⟨13, 2, 0, 864334, 441478, 1557, 16384⟩
    (by decide) selected_cut_33562

theorem selected_cut_33563 : selected 8 ⟨864336, by decide⟩
    (prefixPartial 13 441479) = some ⟨13, 2, 0, 864336, 441479, 545, 16384⟩ := by
  decide +kernel

theorem context_13_441479_864336 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441479 ⟨864336, by decide⟩ :=
  accepted_of_selected 13 441479 ⟨864336, by decide⟩ ⟨13, 2, 0, 864336, 441479, 545, 16384⟩
    (by decide) selected_cut_33563

theorem unmarked_context_12_110369_864337 : frontier 9 ⟨864337, by decide⟩
    (prefixCache 12 110369) (prefixPartial 12 110369) = false := by
  decide +kernel

theorem node_context_12_110369_864337 : EJMOriginalGlobalDAGData.nodes 9 ⟨864337, by decide⟩ =
    .split (coordinate 12) (![⟨864237, by decide⟩,⟨864304, by decide⟩,⟨864334, by decide⟩,⟨864336, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110369_864337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110369 ⟨864337, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110369
    ⟨864337, by decide⟩ (by decide) (![⟨864237, by decide⟩,⟨864304, by decide⟩,⟨864334, by decide⟩,⟨864336, by decide⟩]) unmarked_context_12_110369_864337 node_context_12_110369_864337
  intro a
  fin_cases a
  · exact context_13_441476_864237
  · exact context_13_441477_864304
  · exact context_13_441478_864334
  · exact context_13_441479_864336

theorem selected_cut_33564 : selected 8 ⟨864359, by decide⟩
    (prefixPartial 13 441480) = some ⟨13, 2, 0, 864359, 441480, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_441480_864359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441480 ⟨864359, by decide⟩ :=
  accepted_of_selected 13 441480 ⟨864359, by decide⟩ ⟨13, 2, 0, 864359, 441480, 1461, 16384⟩
    (by decide) selected_cut_33564

theorem selected_cut_33565 : selected 8 ⟨864398, by decide⟩
    (prefixPartial 13 441481) = some ⟨13, 2, 0, 864398, 441481, 2685, 16384⟩ := by
  decide +kernel

theorem context_13_441481_864398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441481 ⟨864398, by decide⟩ :=
  accepted_of_selected 13 441481 ⟨864398, by decide⟩ ⟨13, 2, 0, 864398, 441481, 2685, 16384⟩
    (by decide) selected_cut_33565

theorem selected_cut_33566 : selected 8 ⟨864422, by decide⟩
    (prefixPartial 13 441482) = some ⟨13, 2, 0, 864422, 441482, 1229, 16384⟩ := by
  decide +kernel

theorem context_13_441482_864422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441482 ⟨864422, by decide⟩ :=
  accepted_of_selected 13 441482 ⟨864422, by decide⟩ ⟨13, 2, 0, 864422, 441482, 1229, 16384⟩
    (by decide) selected_cut_33566

theorem selected_cut_33567 : selected 8 ⟨864427, by decide⟩
    (prefixPartial 13 441483) = some ⟨13, 2, 0, 864427, 441483, 601, 16384⟩ := by
  decide +kernel

theorem context_13_441483_864427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441483 ⟨864427, by decide⟩ :=
  accepted_of_selected 13 441483 ⟨864427, by decide⟩ ⟨13, 2, 0, 864427, 441483, 601, 16384⟩
    (by decide) selected_cut_33567

theorem unmarked_context_12_110370_864428 : frontier 9 ⟨864428, by decide⟩
    (prefixCache 12 110370) (prefixPartial 12 110370) = false := by
  decide +kernel

theorem node_context_12_110370_864428 : EJMOriginalGlobalDAGData.nodes 9 ⟨864428, by decide⟩ =
    .split (coordinate 12) (![⟨864359, by decide⟩,⟨864398, by decide⟩,⟨864422, by decide⟩,⟨864427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110370_864428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110370 ⟨864428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110370
    ⟨864428, by decide⟩ (by decide) (![⟨864359, by decide⟩,⟨864398, by decide⟩,⟨864422, by decide⟩,⟨864427, by decide⟩]) unmarked_context_12_110370_864428 node_context_12_110370_864428
  intro a
  fin_cases a
  · exact context_13_441480_864359
  · exact context_13_441481_864398
  · exact context_13_441482_864422
  · exact context_13_441483_864427

theorem selected_cut_33568 : selected 8 ⟨864454, by decide⟩
    (prefixPartial 13 441484) = some ⟨13, 2, 0, 864454, 441484, 1545, 16384⟩ := by
  decide +kernel

theorem context_13_441484_864454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441484 ⟨864454, by decide⟩ :=
  accepted_of_selected 13 441484 ⟨864454, by decide⟩ ⟨13, 2, 0, 864454, 441484, 1545, 16384⟩
    (by decide) selected_cut_33568

theorem selected_cut_33569 : selected 8 ⟨864506, by decide⟩
    (prefixPartial 13 441485) = some ⟨13, 2, 0, 864506, 441485, 3081, 16384⟩ := by
  decide +kernel

theorem context_13_441485_864506 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441485 ⟨864506, by decide⟩ :=
  accepted_of_selected 13 441485 ⟨864506, by decide⟩ ⟨13, 2, 0, 864506, 441485, 3081, 16384⟩
    (by decide) selected_cut_33569

theorem selected_cut_33570 : selected 8 ⟨864532, by decide⟩
    (prefixPartial 13 441486) = some ⟨13, 2, 0, 864532, 441486, 1461, 16384⟩ := by
  decide +kernel

theorem context_13_441486_864532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441486 ⟨864532, by decide⟩ :=
  accepted_of_selected 13 441486 ⟨864532, by decide⟩ ⟨13, 2, 0, 864532, 441486, 1461, 16384⟩
    (by decide) selected_cut_33570

theorem selected_cut_33571 : selected 8 ⟨864536, by decide⟩
    (prefixPartial 13 441487) = some ⟨13, 2, 0, 864536, 441487, 569, 16384⟩ := by
  decide +kernel

theorem context_13_441487_864536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441487 ⟨864536, by decide⟩ :=
  accepted_of_selected 13 441487 ⟨864536, by decide⟩ ⟨13, 2, 0, 864536, 441487, 569, 16384⟩
    (by decide) selected_cut_33571

theorem unmarked_context_12_110371_864537 : frontier 9 ⟨864537, by decide⟩
    (prefixCache 12 110371) (prefixPartial 12 110371) = false := by
  decide +kernel

theorem node_context_12_110371_864537 : EJMOriginalGlobalDAGData.nodes 9 ⟨864537, by decide⟩ =
    .split (coordinate 12) (![⟨864454, by decide⟩,⟨864506, by decide⟩,⟨864532, by decide⟩,⟨864536, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110371_864537 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110371 ⟨864537, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110371
    ⟨864537, by decide⟩ (by decide) (![⟨864454, by decide⟩,⟨864506, by decide⟩,⟨864532, by decide⟩,⟨864536, by decide⟩]) unmarked_context_12_110371_864537 node_context_12_110371_864537
  intro a
  fin_cases a
  · exact context_13_441484_864454
  · exact context_13_441485_864506
  · exact context_13_441486_864532
  · exact context_13_441487_864536

theorem unmarked_context_11_27592_864538 : frontier 10 ⟨864538, by decide⟩
    (prefixCache 11 27592) (prefixPartial 11 27592) = false := by
  decide +kernel

theorem node_context_11_27592_864538 : EJMOriginalGlobalDAGData.nodes 10 ⟨864538, by decide⟩ =
    .split (coordinate 11) (![⟨864202, by decide⟩,⟨864337, by decide⟩,⟨864428, by decide⟩,⟨864537, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27592_864538 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27592 ⟨864538, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27592
    ⟨864538, by decide⟩ (by decide) (![⟨864202, by decide⟩,⟨864337, by decide⟩,⟨864428, by decide⟩,⟨864537, by decide⟩]) unmarked_context_11_27592_864538 node_context_11_27592_864538
  intro a
  fin_cases a
  · exact context_12_110368_864202
  · exact context_12_110369_864337
  · exact context_12_110370_864428
  · exact context_12_110371_864537

theorem selected_cut_33572 : selected 8 ⟨864566, by decide⟩
    (prefixPartial 13 441488) = some ⟨13, 2, 0, 864566, 441488, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_441488_864566 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441488 ⟨864566, by decide⟩ :=
  accepted_of_selected 13 441488 ⟨864566, by decide⟩ ⟨13, 2, 0, 864566, 441488, 1501, 16384⟩
    (by decide) selected_cut_33572

theorem selected_cut_33573 : selected 8 ⟨864612, by decide⟩
    (prefixPartial 13 441489) = some ⟨13, 2, 0, 864612, 441489, 3313, 16384⟩ := by
  decide +kernel

theorem context_13_441489_864612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441489 ⟨864612, by decide⟩ :=
  accepted_of_selected 13 441489 ⟨864612, by decide⟩ ⟨13, 2, 0, 864612, 441489, 3313, 16384⟩
    (by decide) selected_cut_33573

theorem selected_cut_33574 : selected 8 ⟨864640, by decide⟩
    (prefixPartial 13 441490) = some ⟨13, 2, 0, 864640, 441490, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_441490_864640 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441490 ⟨864640, by decide⟩ :=
  accepted_of_selected 13 441490 ⟨864640, by decide⟩ ⟨13, 2, 0, 864640, 441490, 1509, 16384⟩
    (by decide) selected_cut_33574

theorem selected_cut_33575 : selected 8 ⟨864647, by decide⟩
    (prefixPartial 13 441491) = some ⟨13, 2, 0, 864647, 441491, 789, 16384⟩ := by
  decide +kernel

theorem context_13_441491_864647 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441491 ⟨864647, by decide⟩ :=
  accepted_of_selected 13 441491 ⟨864647, by decide⟩ ⟨13, 2, 0, 864647, 441491, 789, 16384⟩
    (by decide) selected_cut_33575

theorem unmarked_context_12_110372_864648 : frontier 9 ⟨864648, by decide⟩
    (prefixCache 12 110372) (prefixPartial 12 110372) = false := by
  decide +kernel

theorem node_context_12_110372_864648 : EJMOriginalGlobalDAGData.nodes 9 ⟨864648, by decide⟩ =
    .split (coordinate 12) (![⟨864566, by decide⟩,⟨864612, by decide⟩,⟨864640, by decide⟩,⟨864647, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110372_864648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110372 ⟨864648, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110372
    ⟨864648, by decide⟩ (by decide) (![⟨864566, by decide⟩,⟨864612, by decide⟩,⟨864640, by decide⟩,⟨864647, by decide⟩]) unmarked_context_12_110372_864648 node_context_12_110372_864648
  intro a
  fin_cases a
  · exact context_13_441488_864566
  · exact context_13_441489_864612
  · exact context_13_441490_864640
  · exact context_13_441491_864647

theorem selected_cut_33576 : selected 8 ⟨864682, by decide⟩
    (prefixPartial 13 441492) = some ⟨13, 2, 0, 864682, 441492, 1749, 16384⟩ := by
  decide +kernel

theorem context_13_441492_864682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441492 ⟨864682, by decide⟩ :=
  accepted_of_selected 13 441492 ⟨864682, by decide⟩ ⟨13, 2, 0, 864682, 441492, 1749, 16384⟩
    (by decide) selected_cut_33576

theorem selected_cut_33577 : selected 8 ⟨864723, by decide⟩
    (prefixPartial 13 441493) = some ⟨13, 2, 0, 864723, 441493, 3141, 16384⟩ := by
  decide +kernel

theorem context_13_441493_864723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441493 ⟨864723, by decide⟩ :=
  accepted_of_selected 13 441493 ⟨864723, by decide⟩ ⟨13, 2, 0, 864723, 441493, 3141, 16384⟩
    (by decide) selected_cut_33577

theorem selected_cut_33578 : selected 8 ⟨864765, by decide⟩
    (prefixPartial 13 441494) = some ⟨13, 2, 0, 864765, 441494, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_441494_864765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441494 ⟨864765, by decide⟩ :=
  accepted_of_selected 13 441494 ⟨864765, by decide⟩ ⟨13, 2, 0, 864765, 441494, 1741, 16384⟩
    (by decide) selected_cut_33578

theorem selected_cut_33579 : selected 8 ⟨864769, by decide⟩
    (prefixPartial 13 441495) = some ⟨13, 2, 0, 864769, 441495, 593, 16384⟩ := by
  decide +kernel

theorem context_13_441495_864769 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441495 ⟨864769, by decide⟩ :=
  accepted_of_selected 13 441495 ⟨864769, by decide⟩ ⟨13, 2, 0, 864769, 441495, 593, 16384⟩
    (by decide) selected_cut_33579

theorem unmarked_context_12_110373_864770 : frontier 9 ⟨864770, by decide⟩
    (prefixCache 12 110373) (prefixPartial 12 110373) = false := by
  decide +kernel

theorem node_context_12_110373_864770 : EJMOriginalGlobalDAGData.nodes 9 ⟨864770, by decide⟩ =
    .split (coordinate 12) (![⟨864682, by decide⟩,⟨864723, by decide⟩,⟨864765, by decide⟩,⟨864769, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110373_864770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110373 ⟨864770, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110373
    ⟨864770, by decide⟩ (by decide) (![⟨864682, by decide⟩,⟨864723, by decide⟩,⟨864765, by decide⟩,⟨864769, by decide⟩]) unmarked_context_12_110373_864770 node_context_12_110373_864770
  intro a
  fin_cases a
  · exact context_13_441492_864682
  · exact context_13_441493_864723
  · exact context_13_441494_864765
  · exact context_13_441495_864769

theorem selected_cut_33580 : selected 8 ⟨864792, by decide⟩
    (prefixPartial 13 441496) = some ⟨13, 2, 0, 864792, 441496, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_441496_864792 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441496 ⟨864792, by decide⟩ :=
  accepted_of_selected 13 441496 ⟨864792, by decide⟩ ⟨13, 2, 0, 864792, 441496, 1293, 16384⟩
    (by decide) selected_cut_33580

theorem selected_cut_33581 : selected 8 ⟨864832, by decide⟩
    (prefixPartial 13 441497) = some ⟨13, 2, 0, 864832, 441497, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_441497_864832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441497 ⟨864832, by decide⟩ :=
  accepted_of_selected 13 441497 ⟨864832, by decide⟩ ⟨13, 2, 0, 864832, 441497, 2925, 16384⟩
    (by decide) selected_cut_33581

theorem selected_cut_33582 : selected 8 ⟨864853, by decide⟩
    (prefixPartial 13 441498) = some ⟨13, 2, 0, 864853, 441498, 1385, 16384⟩ := by
  decide +kernel

theorem context_13_441498_864853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441498 ⟨864853, by decide⟩ :=
  accepted_of_selected 13 441498 ⟨864853, by decide⟩ ⟨13, 2, 0, 864853, 441498, 1385, 16384⟩
    (by decide) selected_cut_33582

theorem selected_cut_33583 : selected 8 ⟨864862, by decide⟩
    (prefixPartial 13 441499) = some ⟨13, 2, 0, 864862, 441499, 761, 16384⟩ := by
  decide +kernel

theorem context_13_441499_864862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441499 ⟨864862, by decide⟩ :=
  accepted_of_selected 13 441499 ⟨864862, by decide⟩ ⟨13, 2, 0, 864862, 441499, 761, 16384⟩
    (by decide) selected_cut_33583

theorem unmarked_context_12_110374_864863 : frontier 9 ⟨864863, by decide⟩
    (prefixCache 12 110374) (prefixPartial 12 110374) = false := by
  decide +kernel

theorem node_context_12_110374_864863 : EJMOriginalGlobalDAGData.nodes 9 ⟨864863, by decide⟩ =
    .split (coordinate 12) (![⟨864792, by decide⟩,⟨864832, by decide⟩,⟨864853, by decide⟩,⟨864862, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110374_864863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110374 ⟨864863, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110374
    ⟨864863, by decide⟩ (by decide) (![⟨864792, by decide⟩,⟨864832, by decide⟩,⟨864853, by decide⟩,⟨864862, by decide⟩]) unmarked_context_12_110374_864863 node_context_12_110374_864863
  intro a
  fin_cases a
  · exact context_13_441496_864792
  · exact context_13_441497_864832
  · exact context_13_441498_864853
  · exact context_13_441499_864862

theorem selected_cut_33584 : selected 8 ⟨864888, by decide⟩
    (prefixPartial 13 441500) = some ⟨13, 2, 0, 864888, 441500, 1381, 16384⟩ := by
  decide +kernel

theorem context_13_441500_864888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441500 ⟨864888, by decide⟩ :=
  accepted_of_selected 13 441500 ⟨864888, by decide⟩ ⟨13, 2, 0, 864888, 441500, 1381, 16384⟩
    (by decide) selected_cut_33584

theorem selected_cut_33585 : selected 8 ⟨864945, by decide⟩
    (prefixPartial 13 441501) = some ⟨13, 2, 0, 864945, 441501, 3237, 16384⟩ := by
  decide +kernel

theorem context_13_441501_864945 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441501 ⟨864945, by decide⟩ :=
  accepted_of_selected 13 441501 ⟨864945, by decide⟩ ⟨13, 2, 0, 864945, 441501, 3237, 16384⟩
    (by decide) selected_cut_33585

theorem selected_cut_33586 : selected 8 ⟨864985, by decide⟩
    (prefixPartial 13 441502) = some ⟨13, 2, 0, 864985, 441502, 1721, 16384⟩ := by
  decide +kernel

theorem context_13_441502_864985 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441502 ⟨864985, by decide⟩ :=
  accepted_of_selected 13 441502 ⟨864985, by decide⟩ ⟨13, 2, 0, 864985, 441502, 1721, 16384⟩
    (by decide) selected_cut_33586

theorem selected_cut_33587 : selected 8 ⟨864989, by decide⟩
    (prefixPartial 13 441503) = some ⟨13, 2, 0, 864989, 441503, 669, 16384⟩ := by
  decide +kernel

theorem context_13_441503_864989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441503 ⟨864989, by decide⟩ :=
  accepted_of_selected 13 441503 ⟨864989, by decide⟩ ⟨13, 2, 0, 864989, 441503, 669, 16384⟩
    (by decide) selected_cut_33587

theorem unmarked_context_12_110375_864990 : frontier 9 ⟨864990, by decide⟩
    (prefixCache 12 110375) (prefixPartial 12 110375) = false := by
  decide +kernel

theorem node_context_12_110375_864990 : EJMOriginalGlobalDAGData.nodes 9 ⟨864990, by decide⟩ =
    .split (coordinate 12) (![⟨864888, by decide⟩,⟨864945, by decide⟩,⟨864985, by decide⟩,⟨864989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110375_864990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110375 ⟨864990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110375
    ⟨864990, by decide⟩ (by decide) (![⟨864888, by decide⟩,⟨864945, by decide⟩,⟨864985, by decide⟩,⟨864989, by decide⟩]) unmarked_context_12_110375_864990 node_context_12_110375_864990
  intro a
  fin_cases a
  · exact context_13_441500_864888
  · exact context_13_441501_864945
  · exact context_13_441502_864985
  · exact context_13_441503_864989

theorem unmarked_context_11_27593_864991 : frontier 10 ⟨864991, by decide⟩
    (prefixCache 11 27593) (prefixPartial 11 27593) = false := by
  decide +kernel

theorem node_context_11_27593_864991 : EJMOriginalGlobalDAGData.nodes 10 ⟨864991, by decide⟩ =
    .split (coordinate 11) (![⟨864648, by decide⟩,⟨864770, by decide⟩,⟨864863, by decide⟩,⟨864990, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27593_864991 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27593 ⟨864991, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27593
    ⟨864991, by decide⟩ (by decide) (![⟨864648, by decide⟩,⟨864770, by decide⟩,⟨864863, by decide⟩,⟨864990, by decide⟩]) unmarked_context_11_27593_864991 node_context_11_27593_864991
  intro a
  fin_cases a
  · exact context_12_110372_864648
  · exact context_12_110373_864770
  · exact context_12_110374_864863
  · exact context_12_110375_864990

theorem selected_cut_33588 : selected 8 ⟨865007, by decide⟩
    (prefixPartial 13 441504) = some ⟨13, 2, 0, 865007, 441504, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_441504_865007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441504 ⟨865007, by decide⟩ :=
  accepted_of_selected 13 441504 ⟨865007, by decide⟩ ⟨13, 2, 0, 865007, 441504, 1069, 16384⟩
    (by decide) selected_cut_33588

theorem selected_cut_33589 : selected 8 ⟨865056, by decide⟩
    (prefixPartial 13 441505) = some ⟨13, 2, 0, 865056, 441505, 3089, 16384⟩ := by
  decide +kernel

theorem context_13_441505_865056 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441505 ⟨865056, by decide⟩ :=
  accepted_of_selected 13 441505 ⟨865056, by decide⟩ ⟨13, 2, 0, 865056, 441505, 3089, 16384⟩
    (by decide) selected_cut_33589

theorem selected_cut_33590 : selected 8 ⟨865100, by decide⟩
    (prefixPartial 13 441506) = some ⟨13, 2, 0, 865100, 441506, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_441506_865100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441506 ⟨865100, by decide⟩ :=
  accepted_of_selected 13 441506 ⟨865100, by decide⟩ ⟨13, 2, 0, 865100, 441506, 1525, 16384⟩
    (by decide) selected_cut_33590

theorem selected_cut_33591 : selected 8 ⟨865104, by decide⟩
    (prefixPartial 13 441507) = some ⟨13, 2, 0, 865104, 441507, 609, 16384⟩ := by
  decide +kernel

theorem context_13_441507_865104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441507 ⟨865104, by decide⟩ :=
  accepted_of_selected 13 441507 ⟨865104, by decide⟩ ⟨13, 2, 0, 865104, 441507, 609, 16384⟩
    (by decide) selected_cut_33591

theorem unmarked_context_12_110376_865105 : frontier 9 ⟨865105, by decide⟩
    (prefixCache 12 110376) (prefixPartial 12 110376) = false := by
  decide +kernel

theorem node_context_12_110376_865105 : EJMOriginalGlobalDAGData.nodes 9 ⟨865105, by decide⟩ =
    .split (coordinate 12) (![⟨865007, by decide⟩,⟨865056, by decide⟩,⟨865100, by decide⟩,⟨865104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110376_865105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110376 ⟨865105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110376
    ⟨865105, by decide⟩ (by decide) (![⟨865007, by decide⟩,⟨865056, by decide⟩,⟨865100, by decide⟩,⟨865104, by decide⟩]) unmarked_context_12_110376_865105 node_context_12_110376_865105
  intro a
  fin_cases a
  · exact context_13_441504_865007
  · exact context_13_441505_865056
  · exact context_13_441506_865100
  · exact context_13_441507_865104

theorem selected_cut_33592 : selected 8 ⟨865124, by decide⟩
    (prefixPartial 13 441508) = some ⟨13, 2, 0, 865124, 441508, 1313, 16384⟩ := by
  decide +kernel

theorem context_13_441508_865124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441508 ⟨865124, by decide⟩ :=
  accepted_of_selected 13 441508 ⟨865124, by decide⟩ ⟨13, 2, 0, 865124, 441508, 1313, 16384⟩
    (by decide) selected_cut_33592

theorem selected_cut_33593 : selected 8 ⟨865171, by decide⟩
    (prefixPartial 13 441509) = some ⟨13, 2, 0, 865171, 441509, 2881, 16384⟩ := by
  decide +kernel

theorem context_13_441509_865171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441509 ⟨865171, by decide⟩ :=
  accepted_of_selected 13 441509 ⟨865171, by decide⟩ ⟨13, 2, 0, 865171, 441509, 2881, 16384⟩
    (by decide) selected_cut_33593

theorem selected_cut_33594 : selected 8 ⟨865210, by decide⟩
    (prefixPartial 13 441510) = some ⟨13, 2, 0, 865210, 441510, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_441510_865210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441510 ⟨865210, by decide⟩ :=
  accepted_of_selected 13 441510 ⟨865210, by decide⟩ ⟨13, 2, 0, 865210, 441510, 1725, 16384⟩
    (by decide) selected_cut_33594

theorem selected_cut_33595 : selected 8 ⟨865212, by decide⟩
    (prefixPartial 13 441511) = some ⟨13, 2, 0, 865212, 441511, 545, 16384⟩ := by
  decide +kernel

theorem context_13_441511_865212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441511 ⟨865212, by decide⟩ :=
  accepted_of_selected 13 441511 ⟨865212, by decide⟩ ⟨13, 2, 0, 865212, 441511, 545, 16384⟩
    (by decide) selected_cut_33595

theorem unmarked_context_12_110377_865213 : frontier 9 ⟨865213, by decide⟩
    (prefixCache 12 110377) (prefixPartial 12 110377) = false := by
  decide +kernel

theorem node_context_12_110377_865213 : EJMOriginalGlobalDAGData.nodes 9 ⟨865213, by decide⟩ =
    .split (coordinate 12) (![⟨865124, by decide⟩,⟨865171, by decide⟩,⟨865210, by decide⟩,⟨865212, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110377_865213 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110377 ⟨865213, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110377
    ⟨865213, by decide⟩ (by decide) (![⟨865124, by decide⟩,⟨865171, by decide⟩,⟨865210, by decide⟩,⟨865212, by decide⟩]) unmarked_context_12_110377_865213 node_context_12_110377_865213
  intro a
  fin_cases a
  · exact context_13_441508_865124
  · exact context_13_441509_865171
  · exact context_13_441510_865210
  · exact context_13_441511_865212

theorem selected_cut_33596 : selected 8 ⟨865226, by decide⟩
    (prefixPartial 13 441512) = some ⟨13, 2, 0, 865226, 441512, 829, 16384⟩ := by
  decide +kernel

theorem context_13_441512_865226 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441512 ⟨865226, by decide⟩ :=
  accepted_of_selected 13 441512 ⟨865226, by decide⟩ ⟨13, 2, 0, 865226, 441512, 829, 16384⟩
    (by decide) selected_cut_33596

theorem selected_cut_33597 : selected 8 ⟨865262, by decide⟩
    (prefixPartial 13 441513) = some ⟨13, 2, 0, 865262, 441513, 2745, 16384⟩ := by
  decide +kernel

theorem context_13_441513_865262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441513 ⟨865262, by decide⟩ :=
  accepted_of_selected 13 441513 ⟨865262, by decide⟩ ⟨13, 2, 0, 865262, 441513, 2745, 16384⟩
    (by decide) selected_cut_33597

theorem selected_cut_33598 : selected 8 ⟨865286, by decide⟩
    (prefixPartial 13 441514) = some ⟨13, 2, 0, 865286, 441514, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_441514_865286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441514 ⟨865286, by decide⟩ :=
  accepted_of_selected 13 441514 ⟨865286, by decide⟩ ⟨13, 2, 0, 865286, 441514, 1289, 16384⟩
    (by decide) selected_cut_33598

theorem selected_cut_33599 : selected 8 ⟨865291, by decide⟩
    (prefixPartial 13 441515) = some ⟨13, 2, 0, 865291, 441515, 561, 16384⟩ := by
  decide +kernel

theorem context_13_441515_865291 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441515 ⟨865291, by decide⟩ :=
  accepted_of_selected 13 441515 ⟨865291, by decide⟩ ⟨13, 2, 0, 865291, 441515, 561, 16384⟩
    (by decide) selected_cut_33599

theorem unmarked_context_12_110378_865292 : frontier 9 ⟨865292, by decide⟩
    (prefixCache 12 110378) (prefixPartial 12 110378) = false := by
  decide +kernel

theorem node_context_12_110378_865292 : EJMOriginalGlobalDAGData.nodes 9 ⟨865292, by decide⟩ =
    .split (coordinate 12) (![⟨865226, by decide⟩,⟨865262, by decide⟩,⟨865286, by decide⟩,⟨865291, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110378_865292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110378 ⟨865292, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110378
    ⟨865292, by decide⟩ (by decide) (![⟨865226, by decide⟩,⟨865262, by decide⟩,⟨865286, by decide⟩,⟨865291, by decide⟩]) unmarked_context_12_110378_865292 node_context_12_110378_865292
  intro a
  fin_cases a
  · exact context_13_441512_865226
  · exact context_13_441513_865262
  · exact context_13_441514_865286
  · exact context_13_441515_865291

theorem selected_cut_33600 : selected 8 ⟨865304, by decide⟩
    (prefixPartial 13 441516) = some ⟨13, 2, 0, 865304, 441516, 877, 16384⟩ := by
  decide +kernel

theorem context_13_441516_865304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441516 ⟨865304, by decide⟩ :=
  accepted_of_selected 13 441516 ⟨865304, by decide⟩ ⟨13, 2, 0, 865304, 441516, 877, 16384⟩
    (by decide) selected_cut_33600

theorem selected_cut_33601 : selected 8 ⟨865346, by decide⟩
    (prefixPartial 13 441517) = some ⟨13, 2, 0, 865346, 441517, 3097, 16384⟩ := by
  decide +kernel

theorem context_13_441517_865346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441517 ⟨865346, by decide⟩ :=
  accepted_of_selected 13 441517 ⟨865346, by decide⟩ ⟨13, 2, 0, 865346, 441517, 3097, 16384⟩
    (by decide) selected_cut_33601

theorem selected_cut_33602 : selected 8 ⟨865381, by decide⟩
    (prefixPartial 13 441518) = some ⟨13, 2, 0, 865381, 441518, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_441518_865381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441518 ⟨865381, by decide⟩ :=
  accepted_of_selected 13 441518 ⟨865381, by decide⟩ ⟨13, 2, 0, 865381, 441518, 1601, 16384⟩
    (by decide) selected_cut_33602

theorem selected_cut_33603 : selected 8 ⟨865385, by decide⟩
    (prefixPartial 13 441519) = some ⟨13, 2, 0, 865385, 441519, 521, 16384⟩ := by
  decide +kernel

theorem context_13_441519_865385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 441519 ⟨865385, by decide⟩ :=
  accepted_of_selected 13 441519 ⟨865385, by decide⟩ ⟨13, 2, 0, 865385, 441519, 521, 16384⟩
    (by decide) selected_cut_33603

theorem unmarked_context_12_110379_865386 : frontier 9 ⟨865386, by decide⟩
    (prefixCache 12 110379) (prefixPartial 12 110379) = false := by
  decide +kernel

theorem node_context_12_110379_865386 : EJMOriginalGlobalDAGData.nodes 9 ⟨865386, by decide⟩ =
    .split (coordinate 12) (![⟨865304, by decide⟩,⟨865346, by decide⟩,⟨865381, by decide⟩,⟨865385, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_110379_865386 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 110379 ⟨865386, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 110379
    ⟨865386, by decide⟩ (by decide) (![⟨865304, by decide⟩,⟨865346, by decide⟩,⟨865381, by decide⟩,⟨865385, by decide⟩]) unmarked_context_12_110379_865386 node_context_12_110379_865386
  intro a
  fin_cases a
  · exact context_13_441516_865304
  · exact context_13_441517_865346
  · exact context_13_441518_865381
  · exact context_13_441519_865385

theorem unmarked_context_11_27594_865387 : frontier 10 ⟨865387, by decide⟩
    (prefixCache 11 27594) (prefixPartial 11 27594) = false := by
  decide +kernel

theorem node_context_11_27594_865387 : EJMOriginalGlobalDAGData.nodes 10 ⟨865387, by decide⟩ =
    .split (coordinate 11) (![⟨865105, by decide⟩,⟨865213, by decide⟩,⟨865292, by decide⟩,⟨865386, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_27594_865387 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 27594 ⟨865387, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 27594
    ⟨865387, by decide⟩ (by decide) (![⟨865105, by decide⟩,⟨865213, by decide⟩,⟨865292, by decide⟩,⟨865386, by decide⟩]) unmarked_context_11_27594_865387 node_context_11_27594_865387
  intro a
  fin_cases a
  · exact context_12_110376_865105
  · exact context_12_110377_865213
  · exact context_12_110378_865292
  · exact context_12_110379_865386

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
