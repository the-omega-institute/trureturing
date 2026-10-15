/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover045
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_04418 : selected 8 ⟨141317, by decide⟩
    (prefixPartial 13 73832) = some ⟨13, 2, 0, 141317, 73832, 1845, 16384⟩ := by
  decide +kernel

theorem context_13_73832_141317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73832 ⟨141317, by decide⟩ :=
  accepted_of_selected 13 73832 ⟨141317, by decide⟩ ⟨13, 2, 0, 141317, 73832, 1845, 16384⟩
    (by decide) selected_cut_04418

theorem selected_cut_04419 : selected 8 ⟨141382, by decide⟩
    (prefixPartial 13 73833) = some ⟨13, 2, 0, 141382, 73833, 2961, 16384⟩ := by
  decide +kernel

theorem context_13_73833_141382 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73833 ⟨141382, by decide⟩ :=
  accepted_of_selected 13 73833 ⟨141382, by decide⟩ ⟨13, 2, 0, 141382, 73833, 2961, 16384⟩
    (by decide) selected_cut_04419

theorem selected_cut_04420 : selected 8 ⟨141404, by decide⟩
    (prefixPartial 13 73834) = some ⟨13, 2, 0, 141404, 73834, 1425, 16384⟩ := by
  decide +kernel

theorem context_13_73834_141404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73834 ⟨141404, by decide⟩ :=
  accepted_of_selected 13 73834 ⟨141404, by decide⟩ ⟨13, 2, 0, 141404, 73834, 1425, 16384⟩
    (by decide) selected_cut_04420

theorem selected_cut_04421 : selected 8 ⟨141412, by decide⟩
    (prefixPartial 13 73835) = some ⟨13, 2, 0, 141412, 73835, 1069, 16384⟩ := by
  decide +kernel

theorem context_13_73835_141412 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73835 ⟨141412, by decide⟩ :=
  accepted_of_selected 13 73835 ⟨141412, by decide⟩ ⟨13, 2, 0, 141412, 73835, 1069, 16384⟩
    (by decide) selected_cut_04421

theorem unmarked_context_12_18458_141413 : frontier 9 ⟨141413, by decide⟩
    (prefixCache 12 18458) (prefixPartial 12 18458) = false := by
  decide +kernel

theorem node_context_12_18458_141413 : EJMOriginalGlobalDAGData.nodes 9 ⟨141413, by decide⟩ =
    .split (coordinate 12) (![⟨141317, by decide⟩,⟨141382, by decide⟩,⟨141404, by decide⟩,⟨141412, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18458_141413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18458 ⟨141413, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18458
    ⟨141413, by decide⟩ (by decide) (![⟨141317, by decide⟩,⟨141382, by decide⟩,⟨141404, by decide⟩,⟨141412, by decide⟩]) unmarked_context_12_18458_141413 node_context_12_18458_141413
  intro a
  fin_cases a
  · exact context_13_73832_141317
  · exact context_13_73833_141382
  · exact context_13_73834_141404
  · exact context_13_73835_141412

theorem selected_cut_04422 : selected 8 ⟨141451, by decide⟩
    (prefixPartial 13 73836) = some ⟨13, 2, 0, 141451, 73836, 2105, 16384⟩ := by
  decide +kernel

theorem context_13_73836_141451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73836 ⟨141451, by decide⟩ :=
  accepted_of_selected 13 73836 ⟨141451, by decide⟩ ⟨13, 2, 0, 141451, 73836, 2105, 16384⟩
    (by decide) selected_cut_04422

theorem selected_cut_04423 : selected 8 ⟨141544, by decide⟩
    (prefixPartial 13 73837) = some ⟨13, 2, 0, 141544, 73837, 3397, 16384⟩ := by
  decide +kernel

theorem context_13_73837_141544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73837 ⟨141544, by decide⟩ :=
  accepted_of_selected 13 73837 ⟨141544, by decide⟩ ⟨13, 2, 0, 141544, 73837, 3397, 16384⟩
    (by decide) selected_cut_04423

theorem selected_cut_04424 : selected 8 ⟨141567, by decide⟩
    (prefixPartial 13 73838) = some ⟨13, 2, 0, 141567, 73838, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_73838_141567 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73838 ⟨141567, by decide⟩ :=
  accepted_of_selected 13 73838 ⟨141567, by decide⟩ ⟨13, 2, 0, 141567, 73838, 1477, 16384⟩
    (by decide) selected_cut_04424

theorem selected_cut_04425 : selected 8 ⟨141577, by decide⟩
    (prefixPartial 13 73839) = some ⟨13, 2, 0, 141577, 73839, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_73839_141577 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73839 ⟨141577, by decide⟩ :=
  accepted_of_selected 13 73839 ⟨141577, by decide⟩ ⟨13, 2, 0, 141577, 73839, 1001, 16384⟩
    (by decide) selected_cut_04425

theorem unmarked_context_12_18459_141578 : frontier 9 ⟨141578, by decide⟩
    (prefixCache 12 18459) (prefixPartial 12 18459) = false := by
  decide +kernel

theorem node_context_12_18459_141578 : EJMOriginalGlobalDAGData.nodes 9 ⟨141578, by decide⟩ =
    .split (coordinate 12) (![⟨141451, by decide⟩,⟨141544, by decide⟩,⟨141567, by decide⟩,⟨141577, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18459_141578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18459 ⟨141578, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18459
    ⟨141578, by decide⟩ (by decide) (![⟨141451, by decide⟩,⟨141544, by decide⟩,⟨141567, by decide⟩,⟨141577, by decide⟩]) unmarked_context_12_18459_141578 node_context_12_18459_141578
  intro a
  fin_cases a
  · exact context_13_73836_141451
  · exact context_13_73837_141544
  · exact context_13_73838_141567
  · exact context_13_73839_141577

theorem unmarked_context_11_4614_141579 : frontier 10 ⟨141579, by decide⟩
    (prefixCache 11 4614) (prefixPartial 11 4614) = false := by
  decide +kernel

theorem node_context_11_4614_141579 : EJMOriginalGlobalDAGData.nodes 10 ⟨141579, by decide⟩ =
    .split (coordinate 11) (![⟨141162, by decide⟩,⟨141280, by decide⟩,⟨141413, by decide⟩,⟨141578, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4614_141579 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4614 ⟨141579, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4614
    ⟨141579, by decide⟩ (by decide) (![⟨141162, by decide⟩,⟨141280, by decide⟩,⟨141413, by decide⟩,⟨141578, by decide⟩]) unmarked_context_11_4614_141579 node_context_11_4614_141579
  intro a
  fin_cases a
  · exact context_12_18456_141162
  · exact context_12_18457_141280
  · exact context_12_18458_141413
  · exact context_12_18459_141578

theorem selected_cut_04426 : selected 8 ⟨141613, by decide⟩
    (prefixPartial 13 73840) = some ⟨13, 2, 0, 141613, 73840, 1365, 16384⟩ := by
  decide +kernel

theorem context_13_73840_141613 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73840 ⟨141613, by decide⟩ :=
  accepted_of_selected 13 73840 ⟨141613, by decide⟩ ⟨13, 2, 0, 141613, 73840, 1365, 16384⟩
    (by decide) selected_cut_04426

theorem selected_cut_04427 : selected 8 ⟨141702, by decide⟩
    (prefixPartial 13 73841) = some ⟨13, 2, 0, 141702, 73841, 3001, 16384⟩ := by
  decide +kernel

theorem context_13_73841_141702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73841 ⟨141702, by decide⟩ :=
  accepted_of_selected 13 73841 ⟨141702, by decide⟩ ⟨13, 2, 0, 141702, 73841, 3001, 16384⟩
    (by decide) selected_cut_04427

theorem selected_cut_04428 : selected 8 ⟨141724, by decide⟩
    (prefixPartial 13 73842) = some ⟨13, 2, 0, 141724, 73842, 1289, 16384⟩ := by
  decide +kernel

theorem context_13_73842_141724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73842 ⟨141724, by decide⟩ :=
  accepted_of_selected 13 73842 ⟨141724, by decide⟩ ⟨13, 2, 0, 141724, 73842, 1289, 16384⟩
    (by decide) selected_cut_04428

theorem selected_cut_04429 : selected 8 ⟨141735, by decide⟩
    (prefixPartial 13 73843) = some ⟨13, 2, 0, 141735, 73843, 857, 16384⟩ := by
  decide +kernel

theorem context_13_73843_141735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73843 ⟨141735, by decide⟩ :=
  accepted_of_selected 13 73843 ⟨141735, by decide⟩ ⟨13, 2, 0, 141735, 73843, 857, 16384⟩
    (by decide) selected_cut_04429

theorem unmarked_context_12_18460_141736 : frontier 9 ⟨141736, by decide⟩
    (prefixCache 12 18460) (prefixPartial 12 18460) = false := by
  decide +kernel

theorem node_context_12_18460_141736 : EJMOriginalGlobalDAGData.nodes 9 ⟨141736, by decide⟩ =
    .split (coordinate 12) (![⟨141613, by decide⟩,⟨141702, by decide⟩,⟨141724, by decide⟩,⟨141735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18460_141736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18460 ⟨141736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18460
    ⟨141736, by decide⟩ (by decide) (![⟨141613, by decide⟩,⟨141702, by decide⟩,⟨141724, by decide⟩,⟨141735, by decide⟩]) unmarked_context_12_18460_141736 node_context_12_18460_141736
  intro a
  fin_cases a
  · exact context_13_73840_141613
  · exact context_13_73841_141702
  · exact context_13_73842_141724
  · exact context_13_73843_141735

theorem selected_cut_04430 : selected 8 ⟨141776, by decide⟩
    (prefixPartial 13 73844) = some ⟨13, 2, 0, 141776, 73844, 1977, 16384⟩ := by
  decide +kernel

theorem context_13_73844_141776 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73844 ⟨141776, by decide⟩ :=
  accepted_of_selected 13 73844 ⟨141776, by decide⟩ ⟨13, 2, 0, 141776, 73844, 1977, 16384⟩
    (by decide) selected_cut_04430

theorem selected_cut_04431 : selected 8 ⟨141840, by decide⟩
    (prefixPartial 13 73845) = some ⟨13, 2, 0, 141840, 73845, 2733, 16384⟩ := by
  decide +kernel

theorem context_13_73845_141840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73845 ⟨141840, by decide⟩ :=
  accepted_of_selected 13 73845 ⟨141840, by decide⟩ ⟨13, 2, 0, 141840, 73845, 2733, 16384⟩
    (by decide) selected_cut_04431

theorem selected_cut_04432 : selected 8 ⟨141866, by decide⟩
    (prefixPartial 13 73846) = some ⟨13, 2, 0, 141866, 73846, 1485, 16384⟩ := by
  decide +kernel

theorem context_13_73846_141866 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73846 ⟨141866, by decide⟩ :=
  accepted_of_selected 13 73846 ⟨141866, by decide⟩ ⟨13, 2, 0, 141866, 73846, 1485, 16384⟩
    (by decide) selected_cut_04432

theorem selected_cut_04433 : selected 8 ⟨141880, by decide⟩
    (prefixPartial 13 73847) = some ⟨13, 2, 0, 141880, 73847, 897, 16384⟩ := by
  decide +kernel

theorem context_13_73847_141880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73847 ⟨141880, by decide⟩ :=
  accepted_of_selected 13 73847 ⟨141880, by decide⟩ ⟨13, 2, 0, 141880, 73847, 897, 16384⟩
    (by decide) selected_cut_04433

theorem unmarked_context_12_18461_141881 : frontier 9 ⟨141881, by decide⟩
    (prefixCache 12 18461) (prefixPartial 12 18461) = false := by
  decide +kernel

theorem node_context_12_18461_141881 : EJMOriginalGlobalDAGData.nodes 9 ⟨141881, by decide⟩ =
    .split (coordinate 12) (![⟨141776, by decide⟩,⟨141840, by decide⟩,⟨141866, by decide⟩,⟨141880, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18461_141881 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18461 ⟨141881, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18461
    ⟨141881, by decide⟩ (by decide) (![⟨141776, by decide⟩,⟨141840, by decide⟩,⟨141866, by decide⟩,⟨141880, by decide⟩]) unmarked_context_12_18461_141881 node_context_12_18461_141881
  intro a
  fin_cases a
  · exact context_13_73844_141776
  · exact context_13_73845_141840
  · exact context_13_73846_141866
  · exact context_13_73847_141880

theorem selected_cut_04434 : selected 8 ⟨141921, by decide⟩
    (prefixPartial 13 73848) = some ⟨13, 2, 0, 141921, 73848, 2013, 16384⟩ := by
  decide +kernel

theorem context_13_73848_141921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73848 ⟨141921, by decide⟩ :=
  accepted_of_selected 13 73848 ⟨141921, by decide⟩ ⟨13, 2, 0, 141921, 73848, 2013, 16384⟩
    (by decide) selected_cut_04434

theorem selected_cut_04435 : selected 8 ⟨142002, by decide⟩
    (prefixPartial 13 73849) = some ⟨13, 2, 0, 142002, 73849, 3193, 16384⟩ := by
  decide +kernel

theorem context_13_73849_142002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73849 ⟨142002, by decide⟩ :=
  accepted_of_selected 13 73849 ⟨142002, by decide⟩ ⟨13, 2, 0, 142002, 73849, 3193, 16384⟩
    (by decide) selected_cut_04435

theorem selected_cut_04436 : selected 8 ⟨142019, by decide⟩
    (prefixPartial 13 73850) = some ⟨13, 2, 0, 142019, 73850, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_73850_142019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73850 ⟨142019, by decide⟩ :=
  accepted_of_selected 13 73850 ⟨142019, by decide⟩ ⟨13, 2, 0, 142019, 73850, 1413, 16384⟩
    (by decide) selected_cut_04436

theorem selected_cut_04437 : selected 8 ⟨142032, by decide⟩
    (prefixPartial 13 73851) = some ⟨13, 2, 0, 142032, 73851, 953, 16384⟩ := by
  decide +kernel

theorem context_13_73851_142032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73851 ⟨142032, by decide⟩ :=
  accepted_of_selected 13 73851 ⟨142032, by decide⟩ ⟨13, 2, 0, 142032, 73851, 953, 16384⟩
    (by decide) selected_cut_04437

theorem unmarked_context_12_18462_142033 : frontier 9 ⟨142033, by decide⟩
    (prefixCache 12 18462) (prefixPartial 12 18462) = false := by
  decide +kernel

theorem node_context_12_18462_142033 : EJMOriginalGlobalDAGData.nodes 9 ⟨142033, by decide⟩ =
    .split (coordinate 12) (![⟨141921, by decide⟩,⟨142002, by decide⟩,⟨142019, by decide⟩,⟨142032, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18462_142033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18462 ⟨142033, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18462
    ⟨142033, by decide⟩ (by decide) (![⟨141921, by decide⟩,⟨142002, by decide⟩,⟨142019, by decide⟩,⟨142032, by decide⟩]) unmarked_context_12_18462_142033 node_context_12_18462_142033
  intro a
  fin_cases a
  · exact context_13_73848_141921
  · exact context_13_73849_142002
  · exact context_13_73850_142019
  · exact context_13_73851_142032

theorem selected_cut_04438 : selected 8 ⟨142072, by decide⟩
    (prefixPartial 13 73852) = some ⟨13, 2, 0, 142072, 73852, 1685, 16384⟩ := by
  decide +kernel

theorem context_13_73852_142072 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73852 ⟨142072, by decide⟩ :=
  accepted_of_selected 13 73852 ⟨142072, by decide⟩ ⟨13, 2, 0, 142072, 73852, 1685, 16384⟩
    (by decide) selected_cut_04438

theorem selected_cut_04439 : selected 8 ⟨142146, by decide⟩
    (prefixPartial 13 73853) = some ⟨13, 2, 0, 142146, 73853, 2833, 16384⟩ := by
  decide +kernel

theorem context_13_73853_142146 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73853 ⟨142146, by decide⟩ :=
  accepted_of_selected 13 73853 ⟨142146, by decide⟩ ⟨13, 2, 0, 142146, 73853, 2833, 16384⟩
    (by decide) selected_cut_04439

theorem selected_cut_04440 : selected 8 ⟨142166, by decide⟩
    (prefixPartial 13 73854) = some ⟨13, 2, 0, 142166, 73854, 1325, 16384⟩ := by
  decide +kernel

theorem context_13_73854_142166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73854 ⟨142166, by decide⟩ :=
  accepted_of_selected 13 73854 ⟨142166, by decide⟩ ⟨13, 2, 0, 142166, 73854, 1325, 16384⟩
    (by decide) selected_cut_04440

theorem selected_cut_04441 : selected 8 ⟨142177, by decide⟩
    (prefixPartial 13 73855) = some ⟨13, 2, 0, 142177, 73855, 757, 16384⟩ := by
  decide +kernel

theorem context_13_73855_142177 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73855 ⟨142177, by decide⟩ :=
  accepted_of_selected 13 73855 ⟨142177, by decide⟩ ⟨13, 2, 0, 142177, 73855, 757, 16384⟩
    (by decide) selected_cut_04441

theorem unmarked_context_12_18463_142178 : frontier 9 ⟨142178, by decide⟩
    (prefixCache 12 18463) (prefixPartial 12 18463) = false := by
  decide +kernel

theorem node_context_12_18463_142178 : EJMOriginalGlobalDAGData.nodes 9 ⟨142178, by decide⟩ =
    .split (coordinate 12) (![⟨142072, by decide⟩,⟨142146, by decide⟩,⟨142166, by decide⟩,⟨142177, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18463_142178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18463 ⟨142178, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18463
    ⟨142178, by decide⟩ (by decide) (![⟨142072, by decide⟩,⟨142146, by decide⟩,⟨142166, by decide⟩,⟨142177, by decide⟩]) unmarked_context_12_18463_142178 node_context_12_18463_142178
  intro a
  fin_cases a
  · exact context_13_73852_142072
  · exact context_13_73853_142146
  · exact context_13_73854_142166
  · exact context_13_73855_142177

theorem unmarked_context_11_4615_142179 : frontier 10 ⟨142179, by decide⟩
    (prefixCache 11 4615) (prefixPartial 11 4615) = false := by
  decide +kernel

theorem node_context_11_4615_142179 : EJMOriginalGlobalDAGData.nodes 10 ⟨142179, by decide⟩ =
    .split (coordinate 11) (![⟨141736, by decide⟩,⟨141881, by decide⟩,⟨142033, by decide⟩,⟨142178, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4615_142179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4615 ⟨142179, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4615
    ⟨142179, by decide⟩ (by decide) (![⟨141736, by decide⟩,⟨141881, by decide⟩,⟨142033, by decide⟩,⟨142178, by decide⟩]) unmarked_context_11_4615_142179 node_context_11_4615_142179
  intro a
  fin_cases a
  · exact context_12_18460_141736
  · exact context_12_18461_141881
  · exact context_12_18462_142033
  · exact context_12_18463_142178

theorem unmarked_context_10_1153_142180 : frontier 11 ⟨142180, by decide⟩
    (prefixCache 10 1153) (prefixPartial 10 1153) = false := by
  decide +kernel

theorem node_context_10_1153_142180 : EJMOriginalGlobalDAGData.nodes 11 ⟨142180, by decide⟩ =
    .split (coordinate 10) (![⟨140417, by decide⟩,⟨141032, by decide⟩,⟨141579, by decide⟩,⟨142179, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1153_142180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1153 ⟨142180, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1153
    ⟨142180, by decide⟩ (by decide) (![⟨140417, by decide⟩,⟨141032, by decide⟩,⟨141579, by decide⟩,⟨142179, by decide⟩]) unmarked_context_10_1153_142180 node_context_10_1153_142180
  intro a
  fin_cases a
  · exact context_11_4612_140417
  · exact context_11_4613_141032
  · exact context_11_4614_141579
  · exact context_11_4615_142179

theorem selected_cut_04442 : selected 9 ⟨118489, by decide⟩
    (prefixPartial 12 18464) = some ⟨12, 1, 0, 118489, 18464, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18464_118489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18464 ⟨118489, by decide⟩ :=
  accepted_of_selected 12 18464 ⟨118489, by decide⟩ ⟨12, 1, 0, 118489, 18464, 1, 65536⟩
    (by decide) selected_cut_04442

theorem selected_cut_04443 : selected 9 ⟨142343, by decide⟩
    (prefixPartial 12 18465) = some ⟨12, 2, 0, 142343, 18465, 3837, 65536⟩ := by
  decide +kernel

theorem context_12_18465_142343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18465 ⟨142343, by decide⟩ :=
  accepted_of_selected 12 18465 ⟨142343, by decide⟩ ⟨12, 2, 0, 142343, 18465, 3837, 65536⟩
    (by decide) selected_cut_04443

theorem selected_cut_04444 : selected 9 ⟨142344, by decide⟩
    (prefixPartial 12 18466) = some ⟨12, 1, 0, 142344, 18466, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18466_142344 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18466 ⟨142344, by decide⟩ :=
  accepted_of_selected 12 18466 ⟨142344, by decide⟩ ⟨12, 1, 0, 142344, 18466, 1, 65536⟩
    (by decide) selected_cut_04444

theorem selected_cut_04445 : selected 8 ⟨142402, by decide⟩
    (prefixPartial 13 73868) = some ⟨13, 2, 0, 142402, 73868, 1753, 16384⟩ := by
  decide +kernel

theorem context_13_73868_142402 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73868 ⟨142402, by decide⟩ :=
  accepted_of_selected 13 73868 ⟨142402, by decide⟩ ⟨13, 2, 0, 142402, 73868, 1753, 16384⟩
    (by decide) selected_cut_04445

theorem selected_cut_04446 : selected 8 ⟨142509, by decide⟩
    (prefixPartial 13 73869) = some ⟨13, 2, 0, 142509, 73869, 2673, 16384⟩ := by
  decide +kernel

theorem context_13_73869_142509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73869 ⟨142509, by decide⟩ :=
  accepted_of_selected 13 73869 ⟨142509, by decide⟩ ⟨13, 2, 0, 142509, 73869, 2673, 16384⟩
    (by decide) selected_cut_04446

theorem selected_cut_04447 : selected 8 ⟨142527, by decide⟩
    (prefixPartial 13 73870) = some ⟨13, 2, 0, 142527, 73870, 1081, 16384⟩ := by
  decide +kernel

theorem context_13_73870_142527 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73870 ⟨142527, by decide⟩ :=
  accepted_of_selected 13 73870 ⟨142527, by decide⟩ ⟨13, 2, 0, 142527, 73870, 1081, 16384⟩
    (by decide) selected_cut_04447

theorem selected_cut_04448 : selected 8 ⟨142545, by decide⟩
    (prefixPartial 13 73871) = some ⟨13, 2, 0, 142545, 73871, 685, 16384⟩ := by
  decide +kernel

theorem context_13_73871_142545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73871 ⟨142545, by decide⟩ :=
  accepted_of_selected 13 73871 ⟨142545, by decide⟩ ⟨13, 2, 0, 142545, 73871, 685, 16384⟩
    (by decide) selected_cut_04448

theorem unmarked_context_12_18467_142546 : frontier 9 ⟨142546, by decide⟩
    (prefixCache 12 18467) (prefixPartial 12 18467) = false := by
  decide +kernel

theorem node_context_12_18467_142546 : EJMOriginalGlobalDAGData.nodes 9 ⟨142546, by decide⟩ =
    .split (coordinate 12) (![⟨142402, by decide⟩,⟨142509, by decide⟩,⟨142527, by decide⟩,⟨142545, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18467_142546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18467 ⟨142546, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18467
    ⟨142546, by decide⟩ (by decide) (![⟨142402, by decide⟩,⟨142509, by decide⟩,⟨142527, by decide⟩,⟨142545, by decide⟩]) unmarked_context_12_18467_142546 node_context_12_18467_142546
  intro a
  fin_cases a
  · exact context_13_73868_142402
  · exact context_13_73869_142509
  · exact context_13_73870_142527
  · exact context_13_73871_142545

theorem unmarked_context_11_4616_142547 : frontier 10 ⟨142547, by decide⟩
    (prefixCache 11 4616) (prefixPartial 11 4616) = false := by
  decide +kernel

theorem node_context_11_4616_142547 : EJMOriginalGlobalDAGData.nodes 10 ⟨142547, by decide⟩ =
    .split (coordinate 11) (![⟨118489, by decide⟩,⟨142343, by decide⟩,⟨142344, by decide⟩,⟨142546, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4616_142547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4616 ⟨142547, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4616
    ⟨142547, by decide⟩ (by decide) (![⟨118489, by decide⟩,⟨142343, by decide⟩,⟨142344, by decide⟩,⟨142546, by decide⟩]) unmarked_context_11_4616_142547 node_context_11_4616_142547
  intro a
  fin_cases a
  · exact context_12_18464_118489
  · exact context_12_18465_142343
  · exact context_12_18466_142344
  · exact context_12_18467_142546

theorem selected_cut_04449 : selected 9 ⟨118489, by decide⟩
    (prefixPartial 12 18468) = some ⟨12, 1, 0, 118489, 18468, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18468_118489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18468 ⟨118489, by decide⟩ :=
  accepted_of_selected 12 18468 ⟨118489, by decide⟩ ⟨12, 1, 0, 118489, 18468, 1, 65536⟩
    (by decide) selected_cut_04449

theorem selected_cut_04450 : selected 8 ⟨142582, by decide⟩
    (prefixPartial 13 73876) = some ⟨13, 2, 0, 142582, 73876, 1337, 16384⟩ := by
  decide +kernel

theorem context_13_73876_142582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73876 ⟨142582, by decide⟩ :=
  accepted_of_selected 13 73876 ⟨142582, by decide⟩ ⟨13, 2, 0, 142582, 73876, 1337, 16384⟩
    (by decide) selected_cut_04450

theorem selected_cut_04451 : selected 8 ⟨142652, by decide⟩
    (prefixPartial 13 73877) = some ⟨13, 2, 0, 142652, 73877, 2261, 16384⟩ := by
  decide +kernel

theorem context_13_73877_142652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73877 ⟨142652, by decide⟩ :=
  accepted_of_selected 13 73877 ⟨142652, by decide⟩ ⟨13, 2, 0, 142652, 73877, 2261, 16384⟩
    (by decide) selected_cut_04451

theorem selected_cut_04452 : selected 8 ⟨142673, by decide⟩
    (prefixPartial 13 73878) = some ⟨13, 2, 0, 142673, 73878, 1277, 16384⟩ := by
  decide +kernel

theorem context_13_73878_142673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73878 ⟨142673, by decide⟩ :=
  accepted_of_selected 13 73878 ⟨142673, by decide⟩ ⟨13, 2, 0, 142673, 73878, 1277, 16384⟩
    (by decide) selected_cut_04452

theorem selected_cut_04453 : selected 8 ⟨142686, by decide⟩
    (prefixPartial 13 73879) = some ⟨13, 2, 0, 142686, 73879, 861, 16384⟩ := by
  decide +kernel

theorem context_13_73879_142686 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73879 ⟨142686, by decide⟩ :=
  accepted_of_selected 13 73879 ⟨142686, by decide⟩ ⟨13, 2, 0, 142686, 73879, 861, 16384⟩
    (by decide) selected_cut_04453

theorem unmarked_context_12_18469_142687 : frontier 9 ⟨142687, by decide⟩
    (prefixCache 12 18469) (prefixPartial 12 18469) = false := by
  decide +kernel

theorem node_context_12_18469_142687 : EJMOriginalGlobalDAGData.nodes 9 ⟨142687, by decide⟩ =
    .split (coordinate 12) (![⟨142582, by decide⟩,⟨142652, by decide⟩,⟨142673, by decide⟩,⟨142686, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18469_142687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18469 ⟨142687, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18469
    ⟨142687, by decide⟩ (by decide) (![⟨142582, by decide⟩,⟨142652, by decide⟩,⟨142673, by decide⟩,⟨142686, by decide⟩]) unmarked_context_12_18469_142687 node_context_12_18469_142687
  intro a
  fin_cases a
  · exact context_13_73876_142582
  · exact context_13_73877_142652
  · exact context_13_73878_142673
  · exact context_13_73879_142686

theorem selected_cut_04454 : selected 8 ⟨142721, by decide⟩
    (prefixPartial 13 73880) = some ⟨13, 2, 0, 142721, 73880, 1501, 16384⟩ := by
  decide +kernel

theorem context_13_73880_142721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73880 ⟨142721, by decide⟩ :=
  accepted_of_selected 13 73880 ⟨142721, by decide⟩ ⟨13, 2, 0, 142721, 73880, 1501, 16384⟩
    (by decide) selected_cut_04454

theorem selected_cut_04455 : selected 8 ⟨142803, by decide⟩
    (prefixPartial 13 73881) = some ⟨13, 2, 0, 142803, 73881, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_73881_142803 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73881 ⟨142803, by decide⟩ :=
  accepted_of_selected 13 73881 ⟨142803, by decide⟩ ⟨13, 2, 0, 142803, 73881, 2689, 16384⟩
    (by decide) selected_cut_04455

theorem selected_cut_04456 : selected 8 ⟨142820, by decide⟩
    (prefixPartial 13 73882) = some ⟨13, 2, 0, 142820, 73882, 1245, 16384⟩ := by
  decide +kernel

theorem context_13_73882_142820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73882 ⟨142820, by decide⟩ :=
  accepted_of_selected 13 73882 ⟨142820, by decide⟩ ⟨13, 2, 0, 142820, 73882, 1245, 16384⟩
    (by decide) selected_cut_04456

theorem selected_cut_04457 : selected 8 ⟨142830, by decide⟩
    (prefixPartial 13 73883) = some ⟨13, 2, 0, 142830, 73883, 897, 16384⟩ := by
  decide +kernel

theorem context_13_73883_142830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73883 ⟨142830, by decide⟩ :=
  accepted_of_selected 13 73883 ⟨142830, by decide⟩ ⟨13, 2, 0, 142830, 73883, 897, 16384⟩
    (by decide) selected_cut_04457

theorem unmarked_context_12_18470_142831 : frontier 9 ⟨142831, by decide⟩
    (prefixCache 12 18470) (prefixPartial 12 18470) = false := by
  decide +kernel

theorem node_context_12_18470_142831 : EJMOriginalGlobalDAGData.nodes 9 ⟨142831, by decide⟩ =
    .split (coordinate 12) (![⟨142721, by decide⟩,⟨142803, by decide⟩,⟨142820, by decide⟩,⟨142830, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18470_142831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18470 ⟨142831, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18470
    ⟨142831, by decide⟩ (by decide) (![⟨142721, by decide⟩,⟨142803, by decide⟩,⟨142820, by decide⟩,⟨142830, by decide⟩]) unmarked_context_12_18470_142831 node_context_12_18470_142831
  intro a
  fin_cases a
  · exact context_13_73880_142721
  · exact context_13_73881_142803
  · exact context_13_73882_142820
  · exact context_13_73883_142830

theorem selected_cut_04458 : selected 8 ⟨142861, by decide⟩
    (prefixPartial 13 73884) = some ⟨13, 2, 0, 142861, 73884, 1489, 16384⟩ := by
  decide +kernel

theorem context_13_73884_142861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73884 ⟨142861, by decide⟩ :=
  accepted_of_selected 13 73884 ⟨142861, by decide⟩ ⟨13, 2, 0, 142861, 73884, 1489, 16384⟩
    (by decide) selected_cut_04458

theorem selected_cut_04459 : selected 8 ⟨142934, by decide⟩
    (prefixPartial 13 73885) = some ⟨13, 2, 0, 142934, 73885, 2621, 16384⟩ := by
  decide +kernel

theorem context_13_73885_142934 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73885 ⟨142934, by decide⟩ :=
  accepted_of_selected 13 73885 ⟨142934, by decide⟩ ⟨13, 2, 0, 142934, 73885, 2621, 16384⟩
    (by decide) selected_cut_04459

theorem selected_cut_04460 : selected 8 ⟨142951, by decide⟩
    (prefixPartial 13 73886) = some ⟨13, 2, 0, 142951, 73886, 1193, 16384⟩ := by
  decide +kernel

theorem context_13_73886_142951 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73886 ⟨142951, by decide⟩ :=
  accepted_of_selected 13 73886 ⟨142951, by decide⟩ ⟨13, 2, 0, 142951, 73886, 1193, 16384⟩
    (by decide) selected_cut_04460

theorem selected_cut_04461 : selected 8 ⟨142966, by decide⟩
    (prefixPartial 13 73887) = some ⟨13, 2, 0, 142966, 73887, 829, 16384⟩ := by
  decide +kernel

theorem context_13_73887_142966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73887 ⟨142966, by decide⟩ :=
  accepted_of_selected 13 73887 ⟨142966, by decide⟩ ⟨13, 2, 0, 142966, 73887, 829, 16384⟩
    (by decide) selected_cut_04461

theorem unmarked_context_12_18471_142967 : frontier 9 ⟨142967, by decide⟩
    (prefixCache 12 18471) (prefixPartial 12 18471) = false := by
  decide +kernel

theorem node_context_12_18471_142967 : EJMOriginalGlobalDAGData.nodes 9 ⟨142967, by decide⟩ =
    .split (coordinate 12) (![⟨142861, by decide⟩,⟨142934, by decide⟩,⟨142951, by decide⟩,⟨142966, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18471_142967 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18471 ⟨142967, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18471
    ⟨142967, by decide⟩ (by decide) (![⟨142861, by decide⟩,⟨142934, by decide⟩,⟨142951, by decide⟩,⟨142966, by decide⟩]) unmarked_context_12_18471_142967 node_context_12_18471_142967
  intro a
  fin_cases a
  · exact context_13_73884_142861
  · exact context_13_73885_142934
  · exact context_13_73886_142951
  · exact context_13_73887_142966

theorem unmarked_context_11_4617_142968 : frontier 10 ⟨142968, by decide⟩
    (prefixCache 11 4617) (prefixPartial 11 4617) = false := by
  decide +kernel

theorem node_context_11_4617_142968 : EJMOriginalGlobalDAGData.nodes 10 ⟨142968, by decide⟩ =
    .split (coordinate 11) (![⟨118489, by decide⟩,⟨142687, by decide⟩,⟨142831, by decide⟩,⟨142967, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4617_142968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4617 ⟨142968, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4617
    ⟨142968, by decide⟩ (by decide) (![⟨118489, by decide⟩,⟨142687, by decide⟩,⟨142831, by decide⟩,⟨142967, by decide⟩]) unmarked_context_11_4617_142968 node_context_11_4617_142968
  intro a
  fin_cases a
  · exact context_12_18468_118489
  · exact context_12_18469_142687
  · exact context_12_18470_142831
  · exact context_12_18471_142967

theorem selected_cut_04462 : selected 8 ⟨143009, by decide⟩
    (prefixPartial 13 73888) = some ⟨13, 2, 0, 143009, 73888, 1249, 16384⟩ := by
  decide +kernel

theorem context_13_73888_143009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73888 ⟨143009, by decide⟩ :=
  accepted_of_selected 13 73888 ⟨143009, by decide⟩ ⟨13, 2, 0, 143009, 73888, 1249, 16384⟩
    (by decide) selected_cut_04462

theorem selected_cut_04463 : selected 8 ⟨143174, by decide⟩
    (prefixPartial 13 73889) = some ⟨13, 2, 0, 143174, 73889, 2853, 16384⟩ := by
  decide +kernel

theorem context_13_73889_143174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73889 ⟨143174, by decide⟩ :=
  accepted_of_selected 13 73889 ⟨143174, by decide⟩ ⟨13, 2, 0, 143174, 73889, 2853, 16384⟩
    (by decide) selected_cut_04463

theorem selected_cut_04464 : selected 8 ⟨143193, by decide⟩
    (prefixPartial 13 73890) = some ⟨13, 2, 0, 143193, 73890, 649, 16384⟩ := by
  decide +kernel

theorem context_13_73890_143193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73890 ⟨143193, by decide⟩ :=
  accepted_of_selected 13 73890 ⟨143193, by decide⟩ ⟨13, 2, 0, 143193, 73890, 649, 16384⟩
    (by decide) selected_cut_04464

theorem selected_cut_04465 : selected 8 ⟨143205, by decide⟩
    (prefixPartial 13 73891) = some ⟨13, 2, 0, 143205, 73891, 293, 16384⟩ := by
  decide +kernel

theorem context_13_73891_143205 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73891 ⟨143205, by decide⟩ :=
  accepted_of_selected 13 73891 ⟨143205, by decide⟩ ⟨13, 2, 0, 143205, 73891, 293, 16384⟩
    (by decide) selected_cut_04465

theorem unmarked_context_12_18472_143206 : frontier 9 ⟨143206, by decide⟩
    (prefixCache 12 18472) (prefixPartial 12 18472) = false := by
  decide +kernel

theorem node_context_12_18472_143206 : EJMOriginalGlobalDAGData.nodes 9 ⟨143206, by decide⟩ =
    .split (coordinate 12) (![⟨143009, by decide⟩,⟨143174, by decide⟩,⟨143193, by decide⟩,⟨143205, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18472_143206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18472 ⟨143206, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18472
    ⟨143206, by decide⟩ (by decide) (![⟨143009, by decide⟩,⟨143174, by decide⟩,⟨143193, by decide⟩,⟨143205, by decide⟩]) unmarked_context_12_18472_143206 node_context_12_18472_143206
  intro a
  fin_cases a
  · exact context_13_73888_143009
  · exact context_13_73889_143174
  · exact context_13_73890_143193
  · exact context_13_73891_143205

theorem selected_cut_04466 : selected 8 ⟨143262, by decide⟩
    (prefixPartial 13 73892) = some ⟨13, 2, 0, 143262, 73892, 1833, 16384⟩ := by
  decide +kernel

theorem context_13_73892_143262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73892 ⟨143262, by decide⟩ :=
  accepted_of_selected 13 73892 ⟨143262, by decide⟩ ⟨13, 2, 0, 143262, 73892, 1833, 16384⟩
    (by decide) selected_cut_04466

theorem selected_cut_04467 : selected 8 ⟨143390, by decide⟩
    (prefixPartial 13 73893) = some ⟨13, 2, 0, 143390, 73893, 3461, 16384⟩ := by
  decide +kernel

theorem context_13_73893_143390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73893 ⟨143390, by decide⟩ :=
  accepted_of_selected 13 73893 ⟨143390, by decide⟩ ⟨13, 2, 0, 143390, 73893, 3461, 16384⟩
    (by decide) selected_cut_04467

theorem selected_cut_04468 : selected 8 ⟨143423, by decide⟩
    (prefixPartial 13 73894) = some ⟨13, 2, 0, 143423, 73894, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_73894_143423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73894 ⟨143423, by decide⟩ :=
  accepted_of_selected 13 73894 ⟨143423, by decide⟩ ⟨13, 2, 0, 143423, 73894, 1333, 16384⟩
    (by decide) selected_cut_04468

theorem selected_cut_04469 : selected 8 ⟨143448, by decide⟩
    (prefixPartial 13 73895) = some ⟨13, 2, 0, 143448, 73895, 1049, 16384⟩ := by
  decide +kernel

theorem context_13_73895_143448 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73895 ⟨143448, by decide⟩ :=
  accepted_of_selected 13 73895 ⟨143448, by decide⟩ ⟨13, 2, 0, 143448, 73895, 1049, 16384⟩
    (by decide) selected_cut_04469

theorem unmarked_context_12_18473_143449 : frontier 9 ⟨143449, by decide⟩
    (prefixCache 12 18473) (prefixPartial 12 18473) = false := by
  decide +kernel

theorem node_context_12_18473_143449 : EJMOriginalGlobalDAGData.nodes 9 ⟨143449, by decide⟩ =
    .split (coordinate 12) (![⟨143262, by decide⟩,⟨143390, by decide⟩,⟨143423, by decide⟩,⟨143448, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18473_143449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18473 ⟨143449, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18473
    ⟨143449, by decide⟩ (by decide) (![⟨143262, by decide⟩,⟨143390, by decide⟩,⟨143423, by decide⟩,⟨143448, by decide⟩]) unmarked_context_12_18473_143449 node_context_12_18473_143449
  intro a
  fin_cases a
  · exact context_13_73892_143262
  · exact context_13_73893_143390
  · exact context_13_73894_143423
  · exact context_13_73895_143448

theorem selected_cut_04470 : selected 8 ⟨143483, by decide⟩
    (prefixPartial 13 73896) = some ⟨13, 2, 0, 143483, 73896, 1393, 16384⟩ := by
  decide +kernel

theorem context_13_73896_143483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73896 ⟨143483, by decide⟩ :=
  accepted_of_selected 13 73896 ⟨143483, by decide⟩ ⟨13, 2, 0, 143483, 73896, 1393, 16384⟩
    (by decide) selected_cut_04470

theorem selected_cut_04471 : selected 8 ⟨143595, by decide⟩
    (prefixPartial 13 73897) = some ⟨13, 2, 0, 143595, 73897, 3389, 16384⟩ := by
  decide +kernel

theorem context_13_73897_143595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73897 ⟨143595, by decide⟩ :=
  accepted_of_selected 13 73897 ⟨143595, by decide⟩ ⟨13, 2, 0, 143595, 73897, 3389, 16384⟩
    (by decide) selected_cut_04471

theorem selected_cut_04472 : selected 8 ⟨143618, by decide⟩
    (prefixPartial 13 73898) = some ⟨13, 2, 0, 143618, 73898, 1145, 16384⟩ := by
  decide +kernel

theorem context_13_73898_143618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73898 ⟨143618, by decide⟩ :=
  accepted_of_selected 13 73898 ⟨143618, by decide⟩ ⟨13, 2, 0, 143618, 73898, 1145, 16384⟩
    (by decide) selected_cut_04472

theorem selected_cut_04473 : selected 8 ⟨143635, by decide⟩
    (prefixPartial 13 73899) = some ⟨13, 2, 0, 143635, 73899, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_73899_143635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73899 ⟨143635, by decide⟩ :=
  accepted_of_selected 13 73899 ⟨143635, by decide⟩ ⟨13, 2, 0, 143635, 73899, 1013, 16384⟩
    (by decide) selected_cut_04473

theorem unmarked_context_12_18474_143636 : frontier 9 ⟨143636, by decide⟩
    (prefixCache 12 18474) (prefixPartial 12 18474) = false := by
  decide +kernel

theorem node_context_12_18474_143636 : EJMOriginalGlobalDAGData.nodes 9 ⟨143636, by decide⟩ =
    .split (coordinate 12) (![⟨143483, by decide⟩,⟨143595, by decide⟩,⟨143618, by decide⟩,⟨143635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18474_143636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18474 ⟨143636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18474
    ⟨143636, by decide⟩ (by decide) (![⟨143483, by decide⟩,⟨143595, by decide⟩,⟨143618, by decide⟩,⟨143635, by decide⟩]) unmarked_context_12_18474_143636 node_context_12_18474_143636
  intro a
  fin_cases a
  · exact context_13_73896_143483
  · exact context_13_73897_143595
  · exact context_13_73898_143618
  · exact context_13_73899_143635

theorem selected_cut_04474 : selected 8 ⟨143689, by decide⟩
    (prefixPartial 13 73900) = some ⟨13, 2, 0, 143689, 73900, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_73900_143689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73900 ⟨143689, by decide⟩ :=
  accepted_of_selected 13 73900 ⟨143689, by decide⟩ ⟨13, 2, 0, 143689, 73900, 1697, 16384⟩
    (by decide) selected_cut_04474

theorem selected_cut_04475 : selected 8 ⟨143814, by decide⟩
    (prefixPartial 13 73901) = some ⟨13, 2, 0, 143814, 73901, 3525, 16384⟩ := by
  decide +kernel

theorem context_13_73901_143814 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73901 ⟨143814, by decide⟩ :=
  accepted_of_selected 13 73901 ⟨143814, by decide⟩ ⟨13, 2, 0, 143814, 73901, 3525, 16384⟩
    (by decide) selected_cut_04475

theorem selected_cut_04476 : selected 8 ⟨143834, by decide⟩
    (prefixPartial 13 73902) = some ⟨13, 2, 0, 143834, 73902, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_73902_143834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73902 ⟨143834, by decide⟩ :=
  accepted_of_selected 13 73902 ⟨143834, by decide⟩ ⟨13, 2, 0, 143834, 73902, 1205, 16384⟩
    (by decide) selected_cut_04476

theorem selected_cut_04477 : selected 8 ⟨143859, by decide⟩
    (prefixPartial 13 73903) = some ⟨13, 2, 0, 143859, 73903, 1001, 16384⟩ := by
  decide +kernel

theorem context_13_73903_143859 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73903 ⟨143859, by decide⟩ :=
  accepted_of_selected 13 73903 ⟨143859, by decide⟩ ⟨13, 2, 0, 143859, 73903, 1001, 16384⟩
    (by decide) selected_cut_04477

theorem unmarked_context_12_18475_143860 : frontier 9 ⟨143860, by decide⟩
    (prefixCache 12 18475) (prefixPartial 12 18475) = false := by
  decide +kernel

theorem node_context_12_18475_143860 : EJMOriginalGlobalDAGData.nodes 9 ⟨143860, by decide⟩ =
    .split (coordinate 12) (![⟨143689, by decide⟩,⟨143814, by decide⟩,⟨143834, by decide⟩,⟨143859, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18475_143860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18475 ⟨143860, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18475
    ⟨143860, by decide⟩ (by decide) (![⟨143689, by decide⟩,⟨143814, by decide⟩,⟨143834, by decide⟩,⟨143859, by decide⟩]) unmarked_context_12_18475_143860 node_context_12_18475_143860
  intro a
  fin_cases a
  · exact context_13_73900_143689
  · exact context_13_73901_143814
  · exact context_13_73902_143834
  · exact context_13_73903_143859

theorem unmarked_context_11_4618_143861 : frontier 10 ⟨143861, by decide⟩
    (prefixCache 11 4618) (prefixPartial 11 4618) = false := by
  decide +kernel

theorem node_context_11_4618_143861 : EJMOriginalGlobalDAGData.nodes 10 ⟨143861, by decide⟩ =
    .split (coordinate 11) (![⟨143206, by decide⟩,⟨143449, by decide⟩,⟨143636, by decide⟩,⟨143860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4618_143861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4618 ⟨143861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4618
    ⟨143861, by decide⟩ (by decide) (![⟨143206, by decide⟩,⟨143449, by decide⟩,⟨143636, by decide⟩,⟨143860, by decide⟩]) unmarked_context_11_4618_143861 node_context_11_4618_143861
  intro a
  fin_cases a
  · exact context_12_18472_143206
  · exact context_12_18473_143449
  · exact context_12_18474_143636
  · exact context_12_18475_143860

theorem selected_cut_04478 : selected 8 ⟨143884, by decide⟩
    (prefixPartial 13 73904) = some ⟨13, 2, 0, 143884, 73904, 669, 16384⟩ := by
  decide +kernel

theorem context_13_73904_143884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73904 ⟨143884, by decide⟩ :=
  accepted_of_selected 13 73904 ⟨143884, by decide⟩ ⟨13, 2, 0, 143884, 73904, 669, 16384⟩
    (by decide) selected_cut_04478

theorem selected_cut_04479 : selected 8 ⟨143952, by decide⟩
    (prefixPartial 13 73905) = some ⟨13, 2, 0, 143952, 73905, 2153, 16384⟩ := by
  decide +kernel

theorem context_13_73905_143952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73905 ⟨143952, by decide⟩ :=
  accepted_of_selected 13 73905 ⟨143952, by decide⟩ ⟨13, 2, 0, 143952, 73905, 2153, 16384⟩
    (by decide) selected_cut_04479

theorem selected_cut_04480 : selected 8 ⟨143973, by decide⟩
    (prefixPartial 13 73906) = some ⟨13, 2, 0, 143973, 73906, 1029, 16384⟩ := by
  decide +kernel

theorem context_13_73906_143973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73906 ⟨143973, by decide⟩ :=
  accepted_of_selected 13 73906 ⟨143973, by decide⟩ ⟨13, 2, 0, 143973, 73906, 1029, 16384⟩
    (by decide) selected_cut_04480

theorem selected_cut_04481 : selected 8 ⟨143989, by decide⟩
    (prefixPartial 13 73907) = some ⟨13, 2, 0, 143989, 73907, 789, 16384⟩ := by
  decide +kernel

theorem context_13_73907_143989 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73907 ⟨143989, by decide⟩ :=
  accepted_of_selected 13 73907 ⟨143989, by decide⟩ ⟨13, 2, 0, 143989, 73907, 789, 16384⟩
    (by decide) selected_cut_04481

theorem unmarked_context_12_18476_143990 : frontier 9 ⟨143990, by decide⟩
    (prefixCache 12 18476) (prefixPartial 12 18476) = false := by
  decide +kernel

theorem node_context_12_18476_143990 : EJMOriginalGlobalDAGData.nodes 9 ⟨143990, by decide⟩ =
    .split (coordinate 12) (![⟨143884, by decide⟩,⟨143952, by decide⟩,⟨143973, by decide⟩,⟨143989, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18476_143990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18476 ⟨143990, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18476
    ⟨143990, by decide⟩ (by decide) (![⟨143884, by decide⟩,⟨143952, by decide⟩,⟨143973, by decide⟩,⟨143989, by decide⟩]) unmarked_context_12_18476_143990 node_context_12_18476_143990
  intro a
  fin_cases a
  · exact context_13_73904_143884
  · exact context_13_73905_143952
  · exact context_13_73906_143973
  · exact context_13_73907_143989

theorem selected_cut_04482 : selected 8 ⟨144019, by decide⟩
    (prefixPartial 13 73908) = some ⟨13, 2, 0, 144019, 73908, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_73908_144019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73908 ⟨144019, by decide⟩ :=
  accepted_of_selected 13 73908 ⟨144019, by decide⟩ ⟨13, 2, 0, 144019, 73908, 1041, 16384⟩
    (by decide) selected_cut_04482

theorem selected_cut_04483 : selected 8 ⟨144067, by decide⟩
    (prefixPartial 13 73909) = some ⟨13, 2, 0, 144067, 73909, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_73909_144067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73909 ⟨144067, by decide⟩ :=
  accepted_of_selected 13 73909 ⟨144067, by decide⟩ ⟨13, 2, 0, 144067, 73909, 2001, 16384⟩
    (by decide) selected_cut_04483

theorem selected_cut_04484 : selected 8 ⟨144093, by decide⟩
    (prefixPartial 13 73910) = some ⟨13, 2, 0, 144093, 73910, 1205, 16384⟩ := by
  decide +kernel

theorem context_13_73910_144093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73910 ⟨144093, by decide⟩ :=
  accepted_of_selected 13 73910 ⟨144093, by decide⟩ ⟨13, 2, 0, 144093, 73910, 1205, 16384⟩
    (by decide) selected_cut_04484

theorem selected_cut_04485 : selected 8 ⟨144105, by decide⟩
    (prefixPartial 13 73911) = some ⟨13, 2, 0, 144105, 73911, 833, 16384⟩ := by
  decide +kernel

theorem context_13_73911_144105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73911 ⟨144105, by decide⟩ :=
  accepted_of_selected 13 73911 ⟨144105, by decide⟩ ⟨13, 2, 0, 144105, 73911, 833, 16384⟩
    (by decide) selected_cut_04485

theorem unmarked_context_12_18477_144106 : frontier 9 ⟨144106, by decide⟩
    (prefixCache 12 18477) (prefixPartial 12 18477) = false := by
  decide +kernel

theorem node_context_12_18477_144106 : EJMOriginalGlobalDAGData.nodes 9 ⟨144106, by decide⟩ =
    .split (coordinate 12) (![⟨144019, by decide⟩,⟨144067, by decide⟩,⟨144093, by decide⟩,⟨144105, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18477_144106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18477 ⟨144106, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18477
    ⟨144106, by decide⟩ (by decide) (![⟨144019, by decide⟩,⟨144067, by decide⟩,⟨144093, by decide⟩,⟨144105, by decide⟩]) unmarked_context_12_18477_144106 node_context_12_18477_144106
  intro a
  fin_cases a
  · exact context_13_73908_144019
  · exact context_13_73909_144067
  · exact context_13_73910_144093
  · exact context_13_73911_144105

theorem selected_cut_04486 : selected 8 ⟨144128, by decide⟩
    (prefixPartial 13 73912) = some ⟨13, 2, 0, 144128, 73912, 913, 16384⟩ := by
  decide +kernel

theorem context_13_73912_144128 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73912 ⟨144128, by decide⟩ :=
  accepted_of_selected 13 73912 ⟨144128, by decide⟩ ⟨13, 2, 0, 144128, 73912, 913, 16384⟩
    (by decide) selected_cut_04486

theorem selected_cut_04487 : selected 8 ⟨144189, by decide⟩
    (prefixPartial 13 73913) = some ⟨13, 2, 0, 144189, 73913, 2269, 16384⟩ := by
  decide +kernel

theorem context_13_73913_144189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73913 ⟨144189, by decide⟩ :=
  accepted_of_selected 13 73913 ⟨144189, by decide⟩ ⟨13, 2, 0, 144189, 73913, 2269, 16384⟩
    (by decide) selected_cut_04487

theorem selected_cut_04488 : selected 8 ⟨144203, by decide⟩
    (prefixPartial 13 73914) = some ⟨13, 2, 0, 144203, 73914, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_73914_144203 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73914 ⟨144203, by decide⟩ :=
  accepted_of_selected 13 73914 ⟨144203, by decide⟩ ⟨13, 2, 0, 144203, 73914, 1101, 16384⟩
    (by decide) selected_cut_04488

theorem selected_cut_04489 : selected 8 ⟨144215, by decide⟩
    (prefixPartial 13 73915) = some ⟨13, 2, 0, 144215, 73915, 821, 16384⟩ := by
  decide +kernel

theorem context_13_73915_144215 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73915 ⟨144215, by decide⟩ :=
  accepted_of_selected 13 73915 ⟨144215, by decide⟩ ⟨13, 2, 0, 144215, 73915, 821, 16384⟩
    (by decide) selected_cut_04489

theorem unmarked_context_12_18478_144216 : frontier 9 ⟨144216, by decide⟩
    (prefixCache 12 18478) (prefixPartial 12 18478) = false := by
  decide +kernel

theorem node_context_12_18478_144216 : EJMOriginalGlobalDAGData.nodes 9 ⟨144216, by decide⟩ =
    .split (coordinate 12) (![⟨144128, by decide⟩,⟨144189, by decide⟩,⟨144203, by decide⟩,⟨144215, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18478_144216 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18478 ⟨144216, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18478
    ⟨144216, by decide⟩ (by decide) (![⟨144128, by decide⟩,⟨144189, by decide⟩,⟨144203, by decide⟩,⟨144215, by decide⟩]) unmarked_context_12_18478_144216 node_context_12_18478_144216
  intro a
  fin_cases a
  · exact context_13_73912_144128
  · exact context_13_73913_144189
  · exact context_13_73914_144203
  · exact context_13_73915_144215

theorem selected_cut_04490 : selected 8 ⟨144241, by decide⟩
    (prefixPartial 13 73916) = some ⟨13, 2, 0, 144241, 73916, 765, 16384⟩ := by
  decide +kernel

theorem context_13_73916_144241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73916 ⟨144241, by decide⟩ :=
  accepted_of_selected 13 73916 ⟨144241, by decide⟩ ⟨13, 2, 0, 144241, 73916, 765, 16384⟩
    (by decide) selected_cut_04490

theorem selected_cut_04491 : selected 8 ⟨144301, by decide⟩
    (prefixPartial 13 73917) = some ⟨13, 2, 0, 144301, 73917, 1989, 16384⟩ := by
  decide +kernel

theorem context_13_73917_144301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73917 ⟨144301, by decide⟩ :=
  accepted_of_selected 13 73917 ⟨144301, by decide⟩ ⟨13, 2, 0, 144301, 73917, 1989, 16384⟩
    (by decide) selected_cut_04491

theorem selected_cut_04492 : selected 8 ⟨144314, by decide⟩
    (prefixPartial 13 73918) = some ⟨13, 2, 0, 144314, 73918, 1057, 16384⟩ := by
  decide +kernel

theorem context_13_73918_144314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73918 ⟨144314, by decide⟩ :=
  accepted_of_selected 13 73918 ⟨144314, by decide⟩ ⟨13, 2, 0, 144314, 73918, 1057, 16384⟩
    (by decide) selected_cut_04492

theorem selected_cut_04493 : selected 8 ⟨144325, by decide⟩
    (prefixPartial 13 73919) = some ⟨13, 2, 0, 144325, 73919, 693, 16384⟩ := by
  decide +kernel

theorem context_13_73919_144325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73919 ⟨144325, by decide⟩ :=
  accepted_of_selected 13 73919 ⟨144325, by decide⟩ ⟨13, 2, 0, 144325, 73919, 693, 16384⟩
    (by decide) selected_cut_04493

theorem unmarked_context_12_18479_144326 : frontier 9 ⟨144326, by decide⟩
    (prefixCache 12 18479) (prefixPartial 12 18479) = false := by
  decide +kernel

theorem node_context_12_18479_144326 : EJMOriginalGlobalDAGData.nodes 9 ⟨144326, by decide⟩ =
    .split (coordinate 12) (![⟨144241, by decide⟩,⟨144301, by decide⟩,⟨144314, by decide⟩,⟨144325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18479_144326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18479 ⟨144326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18479
    ⟨144326, by decide⟩ (by decide) (![⟨144241, by decide⟩,⟨144301, by decide⟩,⟨144314, by decide⟩,⟨144325, by decide⟩]) unmarked_context_12_18479_144326 node_context_12_18479_144326
  intro a
  fin_cases a
  · exact context_13_73916_144241
  · exact context_13_73917_144301
  · exact context_13_73918_144314
  · exact context_13_73919_144325

theorem unmarked_context_11_4619_144327 : frontier 10 ⟨144327, by decide⟩
    (prefixCache 11 4619) (prefixPartial 11 4619) = false := by
  decide +kernel

theorem node_context_11_4619_144327 : EJMOriginalGlobalDAGData.nodes 10 ⟨144327, by decide⟩ =
    .split (coordinate 11) (![⟨143990, by decide⟩,⟨144106, by decide⟩,⟨144216, by decide⟩,⟨144326, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4619_144327 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4619 ⟨144327, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4619
    ⟨144327, by decide⟩ (by decide) (![⟨143990, by decide⟩,⟨144106, by decide⟩,⟨144216, by decide⟩,⟨144326, by decide⟩]) unmarked_context_11_4619_144327 node_context_11_4619_144327
  intro a
  fin_cases a
  · exact context_12_18476_143990
  · exact context_12_18477_144106
  · exact context_12_18478_144216
  · exact context_12_18479_144326

theorem unmarked_context_10_1154_144328 : frontier 11 ⟨144328, by decide⟩
    (prefixCache 10 1154) (prefixPartial 10 1154) = false := by
  decide +kernel

theorem node_context_10_1154_144328 : EJMOriginalGlobalDAGData.nodes 11 ⟨144328, by decide⟩ =
    .split (coordinate 10) (![⟨142547, by decide⟩,⟨142968, by decide⟩,⟨143861, by decide⟩,⟨144327, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1154_144328 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1154 ⟨144328, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1154
    ⟨144328, by decide⟩ (by decide) (![⟨142547, by decide⟩,⟨142968, by decide⟩,⟨143861, by decide⟩,⟨144327, by decide⟩]) unmarked_context_10_1154_144328 node_context_10_1154_144328
  intro a
  fin_cases a
  · exact context_11_4616_142547
  · exact context_11_4617_142968
  · exact context_11_4618_143861
  · exact context_11_4619_144327

theorem selected_cut_04494 : selected 10 ⟨144456, by decide⟩
    (prefixPartial 11 4620) = some ⟨11, 2, 0, 144456, 4620, 2973, 262144⟩ := by
  decide +kernel

theorem context_11_4620_144456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4620 ⟨144456, by decide⟩ :=
  accepted_of_selected 11 4620 ⟨144456, by decide⟩ ⟨11, 2, 0, 144456, 4620, 2973, 262144⟩
    (by decide) selected_cut_04494

theorem selected_cut_04495 : selected 9 ⟨118489, by decide⟩
    (prefixPartial 12 18484) = some ⟨12, 1, 0, 118489, 18484, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18484_118489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18484 ⟨118489, by decide⟩ :=
  accepted_of_selected 12 18484 ⟨118489, by decide⟩ ⟨12, 1, 0, 118489, 18484, 1, 65536⟩
    (by decide) selected_cut_04495

theorem selected_cut_04496 : selected 9 ⟨144564, by decide⟩
    (prefixPartial 12 18485) = some ⟨12, 2, 0, 144564, 18485, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_18485_144564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18485 ⟨144564, by decide⟩ :=
  accepted_of_selected 12 18485 ⟨144564, by decide⟩ ⟨12, 2, 0, 144564, 18485, 3861, 65536⟩
    (by decide) selected_cut_04496

theorem selected_cut_04497 : selected 8 ⟨144578, by decide⟩
    (prefixPartial 13 73944) = some ⟨13, 2, 0, 144578, 73944, 573, 16384⟩ := by
  decide +kernel

theorem context_13_73944_144578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73944 ⟨144578, by decide⟩ :=
  accepted_of_selected 13 73944 ⟨144578, by decide⟩ ⟨13, 2, 0, 144578, 73944, 573, 16384⟩
    (by decide) selected_cut_04497

theorem selected_cut_04498 : selected 8 ⟨144645, by decide⟩
    (prefixPartial 13 73945) = some ⟨13, 2, 0, 144645, 73945, 1897, 16384⟩ := by
  decide +kernel

theorem context_13_73945_144645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73945 ⟨144645, by decide⟩ :=
  accepted_of_selected 13 73945 ⟨144645, by decide⟩ ⟨13, 2, 0, 144645, 73945, 1897, 16384⟩
    (by decide) selected_cut_04498

theorem selected_cut_04499 : selected 8 ⟨144664, by decide⟩
    (prefixPartial 13 73946) = some ⟨13, 2, 0, 144664, 73946, 1105, 16384⟩ := by
  decide +kernel

theorem context_13_73946_144664 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73946 ⟨144664, by decide⟩ :=
  accepted_of_selected 13 73946 ⟨144664, by decide⟩ ⟨13, 2, 0, 144664, 73946, 1105, 16384⟩
    (by decide) selected_cut_04499

theorem selected_cut_04500 : selected 8 ⟨144676, by decide⟩
    (prefixPartial 13 73947) = some ⟨13, 2, 0, 144676, 73947, 645, 16384⟩ := by
  decide +kernel

theorem context_13_73947_144676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73947 ⟨144676, by decide⟩ :=
  accepted_of_selected 13 73947 ⟨144676, by decide⟩ ⟨13, 2, 0, 144676, 73947, 645, 16384⟩
    (by decide) selected_cut_04500

theorem unmarked_context_12_18486_144677 : frontier 9 ⟨144677, by decide⟩
    (prefixCache 12 18486) (prefixPartial 12 18486) = false := by
  decide +kernel

theorem node_context_12_18486_144677 : EJMOriginalGlobalDAGData.nodes 9 ⟨144677, by decide⟩ =
    .split (coordinate 12) (![⟨144578, by decide⟩,⟨144645, by decide⟩,⟨144664, by decide⟩,⟨144676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18486_144677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18486 ⟨144677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18486
    ⟨144677, by decide⟩ (by decide) (![⟨144578, by decide⟩,⟨144645, by decide⟩,⟨144664, by decide⟩,⟨144676, by decide⟩]) unmarked_context_12_18486_144677 node_context_12_18486_144677
  intro a
  fin_cases a
  · exact context_13_73944_144578
  · exact context_13_73945_144645
  · exact context_13_73946_144664
  · exact context_13_73947_144676

theorem selected_cut_04501 : selected 8 ⟨144696, by decide⟩
    (prefixPartial 13 73948) = some ⟨13, 2, 0, 144696, 73948, 601, 16384⟩ := by
  decide +kernel

theorem context_13_73948_144696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73948 ⟨144696, by decide⟩ :=
  accepted_of_selected 13 73948 ⟨144696, by decide⟩ ⟨13, 2, 0, 144696, 73948, 601, 16384⟩
    (by decide) selected_cut_04501

theorem selected_cut_04502 : selected 8 ⟨144759, by decide⟩
    (prefixPartial 13 73949) = some ⟨13, 2, 0, 144759, 73949, 1881, 16384⟩ := by
  decide +kernel

theorem context_13_73949_144759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73949 ⟨144759, by decide⟩ :=
  accepted_of_selected 13 73949 ⟨144759, by decide⟩ ⟨13, 2, 0, 144759, 73949, 1881, 16384⟩
    (by decide) selected_cut_04502

theorem selected_cut_04503 : selected 8 ⟨144788, by decide⟩
    (prefixPartial 13 73950) = some ⟨13, 2, 0, 144788, 73950, 1117, 16384⟩ := by
  decide +kernel

theorem context_13_73950_144788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73950 ⟨144788, by decide⟩ :=
  accepted_of_selected 13 73950 ⟨144788, by decide⟩ ⟨13, 2, 0, 144788, 73950, 1117, 16384⟩
    (by decide) selected_cut_04503

theorem selected_cut_04504 : selected 8 ⟨144806, by decide⟩
    (prefixPartial 13 73951) = some ⟨13, 2, 0, 144806, 73951, 617, 16384⟩ := by
  decide +kernel

theorem context_13_73951_144806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73951 ⟨144806, by decide⟩ :=
  accepted_of_selected 13 73951 ⟨144806, by decide⟩ ⟨13, 2, 0, 144806, 73951, 617, 16384⟩
    (by decide) selected_cut_04504

theorem unmarked_context_12_18487_144807 : frontier 9 ⟨144807, by decide⟩
    (prefixCache 12 18487) (prefixPartial 12 18487) = false := by
  decide +kernel

theorem node_context_12_18487_144807 : EJMOriginalGlobalDAGData.nodes 9 ⟨144807, by decide⟩ =
    .split (coordinate 12) (![⟨144696, by decide⟩,⟨144759, by decide⟩,⟨144788, by decide⟩,⟨144806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18487_144807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18487 ⟨144807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18487
    ⟨144807, by decide⟩ (by decide) (![⟨144696, by decide⟩,⟨144759, by decide⟩,⟨144788, by decide⟩,⟨144806, by decide⟩]) unmarked_context_12_18487_144807 node_context_12_18487_144807
  intro a
  fin_cases a
  · exact context_13_73948_144696
  · exact context_13_73949_144759
  · exact context_13_73950_144788
  · exact context_13_73951_144806

theorem unmarked_context_11_4621_144808 : frontier 10 ⟨144808, by decide⟩
    (prefixCache 11 4621) (prefixPartial 11 4621) = false := by
  decide +kernel

theorem node_context_11_4621_144808 : EJMOriginalGlobalDAGData.nodes 10 ⟨144808, by decide⟩ =
    .split (coordinate 11) (![⟨118489, by decide⟩,⟨144564, by decide⟩,⟨144677, by decide⟩,⟨144807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4621_144808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4621 ⟨144808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4621
    ⟨144808, by decide⟩ (by decide) (![⟨118489, by decide⟩,⟨144564, by decide⟩,⟨144677, by decide⟩,⟨144807, by decide⟩]) unmarked_context_11_4621_144808 node_context_11_4621_144808
  intro a
  fin_cases a
  · exact context_12_18484_118489
  · exact context_12_18485_144564
  · exact context_12_18486_144677
  · exact context_12_18487_144807

theorem selected_cut_04505 : selected 9 ⟨118489, by decide⟩
    (prefixPartial 12 18488) = some ⟨12, 1, 0, 118489, 18488, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18488_118489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18488 ⟨118489, by decide⟩ :=
  accepted_of_selected 12 18488 ⟨118489, by decide⟩ ⟨12, 1, 0, 118489, 18488, 1, 65536⟩
    (by decide) selected_cut_04505

theorem selected_cut_04506 : selected 9 ⟨144902, by decide⟩
    (prefixPartial 12 18489) = some ⟨12, 2, 0, 144902, 18489, 4037, 65536⟩ := by
  decide +kernel

theorem context_12_18489_144902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18489 ⟨144902, by decide⟩ :=
  accepted_of_selected 12 18489 ⟨144902, by decide⟩ ⟨12, 2, 0, 144902, 18489, 4037, 65536⟩
    (by decide) selected_cut_04506

theorem selected_cut_04507 : selected 9 ⟨145010, by decide⟩
    (prefixPartial 12 18490) = some ⟨12, 2, 0, 145010, 18490, 3861, 65536⟩ := by
  decide +kernel

theorem context_12_18490_145010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18490 ⟨145010, by decide⟩ :=
  accepted_of_selected 12 18490 ⟨145010, by decide⟩ ⟨12, 2, 0, 145010, 18490, 3861, 65536⟩
    (by decide) selected_cut_04507

theorem selected_cut_04508 : selected 8 ⟨145024, by decide⟩
    (prefixPartial 13 73964) = some ⟨13, 2, 0, 145024, 73964, 393, 16384⟩ := by
  decide +kernel

theorem context_13_73964_145024 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73964 ⟨145024, by decide⟩ :=
  accepted_of_selected 13 73964 ⟨145024, by decide⟩ ⟨13, 2, 0, 145024, 73964, 393, 16384⟩
    (by decide) selected_cut_04508

theorem selected_cut_04509 : selected 8 ⟨145090, by decide⟩
    (prefixPartial 13 73965) = some ⟨13, 2, 0, 145090, 73965, 2049, 16384⟩ := by
  decide +kernel

theorem context_13_73965_145090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73965 ⟨145090, by decide⟩ :=
  accepted_of_selected 13 73965 ⟨145090, by decide⟩ ⟨13, 2, 0, 145090, 73965, 2049, 16384⟩
    (by decide) selected_cut_04509

theorem selected_cut_04510 : selected 8 ⟨145110, by decide⟩
    (prefixPartial 13 73966) = some ⟨13, 2, 0, 145110, 73966, 1033, 16384⟩ := by
  decide +kernel

theorem context_13_73966_145110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73966 ⟨145110, by decide⟩ :=
  accepted_of_selected 13 73966 ⟨145110, by decide⟩ ⟨13, 2, 0, 145110, 73966, 1033, 16384⟩
    (by decide) selected_cut_04510

theorem selected_cut_04511 : selected 8 ⟨145125, by decide⟩
    (prefixPartial 13 73967) = some ⟨13, 2, 0, 145125, 73967, 653, 16384⟩ := by
  decide +kernel

theorem context_13_73967_145125 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 73967 ⟨145125, by decide⟩ :=
  accepted_of_selected 13 73967 ⟨145125, by decide⟩ ⟨13, 2, 0, 145125, 73967, 653, 16384⟩
    (by decide) selected_cut_04511

theorem unmarked_context_12_18491_145126 : frontier 9 ⟨145126, by decide⟩
    (prefixCache 12 18491) (prefixPartial 12 18491) = false := by
  decide +kernel

theorem node_context_12_18491_145126 : EJMOriginalGlobalDAGData.nodes 9 ⟨145126, by decide⟩ =
    .split (coordinate 12) (![⟨145024, by decide⟩,⟨145090, by decide⟩,⟨145110, by decide⟩,⟨145125, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18491_145126 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18491 ⟨145126, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18491
    ⟨145126, by decide⟩ (by decide) (![⟨145024, by decide⟩,⟨145090, by decide⟩,⟨145110, by decide⟩,⟨145125, by decide⟩]) unmarked_context_12_18491_145126 node_context_12_18491_145126
  intro a
  fin_cases a
  · exact context_13_73964_145024
  · exact context_13_73965_145090
  · exact context_13_73966_145110
  · exact context_13_73967_145125

theorem unmarked_context_11_4622_145127 : frontier 10 ⟨145127, by decide⟩
    (prefixCache 11 4622) (prefixPartial 11 4622) = false := by
  decide +kernel

theorem node_context_11_4622_145127 : EJMOriginalGlobalDAGData.nodes 10 ⟨145127, by decide⟩ =
    .split (coordinate 11) (![⟨118489, by decide⟩,⟨144902, by decide⟩,⟨145010, by decide⟩,⟨145126, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4622_145127 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4622 ⟨145127, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4622
    ⟨145127, by decide⟩ (by decide) (![⟨118489, by decide⟩,⟨144902, by decide⟩,⟨145010, by decide⟩,⟨145126, by decide⟩]) unmarked_context_11_4622_145127 node_context_11_4622_145127
  intro a
  fin_cases a
  · exact context_12_18488_118489
  · exact context_12_18489_144902
  · exact context_12_18490_145010
  · exact context_12_18491_145126

theorem selected_cut_04512 : selected 9 ⟨145206, by decide⟩
    (prefixPartial 12 18492) = some ⟨12, 2, 0, 145206, 18492, 2137, 65536⟩ := by
  decide +kernel

theorem context_12_18492_145206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18492 ⟨145206, by decide⟩ :=
  accepted_of_selected 12 18492 ⟨145206, by decide⟩ ⟨12, 2, 0, 145206, 18492, 2137, 65536⟩
    (by decide) selected_cut_04512

theorem selected_cut_04513 : selected 9 ⟨145274, by decide⟩
    (prefixPartial 12 18493) = some ⟨12, 2, 0, 145274, 18493, 3125, 65536⟩ := by
  decide +kernel

theorem context_12_18493_145274 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18493 ⟨145274, by decide⟩ :=
  accepted_of_selected 12 18493 ⟨145274, by decide⟩ ⟨12, 2, 0, 145274, 18493, 3125, 65536⟩
    (by decide) selected_cut_04513

theorem selected_cut_04514 : selected 9 ⟨145361, by decide⟩
    (prefixPartial 12 18494) = some ⟨12, 2, 0, 145361, 18494, 3333, 65536⟩ := by
  decide +kernel

theorem context_12_18494_145361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18494 ⟨145361, by decide⟩ :=
  accepted_of_selected 12 18494 ⟨145361, by decide⟩ ⟨12, 2, 0, 145361, 18494, 3333, 65536⟩
    (by decide) selected_cut_04514

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
