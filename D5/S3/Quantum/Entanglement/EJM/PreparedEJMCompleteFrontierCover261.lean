/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover260
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_25060 : selected 8 ⟨633840, by decide⟩
    (prefixPartial 13 310444) = some ⟨13, 2, 0, 633840, 310444, 701, 16384⟩ := by
  decide +kernel

theorem context_13_310444_633840 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310444 ⟨633840, by decide⟩ :=
  accepted_of_selected 13 310444 ⟨633840, by decide⟩ ⟨13, 2, 0, 633840, 310444, 701, 16384⟩
    (by decide) selected_cut_25060

theorem selected_cut_25061 : selected 8 ⟨633872, by decide⟩
    (prefixPartial 13 310445) = some ⟨13, 2, 0, 633872, 310445, 2577, 16384⟩ := by
  decide +kernel

theorem context_13_310445_633872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310445 ⟨633872, by decide⟩ :=
  accepted_of_selected 13 310445 ⟨633872, by decide⟩ ⟨13, 2, 0, 633872, 310445, 2577, 16384⟩
    (by decide) selected_cut_25061

theorem selected_cut_25062 : selected 8 ⟨633894, by decide⟩
    (prefixPartial 13 310446) = some ⟨13, 2, 0, 633894, 310446, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_310446_633894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310446 ⟨633894, by decide⟩ :=
  accepted_of_selected 13 310446 ⟨633894, by decide⟩ ⟨13, 2, 0, 633894, 310446, 1957, 16384⟩
    (by decide) selected_cut_25062

theorem selected_cut_25063 : selected 8 ⟨633902, by decide⟩
    (prefixPartial 13 310447) = some ⟨13, 2, 0, 633902, 310447, 781, 16384⟩ := by
  decide +kernel

theorem context_13_310447_633902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310447 ⟨633902, by decide⟩ :=
  accepted_of_selected 13 310447 ⟨633902, by decide⟩ ⟨13, 2, 0, 633902, 310447, 781, 16384⟩
    (by decide) selected_cut_25063

theorem unmarked_context_12_77611_633903 : frontier 9 ⟨633903, by decide⟩
    (prefixCache 12 77611) (prefixPartial 12 77611) = false := by
  decide +kernel

theorem node_context_12_77611_633903 : EJMOriginalGlobalDAGData.nodes 9 ⟨633903, by decide⟩ =
    .split (coordinate 12) (![⟨633840, by decide⟩,⟨633872, by decide⟩,⟨633894, by decide⟩,⟨633902, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77611_633903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77611 ⟨633903, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77611
    ⟨633903, by decide⟩ (by decide) (![⟨633840, by decide⟩,⟨633872, by decide⟩,⟨633894, by decide⟩,⟨633902, by decide⟩]) unmarked_context_12_77611_633903 node_context_12_77611_633903
  intro a
  fin_cases a
  · exact context_13_310444_633840
  · exact context_13_310445_633872
  · exact context_13_310446_633894
  · exact context_13_310447_633902

theorem unmarked_context_11_19402_633904 : frontier 10 ⟨633904, by decide⟩
    (prefixCache 11 19402) (prefixPartial 11 19402) = false := by
  decide +kernel

theorem node_context_11_19402_633904 : EJMOriginalGlobalDAGData.nodes 10 ⟨633904, by decide⟩ =
    .split (coordinate 11) (![⟨435790, by decide⟩,⟨633738, by decide⟩,⟨633825, by decide⟩,⟨633903, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19402_633904 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19402 ⟨633904, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19402
    ⟨633904, by decide⟩ (by decide) (![⟨435790, by decide⟩,⟨633738, by decide⟩,⟨633825, by decide⟩,⟨633903, by decide⟩]) unmarked_context_11_19402_633904 node_context_11_19402_633904
  intro a
  fin_cases a
  · exact context_12_77608_435790
  · exact context_12_77609_633738
  · exact context_12_77610_633825
  · exact context_12_77611_633903

theorem selected_cut_25064 : selected 9 ⟨540189, by decide⟩
    (prefixPartial 12 77612) = some ⟨12, 1, 0, 540189, 77612, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77612_540189 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77612 ⟨540189, by decide⟩ :=
  accepted_of_selected 12 77612 ⟨540189, by decide⟩ ⟨12, 1, 0, 540189, 77612, 1, 65536⟩
    (by decide) selected_cut_25064

theorem selected_cut_25065 : selected 8 ⟨633924, by decide⟩
    (prefixPartial 13 310452) = some ⟨13, 2, 0, 633924, 310452, 581, 16384⟩ := by
  decide +kernel

theorem context_13_310452_633924 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310452 ⟨633924, by decide⟩ :=
  accepted_of_selected 13 310452 ⟨633924, by decide⟩ ⟨13, 2, 0, 633924, 310452, 581, 16384⟩
    (by decide) selected_cut_25065

theorem selected_cut_25066 : selected 8 ⟨633966, by decide⟩
    (prefixPartial 13 310453) = some ⟨13, 2, 0, 633966, 310453, 2253, 16384⟩ := by
  decide +kernel

theorem context_13_310453_633966 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310453 ⟨633966, by decide⟩ :=
  accepted_of_selected 13 310453 ⟨633966, by decide⟩ ⟨13, 2, 0, 633966, 310453, 2253, 16384⟩
    (by decide) selected_cut_25066

theorem selected_cut_25067 : selected 8 ⟨633994, by decide⟩
    (prefixPartial 13 310454) = some ⟨13, 2, 0, 633994, 310454, 1817, 16384⟩ := by
  decide +kernel

theorem context_13_310454_633994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310454 ⟨633994, by decide⟩ :=
  accepted_of_selected 13 310454 ⟨633994, by decide⟩ ⟨13, 2, 0, 633994, 310454, 1817, 16384⟩
    (by decide) selected_cut_25067

theorem selected_cut_25068 : selected 8 ⟨633999, by decide⟩
    (prefixPartial 13 310455) = some ⟨13, 2, 0, 633999, 310455, 529, 16384⟩ := by
  decide +kernel

theorem context_13_310455_633999 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310455 ⟨633999, by decide⟩ :=
  accepted_of_selected 13 310455 ⟨633999, by decide⟩ ⟨13, 2, 0, 633999, 310455, 529, 16384⟩
    (by decide) selected_cut_25068

theorem unmarked_context_12_77613_634000 : frontier 9 ⟨634000, by decide⟩
    (prefixCache 12 77613) (prefixPartial 12 77613) = false := by
  decide +kernel

theorem node_context_12_77613_634000 : EJMOriginalGlobalDAGData.nodes 9 ⟨634000, by decide⟩ =
    .split (coordinate 12) (![⟨633924, by decide⟩,⟨633966, by decide⟩,⟨633994, by decide⟩,⟨633999, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77613_634000 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77613 ⟨634000, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77613
    ⟨634000, by decide⟩ (by decide) (![⟨633924, by decide⟩,⟨633966, by decide⟩,⟨633994, by decide⟩,⟨633999, by decide⟩]) unmarked_context_12_77613_634000 node_context_12_77613_634000
  intro a
  fin_cases a
  · exact context_13_310452_633924
  · exact context_13_310453_633966
  · exact context_13_310454_633994
  · exact context_13_310455_633999

theorem selected_cut_25069 : selected 8 ⟨634012, by decide⟩
    (prefixPartial 13 310456) = some ⟨13, 2, 0, 634012, 310456, 457, 16384⟩ := by
  decide +kernel

theorem context_13_310456_634012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310456 ⟨634012, by decide⟩ :=
  accepted_of_selected 13 310456 ⟨634012, by decide⟩ ⟨13, 2, 0, 634012, 310456, 457, 16384⟩
    (by decide) selected_cut_25069

theorem selected_cut_25070 : selected 8 ⟨634055, by decide⟩
    (prefixPartial 13 310457) = some ⟨13, 2, 0, 634055, 310457, 2117, 16384⟩ := by
  decide +kernel

theorem context_13_310457_634055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310457 ⟨634055, by decide⟩ :=
  accepted_of_selected 13 310457 ⟨634055, by decide⟩ ⟨13, 2, 0, 634055, 310457, 2117, 16384⟩
    (by decide) selected_cut_25070

theorem selected_cut_25071 : selected 8 ⟨634076, by decide⟩
    (prefixPartial 13 310458) = some ⟨13, 2, 0, 634076, 310458, 1321, 16384⟩ := by
  decide +kernel

theorem context_13_310458_634076 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310458 ⟨634076, by decide⟩ :=
  accepted_of_selected 13 310458 ⟨634076, by decide⟩ ⟨13, 2, 0, 634076, 310458, 1321, 16384⟩
    (by decide) selected_cut_25071

theorem selected_cut_25072 : selected 8 ⟨634082, by decide⟩
    (prefixPartial 13 310459) = some ⟨13, 2, 0, 634082, 310459, 661, 16384⟩ := by
  decide +kernel

theorem context_13_310459_634082 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310459 ⟨634082, by decide⟩ :=
  accepted_of_selected 13 310459 ⟨634082, by decide⟩ ⟨13, 2, 0, 634082, 310459, 661, 16384⟩
    (by decide) selected_cut_25072

theorem unmarked_context_12_77614_634083 : frontier 9 ⟨634083, by decide⟩
    (prefixCache 12 77614) (prefixPartial 12 77614) = false := by
  decide +kernel

theorem node_context_12_77614_634083 : EJMOriginalGlobalDAGData.nodes 9 ⟨634083, by decide⟩ =
    .split (coordinate 12) (![⟨634012, by decide⟩,⟨634055, by decide⟩,⟨634076, by decide⟩,⟨634082, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77614_634083 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77614 ⟨634083, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77614
    ⟨634083, by decide⟩ (by decide) (![⟨634012, by decide⟩,⟨634055, by decide⟩,⟨634076, by decide⟩,⟨634082, by decide⟩]) unmarked_context_12_77614_634083 node_context_12_77614_634083
  intro a
  fin_cases a
  · exact context_13_310456_634012
  · exact context_13_310457_634055
  · exact context_13_310458_634076
  · exact context_13_310459_634082

theorem selected_cut_25073 : selected 9 ⟨634084, by decide⟩
    (prefixPartial 12 77615) = some ⟨12, 1, 0, 634084, 77615, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77615_634084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77615 ⟨634084, by decide⟩ :=
  accepted_of_selected 12 77615 ⟨634084, by decide⟩ ⟨12, 1, 0, 634084, 77615, 1, 65536⟩
    (by decide) selected_cut_25073

theorem unmarked_context_11_19403_634085 : frontier 10 ⟨634085, by decide⟩
    (prefixCache 11 19403) (prefixPartial 11 19403) = false := by
  decide +kernel

theorem node_context_11_19403_634085 : EJMOriginalGlobalDAGData.nodes 10 ⟨634085, by decide⟩ =
    .split (coordinate 11) (![⟨540189, by decide⟩,⟨634000, by decide⟩,⟨634083, by decide⟩,⟨634084, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19403_634085 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19403 ⟨634085, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19403
    ⟨634085, by decide⟩ (by decide) (![⟨540189, by decide⟩,⟨634000, by decide⟩,⟨634083, by decide⟩,⟨634084, by decide⟩]) unmarked_context_11_19403_634085 node_context_11_19403_634085
  intro a
  fin_cases a
  · exact context_12_77612_540189
  · exact context_12_77613_634000
  · exact context_12_77614_634083
  · exact context_12_77615_634084

theorem unmarked_context_10_4850_634086 : frontier 11 ⟨634086, by decide⟩
    (prefixCache 10 4850) (prefixPartial 10 4850) = false := by
  decide +kernel

theorem node_context_10_4850_634086 : EJMOriginalGlobalDAGData.nodes 11 ⟨634086, by decide⟩ =
    .split (coordinate 10) (![⟨633200, by decide⟩,⟨633624, by decide⟩,⟨633904, by decide⟩,⟨634085, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4850_634086 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4850 ⟨634086, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4850
    ⟨634086, by decide⟩ (by decide) (![⟨633200, by decide⟩,⟨633624, by decide⟩,⟨633904, by decide⟩,⟨634085, by decide⟩]) unmarked_context_10_4850_634086 node_context_10_4850_634086
  intro a
  fin_cases a
  · exact context_11_19400_633200
  · exact context_11_19401_633624
  · exact context_11_19402_633904
  · exact context_11_19403_634085

theorem selected_cut_25074 : selected 9 ⟨445562, by decide⟩
    (prefixPartial 12 77616) = some ⟨12, 1, 0, 445562, 77616, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77616_445562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77616 ⟨445562, by decide⟩ :=
  accepted_of_selected 12 77616 ⟨445562, by decide⟩ ⟨12, 1, 0, 445562, 77616, 1, 65536⟩
    (by decide) selected_cut_25074

theorem selected_cut_25075 : selected 8 ⟨634093, by decide⟩
    (prefixPartial 13 310468) = some ⟨13, 2, 0, 634093, 310468, 449, 16384⟩ := by
  decide +kernel

theorem context_13_310468_634093 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310468 ⟨634093, by decide⟩ :=
  accepted_of_selected 13 310468 ⟨634093, by decide⟩ ⟨13, 2, 0, 634093, 310468, 449, 16384⟩
    (by decide) selected_cut_25075

theorem selected_cut_25076 : selected 8 ⟨634139, by decide⟩
    (prefixPartial 13 310469) = some ⟨13, 2, 0, 634139, 310469, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_310469_634139 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310469 ⟨634139, by decide⟩ :=
  accepted_of_selected 13 310469 ⟨634139, by decide⟩ ⟨13, 2, 0, 634139, 310469, 2765, 16384⟩
    (by decide) selected_cut_25076

theorem selected_cut_25077 : selected 8 ⟨634164, by decide⟩
    (prefixPartial 13 310470) = some ⟨13, 2, 0, 634164, 310470, 1925, 16384⟩ := by
  decide +kernel

theorem context_13_310470_634164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310470 ⟨634164, by decide⟩ :=
  accepted_of_selected 13 310470 ⟨634164, by decide⟩ ⟨13, 2, 0, 634164, 310470, 1925, 16384⟩
    (by decide) selected_cut_25077

theorem selected_cut_25078 : selected 8 ⟨634173, by decide⟩
    (prefixPartial 13 310471) = some ⟨13, 2, 0, 634173, 310471, 765, 16384⟩ := by
  decide +kernel

theorem context_13_310471_634173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310471 ⟨634173, by decide⟩ :=
  accepted_of_selected 13 310471 ⟨634173, by decide⟩ ⟨13, 2, 0, 634173, 310471, 765, 16384⟩
    (by decide) selected_cut_25078

theorem unmarked_context_12_77617_634174 : frontier 9 ⟨634174, by decide⟩
    (prefixCache 12 77617) (prefixPartial 12 77617) = false := by
  decide +kernel

theorem node_context_12_77617_634174 : EJMOriginalGlobalDAGData.nodes 9 ⟨634174, by decide⟩ =
    .split (coordinate 12) (![⟨634093, by decide⟩,⟨634139, by decide⟩,⟨634164, by decide⟩,⟨634173, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77617_634174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77617 ⟨634174, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77617
    ⟨634174, by decide⟩ (by decide) (![⟨634093, by decide⟩,⟨634139, by decide⟩,⟨634164, by decide⟩,⟨634173, by decide⟩]) unmarked_context_12_77617_634174 node_context_12_77617_634174
  intro a
  fin_cases a
  · exact context_13_310468_634093
  · exact context_13_310469_634139
  · exact context_13_310470_634164
  · exact context_13_310471_634173

theorem selected_cut_25079 : selected 8 ⟨634181, by decide⟩
    (prefixPartial 13 310472) = some ⟨13, 2, 0, 634181, 310472, 365, 16384⟩ := by
  decide +kernel

theorem context_13_310472_634181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310472 ⟨634181, by decide⟩ :=
  accepted_of_selected 13 310472 ⟨634181, by decide⟩ ⟨13, 2, 0, 634181, 310472, 365, 16384⟩
    (by decide) selected_cut_25079

theorem selected_cut_25080 : selected 8 ⟨634217, by decide⟩
    (prefixPartial 13 310473) = some ⟨13, 2, 0, 634217, 310473, 2521, 16384⟩ := by
  decide +kernel

theorem context_13_310473_634217 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310473 ⟨634217, by decide⟩ :=
  accepted_of_selected 13 310473 ⟨634217, by decide⟩ ⟨13, 2, 0, 634217, 310473, 2521, 16384⟩
    (by decide) selected_cut_25080

theorem selected_cut_25081 : selected 8 ⟨634235, by decide⟩
    (prefixPartial 13 310474) = some ⟨13, 2, 0, 634235, 310474, 1673, 16384⟩ := by
  decide +kernel

theorem context_13_310474_634235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310474 ⟨634235, by decide⟩ :=
  accepted_of_selected 13 310474 ⟨634235, by decide⟩ ⟨13, 2, 0, 634235, 310474, 1673, 16384⟩
    (by decide) selected_cut_25081

theorem selected_cut_25082 : selected 8 ⟨634246, by decide⟩
    (prefixPartial 13 310475) = some ⟨13, 2, 0, 634246, 310475, 781, 16384⟩ := by
  decide +kernel

theorem context_13_310475_634246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310475 ⟨634246, by decide⟩ :=
  accepted_of_selected 13 310475 ⟨634246, by decide⟩ ⟨13, 2, 0, 634246, 310475, 781, 16384⟩
    (by decide) selected_cut_25082

theorem unmarked_context_12_77618_634247 : frontier 9 ⟨634247, by decide⟩
    (prefixCache 12 77618) (prefixPartial 12 77618) = false := by
  decide +kernel

theorem node_context_12_77618_634247 : EJMOriginalGlobalDAGData.nodes 9 ⟨634247, by decide⟩ =
    .split (coordinate 12) (![⟨634181, by decide⟩,⟨634217, by decide⟩,⟨634235, by decide⟩,⟨634246, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77618_634247 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77618 ⟨634247, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77618
    ⟨634247, by decide⟩ (by decide) (![⟨634181, by decide⟩,⟨634217, by decide⟩,⟨634235, by decide⟩,⟨634246, by decide⟩]) unmarked_context_12_77618_634247 node_context_12_77618_634247
  intro a
  fin_cases a
  · exact context_13_310472_634181
  · exact context_13_310473_634217
  · exact context_13_310474_634235
  · exact context_13_310475_634246

theorem selected_cut_25083 : selected 8 ⟨634254, by decide⟩
    (prefixPartial 13 310476) = some ⟨13, 2, 0, 634254, 310476, 349, 16384⟩ := by
  decide +kernel

theorem context_13_310476_634254 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310476 ⟨634254, by decide⟩ :=
  accepted_of_selected 13 310476 ⟨634254, by decide⟩ ⟨13, 2, 0, 634254, 310476, 349, 16384⟩
    (by decide) selected_cut_25083

theorem selected_cut_25084 : selected 8 ⟨634281, by decide⟩
    (prefixPartial 13 310477) = some ⟨13, 2, 0, 634281, 310477, 2445, 16384⟩ := by
  decide +kernel

theorem context_13_310477_634281 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310477 ⟨634281, by decide⟩ :=
  accepted_of_selected 13 310477 ⟨634281, by decide⟩ ⟨13, 2, 0, 634281, 310477, 2445, 16384⟩
    (by decide) selected_cut_25084

theorem selected_cut_25085 : selected 8 ⟨634305, by decide⟩
    (prefixPartial 13 310478) = some ⟨13, 2, 0, 634305, 310478, 1537, 16384⟩ := by
  decide +kernel

theorem context_13_310478_634305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310478 ⟨634305, by decide⟩ :=
  accepted_of_selected 13 310478 ⟨634305, by decide⟩ ⟨13, 2, 0, 634305, 310478, 1537, 16384⟩
    (by decide) selected_cut_25085

theorem selected_cut_25086 : selected 8 ⟨634313, by decide⟩
    (prefixPartial 13 310479) = some ⟨13, 2, 0, 634313, 310479, 725, 16384⟩ := by
  decide +kernel

theorem context_13_310479_634313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310479 ⟨634313, by decide⟩ :=
  accepted_of_selected 13 310479 ⟨634313, by decide⟩ ⟨13, 2, 0, 634313, 310479, 725, 16384⟩
    (by decide) selected_cut_25086

theorem unmarked_context_12_77619_634314 : frontier 9 ⟨634314, by decide⟩
    (prefixCache 12 77619) (prefixPartial 12 77619) = false := by
  decide +kernel

theorem node_context_12_77619_634314 : EJMOriginalGlobalDAGData.nodes 9 ⟨634314, by decide⟩ =
    .split (coordinate 12) (![⟨634254, by decide⟩,⟨634281, by decide⟩,⟨634305, by decide⟩,⟨634313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77619_634314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77619 ⟨634314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77619
    ⟨634314, by decide⟩ (by decide) (![⟨634254, by decide⟩,⟨634281, by decide⟩,⟨634305, by decide⟩,⟨634313, by decide⟩]) unmarked_context_12_77619_634314 node_context_12_77619_634314
  intro a
  fin_cases a
  · exact context_13_310476_634254
  · exact context_13_310477_634281
  · exact context_13_310478_634305
  · exact context_13_310479_634313

theorem unmarked_context_11_19404_634315 : frontier 10 ⟨634315, by decide⟩
    (prefixCache 11 19404) (prefixPartial 11 19404) = false := by
  decide +kernel

theorem node_context_11_19404_634315 : EJMOriginalGlobalDAGData.nodes 10 ⟨634315, by decide⟩ =
    .split (coordinate 11) (![⟨445562, by decide⟩,⟨634174, by decide⟩,⟨634247, by decide⟩,⟨634314, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19404_634315 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19404 ⟨634315, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19404
    ⟨634315, by decide⟩ (by decide) (![⟨445562, by decide⟩,⟨634174, by decide⟩,⟨634247, by decide⟩,⟨634314, by decide⟩]) unmarked_context_11_19404_634315 node_context_11_19404_634315
  intro a
  fin_cases a
  · exact context_12_77616_445562
  · exact context_12_77617_634174
  · exact context_12_77618_634247
  · exact context_12_77619_634314

theorem selected_cut_25087 : selected 9 ⟨475533, by decide⟩
    (prefixPartial 12 77620) = some ⟨12, 1, 0, 475533, 77620, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77620_475533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77620 ⟨475533, by decide⟩ :=
  accepted_of_selected 12 77620 ⟨475533, by decide⟩ ⟨12, 1, 0, 475533, 77620, 1, 65536⟩
    (by decide) selected_cut_25087

theorem selected_cut_25088 : selected 8 ⟨634322, by decide⟩
    (prefixPartial 13 310484) = some ⟨13, 2, 0, 634322, 310484, 253, 16384⟩ := by
  decide +kernel

theorem context_13_310484_634322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310484 ⟨634322, by decide⟩ :=
  accepted_of_selected 13 310484 ⟨634322, by decide⟩ ⟨13, 2, 0, 634322, 310484, 253, 16384⟩
    (by decide) selected_cut_25088

theorem selected_cut_25089 : selected 8 ⟨634351, by decide⟩
    (prefixPartial 13 310485) = some ⟨13, 2, 0, 634351, 310485, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_310485_634351 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310485 ⟨634351, by decide⟩ :=
  accepted_of_selected 13 310485 ⟨634351, by decide⟩ ⟨13, 2, 0, 634351, 310485, 2389, 16384⟩
    (by decide) selected_cut_25089

theorem selected_cut_25090 : selected 8 ⟨634373, by decide⟩
    (prefixPartial 13 310486) = some ⟨13, 2, 0, 634373, 310486, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_310486_634373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310486 ⟨634373, by decide⟩ :=
  accepted_of_selected 13 310486 ⟨634373, by decide⟩ ⟨13, 2, 0, 634373, 310486, 1973, 16384⟩
    (by decide) selected_cut_25090

theorem selected_cut_25091 : selected 8 ⟨634380, by decide⟩
    (prefixPartial 13 310487) = some ⟨13, 2, 0, 634380, 310487, 777, 16384⟩ := by
  decide +kernel

theorem context_13_310487_634380 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310487 ⟨634380, by decide⟩ :=
  accepted_of_selected 13 310487 ⟨634380, by decide⟩ ⟨13, 2, 0, 634380, 310487, 777, 16384⟩
    (by decide) selected_cut_25091

theorem unmarked_context_12_77621_634381 : frontier 9 ⟨634381, by decide⟩
    (prefixCache 12 77621) (prefixPartial 12 77621) = false := by
  decide +kernel

theorem node_context_12_77621_634381 : EJMOriginalGlobalDAGData.nodes 9 ⟨634381, by decide⟩ =
    .split (coordinate 12) (![⟨634322, by decide⟩,⟨634351, by decide⟩,⟨634373, by decide⟩,⟨634380, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77621_634381 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77621 ⟨634381, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77621
    ⟨634381, by decide⟩ (by decide) (![⟨634322, by decide⟩,⟨634351, by decide⟩,⟨634373, by decide⟩,⟨634380, by decide⟩]) unmarked_context_12_77621_634381 node_context_12_77621_634381
  intro a
  fin_cases a
  · exact context_13_310484_634322
  · exact context_13_310485_634351
  · exact context_13_310486_634373
  · exact context_13_310487_634380

theorem selected_cut_25092 : selected 8 ⟨634388, by decide⟩
    (prefixPartial 13 310488) = some ⟨13, 2, 0, 634388, 310488, 233, 16384⟩ := by
  decide +kernel

theorem context_13_310488_634388 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310488 ⟨634388, by decide⟩ :=
  accepted_of_selected 13 310488 ⟨634388, by decide⟩ ⟨13, 2, 0, 634388, 310488, 233, 16384⟩
    (by decide) selected_cut_25092

theorem selected_cut_25093 : selected 8 ⟨634413, by decide⟩
    (prefixPartial 13 310489) = some ⟨13, 2, 0, 634413, 310489, 2377, 16384⟩ := by
  decide +kernel

theorem context_13_310489_634413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310489 ⟨634413, by decide⟩ :=
  accepted_of_selected 13 310489 ⟨634413, by decide⟩ ⟨13, 2, 0, 634413, 310489, 2377, 16384⟩
    (by decide) selected_cut_25093

theorem selected_cut_25094 : selected 8 ⟨634434, by decide⟩
    (prefixPartial 13 310490) = some ⟨13, 2, 0, 634434, 310490, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_310490_634434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310490 ⟨634434, by decide⟩ :=
  accepted_of_selected 13 310490 ⟨634434, by decide⟩ ⟨13, 2, 0, 634434, 310490, 1725, 16384⟩
    (by decide) selected_cut_25094

theorem selected_cut_25095 : selected 8 ⟨634443, by decide⟩
    (prefixPartial 13 310491) = some ⟨13, 2, 0, 634443, 310491, 829, 16384⟩ := by
  decide +kernel

theorem context_13_310491_634443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310491 ⟨634443, by decide⟩ :=
  accepted_of_selected 13 310491 ⟨634443, by decide⟩ ⟨13, 2, 0, 634443, 310491, 829, 16384⟩
    (by decide) selected_cut_25095

theorem unmarked_context_12_77622_634444 : frontier 9 ⟨634444, by decide⟩
    (prefixCache 12 77622) (prefixPartial 12 77622) = false := by
  decide +kernel

theorem node_context_12_77622_634444 : EJMOriginalGlobalDAGData.nodes 9 ⟨634444, by decide⟩ =
    .split (coordinate 12) (![⟨634388, by decide⟩,⟨634413, by decide⟩,⟨634434, by decide⟩,⟨634443, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77622_634444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77622 ⟨634444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77622
    ⟨634444, by decide⟩ (by decide) (![⟨634388, by decide⟩,⟨634413, by decide⟩,⟨634434, by decide⟩,⟨634443, by decide⟩]) unmarked_context_12_77622_634444 node_context_12_77622_634444
  intro a
  fin_cases a
  · exact context_13_310488_634388
  · exact context_13_310489_634413
  · exact context_13_310490_634434
  · exact context_13_310491_634443

theorem selected_cut_25096 : selected 8 ⟨634449, by decide⟩
    (prefixPartial 13 310492) = some ⟨13, 2, 0, 634449, 310492, 209, 16384⟩ := by
  decide +kernel

theorem context_13_310492_634449 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310492 ⟨634449, by decide⟩ :=
  accepted_of_selected 13 310492 ⟨634449, by decide⟩ ⟨13, 2, 0, 634449, 310492, 209, 16384⟩
    (by decide) selected_cut_25096

theorem selected_cut_25097 : selected 8 ⟨634476, by decide⟩
    (prefixPartial 13 310493) = some ⟨13, 2, 0, 634476, 310493, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_310493_634476 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310493 ⟨634476, by decide⟩ :=
  accepted_of_selected 13 310493 ⟨634476, by decide⟩ ⟨13, 2, 0, 634476, 310493, 2201, 16384⟩
    (by decide) selected_cut_25097

theorem selected_cut_25098 : selected 8 ⟨634496, by decide⟩
    (prefixPartial 13 310494) = some ⟨13, 2, 0, 634496, 310494, 1789, 16384⟩ := by
  decide +kernel

theorem context_13_310494_634496 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310494 ⟨634496, by decide⟩ :=
  accepted_of_selected 13 310494 ⟨634496, by decide⟩ ⟨13, 2, 0, 634496, 310494, 1789, 16384⟩
    (by decide) selected_cut_25098

theorem selected_cut_25099 : selected 8 ⟨634503, by decide⟩
    (prefixPartial 13 310495) = some ⟨13, 2, 0, 634503, 310495, 765, 16384⟩ := by
  decide +kernel

theorem context_13_310495_634503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310495 ⟨634503, by decide⟩ :=
  accepted_of_selected 13 310495 ⟨634503, by decide⟩ ⟨13, 2, 0, 634503, 310495, 765, 16384⟩
    (by decide) selected_cut_25099

theorem unmarked_context_12_77623_634504 : frontier 9 ⟨634504, by decide⟩
    (prefixCache 12 77623) (prefixPartial 12 77623) = false := by
  decide +kernel

theorem node_context_12_77623_634504 : EJMOriginalGlobalDAGData.nodes 9 ⟨634504, by decide⟩ =
    .split (coordinate 12) (![⟨634449, by decide⟩,⟨634476, by decide⟩,⟨634496, by decide⟩,⟨634503, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77623_634504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77623 ⟨634504, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77623
    ⟨634504, by decide⟩ (by decide) (![⟨634449, by decide⟩,⟨634476, by decide⟩,⟨634496, by decide⟩,⟨634503, by decide⟩]) unmarked_context_12_77623_634504 node_context_12_77623_634504
  intro a
  fin_cases a
  · exact context_13_310492_634449
  · exact context_13_310493_634476
  · exact context_13_310494_634496
  · exact context_13_310495_634503

theorem unmarked_context_11_19405_634505 : frontier 10 ⟨634505, by decide⟩
    (prefixCache 11 19405) (prefixPartial 11 19405) = false := by
  decide +kernel

theorem node_context_11_19405_634505 : EJMOriginalGlobalDAGData.nodes 10 ⟨634505, by decide⟩ =
    .split (coordinate 11) (![⟨475533, by decide⟩,⟨634381, by decide⟩,⟨634444, by decide⟩,⟨634504, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19405_634505 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19405 ⟨634505, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19405
    ⟨634505, by decide⟩ (by decide) (![⟨475533, by decide⟩,⟨634381, by decide⟩,⟨634444, by decide⟩,⟨634504, by decide⟩]) unmarked_context_11_19405_634505 node_context_11_19405_634505
  intro a
  fin_cases a
  · exact context_12_77620_475533
  · exact context_12_77621_634381
  · exact context_12_77622_634444
  · exact context_12_77623_634504

theorem selected_cut_25100 : selected 9 ⟨540780, by decide⟩
    (prefixPartial 12 77624) = some ⟨12, 1, 0, 540780, 77624, 1, 65536⟩ := by
  decide +kernel

theorem context_12_77624_540780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77624 ⟨540780, by decide⟩ :=
  accepted_of_selected 12 77624 ⟨540780, by decide⟩ ⟨12, 1, 0, 540780, 77624, 1, 65536⟩
    (by decide) selected_cut_25100

theorem selected_cut_25101 : selected 8 ⟨634509, by decide⟩
    (prefixPartial 13 310500) = some ⟨13, 2, 0, 634509, 310500, 201, 16384⟩ := by
  decide +kernel

theorem context_13_310500_634509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310500 ⟨634509, by decide⟩ :=
  accepted_of_selected 13 310500 ⟨634509, by decide⟩ ⟨13, 2, 0, 634509, 310500, 201, 16384⟩
    (by decide) selected_cut_25101

theorem selected_cut_25102 : selected 8 ⟨634559, by decide⟩
    (prefixPartial 13 310501) = some ⟨13, 2, 0, 634559, 310501, 2665, 16384⟩ := by
  decide +kernel

theorem context_13_310501_634559 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310501 ⟨634559, by decide⟩ :=
  accepted_of_selected 13 310501 ⟨634559, by decide⟩ ⟨13, 2, 0, 634559, 310501, 2665, 16384⟩
    (by decide) selected_cut_25102

theorem selected_cut_25103 : selected 8 ⟨634583, by decide⟩
    (prefixPartial 13 310502) = some ⟨13, 2, 0, 634583, 310502, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_310502_634583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310502 ⟨634583, by decide⟩ :=
  accepted_of_selected 13 310502 ⟨634583, by decide⟩ ⟨13, 2, 0, 634583, 310502, 1949, 16384⟩
    (by decide) selected_cut_25103

theorem selected_cut_25104 : selected 8 ⟨634598, by decide⟩
    (prefixPartial 13 310503) = some ⟨13, 2, 0, 634598, 310503, 929, 16384⟩ := by
  decide +kernel

theorem context_13_310503_634598 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310503 ⟨634598, by decide⟩ :=
  accepted_of_selected 13 310503 ⟨634598, by decide⟩ ⟨13, 2, 0, 634598, 310503, 929, 16384⟩
    (by decide) selected_cut_25104

theorem unmarked_context_12_77625_634599 : frontier 9 ⟨634599, by decide⟩
    (prefixCache 12 77625) (prefixPartial 12 77625) = false := by
  decide +kernel

theorem node_context_12_77625_634599 : EJMOriginalGlobalDAGData.nodes 9 ⟨634599, by decide⟩ =
    .split (coordinate 12) (![⟨634509, by decide⟩,⟨634559, by decide⟩,⟨634583, by decide⟩,⟨634598, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77625_634599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77625 ⟨634599, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77625
    ⟨634599, by decide⟩ (by decide) (![⟨634509, by decide⟩,⟨634559, by decide⟩,⟨634583, by decide⟩,⟨634598, by decide⟩]) unmarked_context_12_77625_634599 node_context_12_77625_634599
  intro a
  fin_cases a
  · exact context_13_310500_634509
  · exact context_13_310501_634559
  · exact context_13_310502_634583
  · exact context_13_310503_634598

theorem selected_cut_25105 : selected 8 ⟨634602, by decide⟩
    (prefixPartial 13 310504) = some ⟨13, 2, 0, 634602, 310504, 89, 16384⟩ := by
  decide +kernel

theorem context_13_310504_634602 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310504 ⟨634602, by decide⟩ :=
  accepted_of_selected 13 310504 ⟨634602, by decide⟩ ⟨13, 2, 0, 634602, 310504, 89, 16384⟩
    (by decide) selected_cut_25105

theorem selected_cut_25106 : selected 8 ⟨634643, by decide⟩
    (prefixPartial 13 310505) = some ⟨13, 2, 0, 634643, 310505, 2729, 16384⟩ := by
  decide +kernel

theorem context_13_310505_634643 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310505 ⟨634643, by decide⟩ :=
  accepted_of_selected 13 310505 ⟨634643, by decide⟩ ⟨13, 2, 0, 634643, 310505, 2729, 16384⟩
    (by decide) selected_cut_25106

theorem selected_cut_25107 : selected 8 ⟨634666, by decide⟩
    (prefixPartial 13 310506) = some ⟨13, 2, 0, 634666, 310506, 1693, 16384⟩ := by
  decide +kernel

theorem context_13_310506_634666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310506 ⟨634666, by decide⟩ :=
  accepted_of_selected 13 310506 ⟨634666, by decide⟩ ⟨13, 2, 0, 634666, 310506, 1693, 16384⟩
    (by decide) selected_cut_25107

theorem selected_cut_25108 : selected 8 ⟨634676, by decide⟩
    (prefixPartial 13 310507) = some ⟨13, 2, 0, 634676, 310507, 841, 16384⟩ := by
  decide +kernel

theorem context_13_310507_634676 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310507 ⟨634676, by decide⟩ :=
  accepted_of_selected 13 310507 ⟨634676, by decide⟩ ⟨13, 2, 0, 634676, 310507, 841, 16384⟩
    (by decide) selected_cut_25108

theorem unmarked_context_12_77626_634677 : frontier 9 ⟨634677, by decide⟩
    (prefixCache 12 77626) (prefixPartial 12 77626) = false := by
  decide +kernel

theorem node_context_12_77626_634677 : EJMOriginalGlobalDAGData.nodes 9 ⟨634677, by decide⟩ =
    .split (coordinate 12) (![⟨634602, by decide⟩,⟨634643, by decide⟩,⟨634666, by decide⟩,⟨634676, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77626_634677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77626 ⟨634677, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77626
    ⟨634677, by decide⟩ (by decide) (![⟨634602, by decide⟩,⟨634643, by decide⟩,⟨634666, by decide⟩,⟨634676, by decide⟩]) unmarked_context_12_77626_634677 node_context_12_77626_634677
  intro a
  fin_cases a
  · exact context_13_310504_634602
  · exact context_13_310505_634643
  · exact context_13_310506_634666
  · exact context_13_310507_634676

theorem selected_cut_25109 : selected 8 ⟨634681, by decide⟩
    (prefixPartial 13 310508) = some ⟨13, 2, 0, 634681, 310508, 69, 16384⟩ := by
  decide +kernel

theorem context_13_310508_634681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310508 ⟨634681, by decide⟩ :=
  accepted_of_selected 13 310508 ⟨634681, by decide⟩ ⟨13, 2, 0, 634681, 310508, 69, 16384⟩
    (by decide) selected_cut_25109

theorem selected_cut_25110 : selected 8 ⟨634709, by decide⟩
    (prefixPartial 13 310509) = some ⟨13, 2, 0, 634709, 310509, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_310509_634709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310509 ⟨634709, by decide⟩ :=
  accepted_of_selected 13 310509 ⟨634709, by decide⟩ ⟨13, 2, 0, 634709, 310509, 2689, 16384⟩
    (by decide) selected_cut_25110

theorem selected_cut_25111 : selected 8 ⟨634730, by decide⟩
    (prefixPartial 13 310510) = some ⟨13, 2, 0, 634730, 310510, 1657, 16384⟩ := by
  decide +kernel

theorem context_13_310510_634730 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310510 ⟨634730, by decide⟩ :=
  accepted_of_selected 13 310510 ⟨634730, by decide⟩ ⟨13, 2, 0, 634730, 310510, 1657, 16384⟩
    (by decide) selected_cut_25111

theorem selected_cut_25112 : selected 8 ⟨634744, by decide⟩
    (prefixPartial 13 310511) = some ⟨13, 2, 0, 634744, 310511, 829, 16384⟩ := by
  decide +kernel

theorem context_13_310511_634744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310511 ⟨634744, by decide⟩ :=
  accepted_of_selected 13 310511 ⟨634744, by decide⟩ ⟨13, 2, 0, 634744, 310511, 829, 16384⟩
    (by decide) selected_cut_25112

theorem unmarked_context_12_77627_634745 : frontier 9 ⟨634745, by decide⟩
    (prefixCache 12 77627) (prefixPartial 12 77627) = false := by
  decide +kernel

theorem node_context_12_77627_634745 : EJMOriginalGlobalDAGData.nodes 9 ⟨634745, by decide⟩ =
    .split (coordinate 12) (![⟨634681, by decide⟩,⟨634709, by decide⟩,⟨634730, by decide⟩,⟨634744, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77627_634745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77627 ⟨634745, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77627
    ⟨634745, by decide⟩ (by decide) (![⟨634681, by decide⟩,⟨634709, by decide⟩,⟨634730, by decide⟩,⟨634744, by decide⟩]) unmarked_context_12_77627_634745 node_context_12_77627_634745
  intro a
  fin_cases a
  · exact context_13_310508_634681
  · exact context_13_310509_634709
  · exact context_13_310510_634730
  · exact context_13_310511_634744

theorem unmarked_context_11_19406_634746 : frontier 10 ⟨634746, by decide⟩
    (prefixCache 11 19406) (prefixPartial 11 19406) = false := by
  decide +kernel

theorem node_context_11_19406_634746 : EJMOriginalGlobalDAGData.nodes 10 ⟨634746, by decide⟩ =
    .split (coordinate 11) (![⟨540780, by decide⟩,⟨634599, by decide⟩,⟨634677, by decide⟩,⟨634745, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19406_634746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19406 ⟨634746, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19406
    ⟨634746, by decide⟩ (by decide) (![⟨540780, by decide⟩,⟨634599, by decide⟩,⟨634677, by decide⟩,⟨634745, by decide⟩]) unmarked_context_11_19406_634746 node_context_11_19406_634746
  intro a
  fin_cases a
  · exact context_12_77624_540780
  · exact context_12_77625_634599
  · exact context_12_77626_634677
  · exact context_12_77627_634745

theorem selected_cut_25113 : selected 10 ⟨634747, by decide⟩
    (prefixPartial 11 19407) = some ⟨11, 2, 0, 634747, 19407, 5, 262144⟩ := by
  decide +kernel

theorem context_11_19407_634747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19407 ⟨634747, by decide⟩ :=
  accepted_of_selected 11 19407 ⟨634747, by decide⟩ ⟨11, 2, 0, 634747, 19407, 5, 262144⟩
    (by decide) selected_cut_25113

theorem unmarked_context_10_4851_634748 : frontier 11 ⟨634748, by decide⟩
    (prefixCache 10 4851) (prefixPartial 10 4851) = false := by
  decide +kernel

theorem node_context_10_4851_634748 : EJMOriginalGlobalDAGData.nodes 11 ⟨634748, by decide⟩ =
    .split (coordinate 10) (![⟨634315, by decide⟩,⟨634505, by decide⟩,⟨634746, by decide⟩,⟨634747, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4851_634748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4851 ⟨634748, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4851
    ⟨634748, by decide⟩ (by decide) (![⟨634315, by decide⟩,⟨634505, by decide⟩,⟨634746, by decide⟩,⟨634747, by decide⟩]) unmarked_context_10_4851_634748 node_context_10_4851_634748
  intro a
  fin_cases a
  · exact context_11_19404_634315
  · exact context_11_19405_634505
  · exact context_11_19406_634746
  · exact context_11_19407_634747

theorem unmarked_context_9_1212_634749 : frontier 12 ⟨634749, by decide⟩
    (prefixCache 9 1212) (prefixPartial 9 1212) = false := by
  decide +kernel

theorem node_context_9_1212_634749 : EJMOriginalGlobalDAGData.nodes 12 ⟨634749, by decide⟩ =
    .split (coordinate 9) (![⟨631211, by decide⟩,⟨632899, by decide⟩,⟨634086, by decide⟩,⟨634748, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1212_634749 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1212 ⟨634749, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1212
    ⟨634749, by decide⟩ (by decide) (![⟨631211, by decide⟩,⟨632899, by decide⟩,⟨634086, by decide⟩,⟨634748, by decide⟩]) unmarked_context_9_1212_634749 node_context_9_1212_634749
  intro a
  fin_cases a
  · exact context_10_4848_631211
  · exact context_10_4849_632899
  · exact context_10_4850_634086
  · exact context_10_4851_634748

theorem selected_cut_25114 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310528) = some ⟨13, 1, 0, 3444, 310528, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310528_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310528 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310528 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310528, 1, 16384⟩
    (by decide) selected_cut_25114

theorem selected_cut_25115 : selected 8 ⟨634791, by decide⟩
    (prefixPartial 13 310529) = some ⟨13, 2, 0, 634791, 310529, 2389, 16384⟩ := by
  decide +kernel

theorem context_13_310529_634791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310529 ⟨634791, by decide⟩ :=
  accepted_of_selected 13 310529 ⟨634791, by decide⟩ ⟨13, 2, 0, 634791, 310529, 2389, 16384⟩
    (by decide) selected_cut_25115

theorem selected_cut_25116 : selected 8 ⟨634813, by decide⟩
    (prefixPartial 13 310530) = some ⟨13, 2, 0, 634813, 310530, 1221, 16384⟩ := by
  decide +kernel

theorem context_13_310530_634813 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310530 ⟨634813, by decide⟩ :=
  accepted_of_selected 13 310530 ⟨634813, by decide⟩ ⟨13, 2, 0, 634813, 310530, 1221, 16384⟩
    (by decide) selected_cut_25116

theorem selected_cut_25117 : selected 8 ⟨634821, by decide⟩
    (prefixPartial 13 310531) = some ⟨13, 2, 0, 634821, 310531, 681, 16384⟩ := by
  decide +kernel

theorem context_13_310531_634821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310531 ⟨634821, by decide⟩ :=
  accepted_of_selected 13 310531 ⟨634821, by decide⟩ ⟨13, 2, 0, 634821, 310531, 681, 16384⟩
    (by decide) selected_cut_25117

theorem unmarked_context_12_77632_634822 : frontier 9 ⟨634822, by decide⟩
    (prefixCache 12 77632) (prefixPartial 12 77632) = false := by
  decide +kernel

theorem node_context_12_77632_634822 : EJMOriginalGlobalDAGData.nodes 9 ⟨634822, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨634791, by decide⟩,⟨634813, by decide⟩,⟨634821, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77632_634822 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77632 ⟨634822, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77632
    ⟨634822, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨634791, by decide⟩,⟨634813, by decide⟩,⟨634821, by decide⟩]) unmarked_context_12_77632_634822 node_context_12_77632_634822
  intro a
  fin_cases a
  · exact context_13_310528_3444
  · exact context_13_310529_634791
  · exact context_13_310530_634813
  · exact context_13_310531_634821

theorem selected_cut_25118 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310532) = some ⟨13, 1, 0, 3444, 310532, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310532_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310532 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310532 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310532, 1, 16384⟩
    (by decide) selected_cut_25118

theorem selected_cut_25119 : selected 8 ⟨634852, by decide⟩
    (prefixPartial 13 310533) = some ⟨13, 2, 0, 634852, 310533, 2349, 16384⟩ := by
  decide +kernel

theorem context_13_310533_634852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310533 ⟨634852, by decide⟩ :=
  accepted_of_selected 13 310533 ⟨634852, by decide⟩ ⟨13, 2, 0, 634852, 310533, 2349, 16384⟩
    (by decide) selected_cut_25119

theorem selected_cut_25120 : selected 8 ⟨634879, by decide⟩
    (prefixPartial 13 310534) = some ⟨13, 2, 0, 634879, 310534, 1549, 16384⟩ := by
  decide +kernel

theorem context_13_310534_634879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310534 ⟨634879, by decide⟩ :=
  accepted_of_selected 13 310534 ⟨634879, by decide⟩ ⟨13, 2, 0, 634879, 310534, 1549, 16384⟩
    (by decide) selected_cut_25120

theorem selected_cut_25121 : selected 8 ⟨634885, by decide⟩
    (prefixPartial 13 310535) = some ⟨13, 2, 0, 634885, 310535, 581, 16384⟩ := by
  decide +kernel

theorem context_13_310535_634885 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310535 ⟨634885, by decide⟩ :=
  accepted_of_selected 13 310535 ⟨634885, by decide⟩ ⟨13, 2, 0, 634885, 310535, 581, 16384⟩
    (by decide) selected_cut_25121

theorem unmarked_context_12_77633_634886 : frontier 9 ⟨634886, by decide⟩
    (prefixCache 12 77633) (prefixPartial 12 77633) = false := by
  decide +kernel

theorem node_context_12_77633_634886 : EJMOriginalGlobalDAGData.nodes 9 ⟨634886, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨634852, by decide⟩,⟨634879, by decide⟩,⟨634885, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77633_634886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77633 ⟨634886, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77633
    ⟨634886, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨634852, by decide⟩,⟨634879, by decide⟩,⟨634885, by decide⟩]) unmarked_context_12_77633_634886 node_context_12_77633_634886
  intro a
  fin_cases a
  · exact context_13_310532_3444
  · exact context_13_310533_634852
  · exact context_13_310534_634879
  · exact context_13_310535_634885

theorem selected_cut_25122 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310536) = some ⟨13, 1, 0, 3444, 310536, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310536_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310536 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310536 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310536, 1, 16384⟩
    (by decide) selected_cut_25122

theorem selected_cut_25123 : selected 8 ⟨634932, by decide⟩
    (prefixPartial 13 310537) = some ⟨13, 2, 0, 634932, 310537, 2753, 16384⟩ := by
  decide +kernel

theorem context_13_310537_634932 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310537 ⟨634932, by decide⟩ :=
  accepted_of_selected 13 310537 ⟨634932, by decide⟩ ⟨13, 2, 0, 634932, 310537, 2753, 16384⟩
    (by decide) selected_cut_25123

theorem selected_cut_25124 : selected 8 ⟨634956, by decide⟩
    (prefixPartial 13 310538) = some ⟨13, 2, 0, 634956, 310538, 1669, 16384⟩ := by
  decide +kernel

theorem context_13_310538_634956 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310538 ⟨634956, by decide⟩ :=
  accepted_of_selected 13 310538 ⟨634956, by decide⟩ ⟨13, 2, 0, 634956, 310538, 1669, 16384⟩
    (by decide) selected_cut_25124

theorem selected_cut_25125 : selected 8 ⟨634964, by decide⟩
    (prefixPartial 13 310539) = some ⟨13, 2, 0, 634964, 310539, 657, 16384⟩ := by
  decide +kernel

theorem context_13_310539_634964 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310539 ⟨634964, by decide⟩ :=
  accepted_of_selected 13 310539 ⟨634964, by decide⟩ ⟨13, 2, 0, 634964, 310539, 657, 16384⟩
    (by decide) selected_cut_25125

theorem unmarked_context_12_77634_634965 : frontier 9 ⟨634965, by decide⟩
    (prefixCache 12 77634) (prefixPartial 12 77634) = false := by
  decide +kernel

theorem node_context_12_77634_634965 : EJMOriginalGlobalDAGData.nodes 9 ⟨634965, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨634932, by decide⟩,⟨634956, by decide⟩,⟨634964, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77634_634965 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77634 ⟨634965, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77634
    ⟨634965, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨634932, by decide⟩,⟨634956, by decide⟩,⟨634964, by decide⟩]) unmarked_context_12_77634_634965 node_context_12_77634_634965
  intro a
  fin_cases a
  · exact context_13_310536_3444
  · exact context_13_310537_634932
  · exact context_13_310538_634956
  · exact context_13_310539_634964

theorem selected_cut_25126 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310540) = some ⟨13, 1, 0, 3444, 310540, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310540_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310540 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310540 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310540, 1, 16384⟩
    (by decide) selected_cut_25126

theorem selected_cut_25127 : selected 8 ⟨634996, by decide⟩
    (prefixPartial 13 310541) = some ⟨13, 2, 0, 634996, 310541, 2553, 16384⟩ := by
  decide +kernel

theorem context_13_310541_634996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310541 ⟨634996, by decide⟩ :=
  accepted_of_selected 13 310541 ⟨634996, by decide⟩ ⟨13, 2, 0, 634996, 310541, 2553, 16384⟩
    (by decide) selected_cut_25127

theorem selected_cut_25128 : selected 8 ⟨635019, by decide⟩
    (prefixPartial 13 310542) = some ⟨13, 2, 0, 635019, 310542, 1477, 16384⟩ := by
  decide +kernel

theorem context_13_310542_635019 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310542 ⟨635019, by decide⟩ :=
  accepted_of_selected 13 310542 ⟨635019, by decide⟩ ⟨13, 2, 0, 635019, 310542, 1477, 16384⟩
    (by decide) selected_cut_25128

theorem selected_cut_25129 : selected 8 ⟨635025, by decide⟩
    (prefixPartial 13 310543) = some ⟨13, 2, 0, 635025, 310543, 689, 16384⟩ := by
  decide +kernel

theorem context_13_310543_635025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310543 ⟨635025, by decide⟩ :=
  accepted_of_selected 13 310543 ⟨635025, by decide⟩ ⟨13, 2, 0, 635025, 310543, 689, 16384⟩
    (by decide) selected_cut_25129

theorem unmarked_context_12_77635_635026 : frontier 9 ⟨635026, by decide⟩
    (prefixCache 12 77635) (prefixPartial 12 77635) = false := by
  decide +kernel

theorem node_context_12_77635_635026 : EJMOriginalGlobalDAGData.nodes 9 ⟨635026, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨634996, by decide⟩,⟨635019, by decide⟩,⟨635025, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77635_635026 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77635 ⟨635026, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77635
    ⟨635026, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨634996, by decide⟩,⟨635019, by decide⟩,⟨635025, by decide⟩]) unmarked_context_12_77635_635026 node_context_12_77635_635026
  intro a
  fin_cases a
  · exact context_13_310540_3444
  · exact context_13_310541_634996
  · exact context_13_310542_635019
  · exact context_13_310543_635025

theorem unmarked_context_11_19408_635027 : frontier 10 ⟨635027, by decide⟩
    (prefixCache 11 19408) (prefixPartial 11 19408) = false := by
  decide +kernel

theorem node_context_11_19408_635027 : EJMOriginalGlobalDAGData.nodes 10 ⟨635027, by decide⟩ =
    .split (coordinate 11) (![⟨634822, by decide⟩,⟨634886, by decide⟩,⟨634965, by decide⟩,⟨635026, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19408_635027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19408 ⟨635027, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19408
    ⟨635027, by decide⟩ (by decide) (![⟨634822, by decide⟩,⟨634886, by decide⟩,⟨634965, by decide⟩,⟨635026, by decide⟩]) unmarked_context_11_19408_635027 node_context_11_19408_635027
  intro a
  fin_cases a
  · exact context_12_77632_634822
  · exact context_12_77633_634886
  · exact context_12_77634_634965
  · exact context_12_77635_635026

theorem selected_cut_25130 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310544) = some ⟨13, 1, 0, 3444, 310544, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310544_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310544 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310544 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310544, 1, 16384⟩
    (by decide) selected_cut_25130

theorem selected_cut_25131 : selected 8 ⟨635066, by decide⟩
    (prefixPartial 13 310545) = some ⟨13, 2, 0, 635066, 310545, 2209, 16384⟩ := by
  decide +kernel

theorem context_13_310545_635066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310545 ⟨635066, by decide⟩ :=
  accepted_of_selected 13 310545 ⟨635066, by decide⟩ ⟨13, 2, 0, 635066, 310545, 2209, 16384⟩
    (by decide) selected_cut_25131

theorem selected_cut_25132 : selected 8 ⟨635091, by decide⟩
    (prefixPartial 13 310546) = some ⟨13, 2, 0, 635091, 310546, 1361, 16384⟩ := by
  decide +kernel

theorem context_13_310546_635091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310546 ⟨635091, by decide⟩ :=
  accepted_of_selected 13 310546 ⟨635091, by decide⟩ ⟨13, 2, 0, 635091, 310546, 1361, 16384⟩
    (by decide) selected_cut_25132

theorem selected_cut_25133 : selected 8 ⟨635100, by decide⟩
    (prefixPartial 13 310547) = some ⟨13, 2, 0, 635100, 310547, 717, 16384⟩ := by
  decide +kernel

theorem context_13_310547_635100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310547 ⟨635100, by decide⟩ :=
  accepted_of_selected 13 310547 ⟨635100, by decide⟩ ⟨13, 2, 0, 635100, 310547, 717, 16384⟩
    (by decide) selected_cut_25133

theorem unmarked_context_12_77636_635101 : frontier 9 ⟨635101, by decide⟩
    (prefixCache 12 77636) (prefixPartial 12 77636) = false := by
  decide +kernel

theorem node_context_12_77636_635101 : EJMOriginalGlobalDAGData.nodes 9 ⟨635101, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635066, by decide⟩,⟨635091, by decide⟩,⟨635100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77636_635101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77636 ⟨635101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77636
    ⟨635101, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635066, by decide⟩,⟨635091, by decide⟩,⟨635100, by decide⟩]) unmarked_context_12_77636_635101 node_context_12_77636_635101
  intro a
  fin_cases a
  · exact context_13_310544_3444
  · exact context_13_310545_635066
  · exact context_13_310546_635091
  · exact context_13_310547_635100

theorem selected_cut_25134 : selected 9 ⟨635155, by decide⟩
    (prefixPartial 12 77637) = some ⟨12, 2, 0, 635155, 77637, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_77637_635155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77637 ⟨635155, by decide⟩ :=
  accepted_of_selected 12 77637 ⟨635155, by decide⟩ ⟨12, 2, 0, 635155, 77637, 4077, 65536⟩
    (by decide) selected_cut_25134

theorem selected_cut_25135 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310552) = some ⟨13, 1, 0, 3444, 310552, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310552_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310552 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310552 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310552, 1, 16384⟩
    (by decide) selected_cut_25135

theorem selected_cut_25136 : selected 8 ⟨635193, by decide⟩
    (prefixPartial 13 310553) = some ⟨13, 2, 0, 635193, 310553, 2429, 16384⟩ := by
  decide +kernel

theorem context_13_310553_635193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310553 ⟨635193, by decide⟩ :=
  accepted_of_selected 13 310553 ⟨635193, by decide⟩ ⟨13, 2, 0, 635193, 310553, 2429, 16384⟩
    (by decide) selected_cut_25136

theorem selected_cut_25137 : selected 8 ⟨635218, by decide⟩
    (prefixPartial 13 310554) = some ⟨13, 2, 0, 635218, 310554, 1677, 16384⟩ := by
  decide +kernel

theorem context_13_310554_635218 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310554 ⟨635218, by decide⟩ :=
  accepted_of_selected 13 310554 ⟨635218, by decide⟩ ⟨13, 2, 0, 635218, 310554, 1677, 16384⟩
    (by decide) selected_cut_25137

theorem selected_cut_25138 : selected 8 ⟨635228, by decide⟩
    (prefixPartial 13 310555) = some ⟨13, 2, 0, 635228, 310555, 769, 16384⟩ := by
  decide +kernel

theorem context_13_310555_635228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310555 ⟨635228, by decide⟩ :=
  accepted_of_selected 13 310555 ⟨635228, by decide⟩ ⟨13, 2, 0, 635228, 310555, 769, 16384⟩
    (by decide) selected_cut_25138

theorem unmarked_context_12_77638_635229 : frontier 9 ⟨635229, by decide⟩
    (prefixCache 12 77638) (prefixPartial 12 77638) = false := by
  decide +kernel

theorem node_context_12_77638_635229 : EJMOriginalGlobalDAGData.nodes 9 ⟨635229, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635193, by decide⟩,⟨635218, by decide⟩,⟨635228, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77638_635229 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77638 ⟨635229, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77638
    ⟨635229, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635193, by decide⟩,⟨635218, by decide⟩,⟨635228, by decide⟩]) unmarked_context_12_77638_635229 node_context_12_77638_635229
  intro a
  fin_cases a
  · exact context_13_310552_3444
  · exact context_13_310553_635193
  · exact context_13_310554_635218
  · exact context_13_310555_635228

theorem selected_cut_25139 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310556) = some ⟨13, 1, 0, 3444, 310556, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310556_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310556 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310556 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310556, 1, 16384⟩
    (by decide) selected_cut_25139

theorem selected_cut_25140 : selected 8 ⟨635262, by decide⟩
    (prefixPartial 13 310557) = some ⟨13, 2, 0, 635262, 310557, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_310557_635262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310557 ⟨635262, by decide⟩ :=
  accepted_of_selected 13 310557 ⟨635262, by decide⟩ ⟨13, 2, 0, 635262, 310557, 2277, 16384⟩
    (by decide) selected_cut_25140

theorem selected_cut_25141 : selected 8 ⟨635292, by decide⟩
    (prefixPartial 13 310558) = some ⟨13, 2, 0, 635292, 310558, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_310558_635292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310558 ⟨635292, by decide⟩ :=
  accepted_of_selected 13 310558 ⟨635292, by decide⟩ ⟨13, 2, 0, 635292, 310558, 1601, 16384⟩
    (by decide) selected_cut_25141

theorem selected_cut_25142 : selected 8 ⟨635300, by decide⟩
    (prefixPartial 13 310559) = some ⟨13, 2, 0, 635300, 310559, 777, 16384⟩ := by
  decide +kernel

theorem context_13_310559_635300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310559 ⟨635300, by decide⟩ :=
  accepted_of_selected 13 310559 ⟨635300, by decide⟩ ⟨13, 2, 0, 635300, 310559, 777, 16384⟩
    (by decide) selected_cut_25142

theorem unmarked_context_12_77639_635301 : frontier 9 ⟨635301, by decide⟩
    (prefixCache 12 77639) (prefixPartial 12 77639) = false := by
  decide +kernel

theorem node_context_12_77639_635301 : EJMOriginalGlobalDAGData.nodes 9 ⟨635301, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635262, by decide⟩,⟨635292, by decide⟩,⟨635300, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77639_635301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77639 ⟨635301, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77639
    ⟨635301, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635262, by decide⟩,⟨635292, by decide⟩,⟨635300, by decide⟩]) unmarked_context_12_77639_635301 node_context_12_77639_635301
  intro a
  fin_cases a
  · exact context_13_310556_3444
  · exact context_13_310557_635262
  · exact context_13_310558_635292
  · exact context_13_310559_635300

theorem unmarked_context_11_19409_635302 : frontier 10 ⟨635302, by decide⟩
    (prefixCache 11 19409) (prefixPartial 11 19409) = false := by
  decide +kernel

theorem node_context_11_19409_635302 : EJMOriginalGlobalDAGData.nodes 10 ⟨635302, by decide⟩ =
    .split (coordinate 11) (![⟨635101, by decide⟩,⟨635155, by decide⟩,⟨635229, by decide⟩,⟨635301, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_19409_635302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 19409 ⟨635302, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 19409
    ⟨635302, by decide⟩ (by decide) (![⟨635101, by decide⟩,⟨635155, by decide⟩,⟨635229, by decide⟩,⟨635301, by decide⟩]) unmarked_context_11_19409_635302 node_context_11_19409_635302
  intro a
  fin_cases a
  · exact context_12_77636_635101
  · exact context_12_77637_635155
  · exact context_12_77638_635229
  · exact context_12_77639_635301

theorem selected_cut_25143 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310560) = some ⟨13, 1, 0, 3444, 310560, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310560_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310560 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310560 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310560, 1, 16384⟩
    (by decide) selected_cut_25143

theorem selected_cut_25144 : selected 8 ⟨635337, by decide⟩
    (prefixPartial 13 310561) = some ⟨13, 2, 0, 635337, 310561, 2237, 16384⟩ := by
  decide +kernel

theorem context_13_310561_635337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310561 ⟨635337, by decide⟩ :=
  accepted_of_selected 13 310561 ⟨635337, by decide⟩ ⟨13, 2, 0, 635337, 310561, 2237, 16384⟩
    (by decide) selected_cut_25144

theorem selected_cut_25145 : selected 8 ⟨635358, by decide⟩
    (prefixPartial 13 310562) = some ⟨13, 2, 0, 635358, 310562, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_310562_635358 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310562 ⟨635358, by decide⟩ :=
  accepted_of_selected 13 310562 ⟨635358, by decide⟩ ⟨13, 2, 0, 635358, 310562, 1293, 16384⟩
    (by decide) selected_cut_25145

theorem selected_cut_25146 : selected 8 ⟨635366, by decide⟩
    (prefixPartial 13 310563) = some ⟨13, 2, 0, 635366, 310563, 729, 16384⟩ := by
  decide +kernel

theorem context_13_310563_635366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310563 ⟨635366, by decide⟩ :=
  accepted_of_selected 13 310563 ⟨635366, by decide⟩ ⟨13, 2, 0, 635366, 310563, 729, 16384⟩
    (by decide) selected_cut_25146

theorem unmarked_context_12_77640_635367 : frontier 9 ⟨635367, by decide⟩
    (prefixCache 12 77640) (prefixPartial 12 77640) = false := by
  decide +kernel

theorem node_context_12_77640_635367 : EJMOriginalGlobalDAGData.nodes 9 ⟨635367, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635337, by decide⟩,⟨635358, by decide⟩,⟨635366, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77640_635367 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77640 ⟨635367, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77640
    ⟨635367, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635337, by decide⟩,⟨635358, by decide⟩,⟨635366, by decide⟩]) unmarked_context_12_77640_635367 node_context_12_77640_635367
  intro a
  fin_cases a
  · exact context_13_310560_3444
  · exact context_13_310561_635337
  · exact context_13_310562_635358
  · exact context_13_310563_635366

theorem selected_cut_25147 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310564) = some ⟨13, 1, 0, 3444, 310564, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310564_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310564 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310564 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310564, 1, 16384⟩
    (by decide) selected_cut_25147

theorem selected_cut_25148 : selected 8 ⟨635394, by decide⟩
    (prefixPartial 13 310565) = some ⟨13, 2, 0, 635394, 310565, 1949, 16384⟩ := by
  decide +kernel

theorem context_13_310565_635394 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310565 ⟨635394, by decide⟩ :=
  accepted_of_selected 13 310565 ⟨635394, by decide⟩ ⟨13, 2, 0, 635394, 310565, 1949, 16384⟩
    (by decide) selected_cut_25148

theorem selected_cut_25149 : selected 8 ⟨635417, by decide⟩
    (prefixPartial 13 310566) = some ⟨13, 2, 0, 635417, 310566, 1609, 16384⟩ := by
  decide +kernel

theorem context_13_310566_635417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310566 ⟨635417, by decide⟩ :=
  accepted_of_selected 13 310566 ⟨635417, by decide⟩ ⟨13, 2, 0, 635417, 310566, 1609, 16384⟩
    (by decide) selected_cut_25149

theorem selected_cut_25150 : selected 8 ⟨635427, by decide⟩
    (prefixPartial 13 310567) = some ⟨13, 2, 0, 635427, 310567, 669, 16384⟩ := by
  decide +kernel

theorem context_13_310567_635427 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310567 ⟨635427, by decide⟩ :=
  accepted_of_selected 13 310567 ⟨635427, by decide⟩ ⟨13, 2, 0, 635427, 310567, 669, 16384⟩
    (by decide) selected_cut_25150

theorem unmarked_context_12_77641_635428 : frontier 9 ⟨635428, by decide⟩
    (prefixCache 12 77641) (prefixPartial 12 77641) = false := by
  decide +kernel

theorem node_context_12_77641_635428 : EJMOriginalGlobalDAGData.nodes 9 ⟨635428, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635394, by decide⟩,⟨635417, by decide⟩,⟨635427, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77641_635428 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77641 ⟨635428, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77641
    ⟨635428, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635394, by decide⟩,⟨635417, by decide⟩,⟨635427, by decide⟩]) unmarked_context_12_77641_635428 node_context_12_77641_635428
  intro a
  fin_cases a
  · exact context_13_310564_3444
  · exact context_13_310565_635394
  · exact context_13_310566_635417
  · exact context_13_310567_635427

theorem selected_cut_25151 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310568) = some ⟨13, 1, 0, 3444, 310568, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310568_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310568 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310568 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310568, 1, 16384⟩
    (by decide) selected_cut_25151

theorem selected_cut_25152 : selected 8 ⟨635466, by decide⟩
    (prefixPartial 13 310569) = some ⟨13, 2, 0, 635466, 310569, 2309, 16384⟩ := by
  decide +kernel

theorem context_13_310569_635466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310569 ⟨635466, by decide⟩ :=
  accepted_of_selected 13 310569 ⟨635466, by decide⟩ ⟨13, 2, 0, 635466, 310569, 2309, 16384⟩
    (by decide) selected_cut_25152

theorem selected_cut_25153 : selected 8 ⟨635486, by decide⟩
    (prefixPartial 13 310570) = some ⟨13, 2, 0, 635486, 310570, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_310570_635486 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310570 ⟨635486, by decide⟩ :=
  accepted_of_selected 13 310570 ⟨635486, by decide⟩ ⟨13, 2, 0, 635486, 310570, 1709, 16384⟩
    (by decide) selected_cut_25153

theorem selected_cut_25154 : selected 8 ⟨635494, by decide⟩
    (prefixPartial 13 310571) = some ⟨13, 2, 0, 635494, 310571, 745, 16384⟩ := by
  decide +kernel

theorem context_13_310571_635494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310571 ⟨635494, by decide⟩ :=
  accepted_of_selected 13 310571 ⟨635494, by decide⟩ ⟨13, 2, 0, 635494, 310571, 745, 16384⟩
    (by decide) selected_cut_25154

theorem unmarked_context_12_77642_635495 : frontier 9 ⟨635495, by decide⟩
    (prefixCache 12 77642) (prefixPartial 12 77642) = false := by
  decide +kernel

theorem node_context_12_77642_635495 : EJMOriginalGlobalDAGData.nodes 9 ⟨635495, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨635466, by decide⟩,⟨635486, by decide⟩,⟨635494, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_77642_635495 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 77642 ⟨635495, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 77642
    ⟨635495, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨635466, by decide⟩,⟨635486, by decide⟩,⟨635494, by decide⟩]) unmarked_context_12_77642_635495 node_context_12_77642_635495
  intro a
  fin_cases a
  · exact context_13_310568_3444
  · exact context_13_310569_635466
  · exact context_13_310570_635486
  · exact context_13_310571_635494

theorem selected_cut_25155 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 310572) = some ⟨13, 1, 0, 3444, 310572, 1, 16384⟩ := by
  decide +kernel

theorem context_13_310572_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 310572 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 310572 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 310572, 1, 16384⟩
    (by decide) selected_cut_25155

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
