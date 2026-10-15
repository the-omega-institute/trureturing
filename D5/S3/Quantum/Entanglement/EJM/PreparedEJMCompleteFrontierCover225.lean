/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover224
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_21602 : selected 9 ⟨552155, by decide⟩
    (prefixPartial 12 75104) = some ⟨12, 2, 0, 552155, 75104, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_75104_552155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75104 ⟨552155, by decide⟩ :=
  accepted_of_selected 12 75104 ⟨552155, by decide⟩ ⟨12, 2, 0, 552155, 75104, 3557, 65536⟩
    (by decide) selected_cut_21602

theorem selected_cut_21603 : selected 9 ⟨552192, by decide⟩
    (prefixPartial 12 75105) = some ⟨12, 2, 0, 552192, 75105, 3193, 65536⟩ := by
  decide +kernel

theorem context_12_75105_552192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75105 ⟨552192, by decide⟩ :=
  accepted_of_selected 12 75105 ⟨552192, by decide⟩ ⟨12, 2, 0, 552192, 75105, 3193, 65536⟩
    (by decide) selected_cut_21603

theorem selected_cut_21604 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300424) = some ⟨13, 1, 0, 3444, 300424, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300424_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300424 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300424 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300424, 1, 16384⟩
    (by decide) selected_cut_21604

theorem selected_cut_21605 : selected 8 ⟨552211, by decide⟩
    (prefixPartial 13 300425) = some ⟨13, 2, 0, 552211, 300425, 1217, 16384⟩ := by
  decide +kernel

theorem context_13_300425_552211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300425 ⟨552211, by decide⟩ :=
  accepted_of_selected 13 300425 ⟨552211, by decide⟩ ⟨13, 2, 0, 552211, 300425, 1217, 16384⟩
    (by decide) selected_cut_21605

theorem selected_cut_21606 : selected 8 ⟨552237, by decide⟩
    (prefixPartial 13 300426) = some ⟨13, 2, 0, 552237, 300426, 1929, 16384⟩ := by
  decide +kernel

theorem context_13_300426_552237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300426 ⟨552237, by decide⟩ :=
  accepted_of_selected 13 300426 ⟨552237, by decide⟩ ⟨13, 2, 0, 552237, 300426, 1929, 16384⟩
    (by decide) selected_cut_21606

theorem selected_cut_21607 : selected 8 ⟨552245, by decide⟩
    (prefixPartial 13 300427) = some ⟨13, 2, 0, 552245, 300427, 949, 16384⟩ := by
  decide +kernel

theorem context_13_300427_552245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300427 ⟨552245, by decide⟩ :=
  accepted_of_selected 13 300427 ⟨552245, by decide⟩ ⟨13, 2, 0, 552245, 300427, 949, 16384⟩
    (by decide) selected_cut_21607

theorem unmarked_context_12_75106_552246 : frontier 9 ⟨552246, by decide⟩
    (prefixCache 12 75106) (prefixPartial 12 75106) = false := by
  decide +kernel

theorem node_context_12_75106_552246 : EJMOriginalGlobalDAGData.nodes 9 ⟨552246, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨552211, by decide⟩,⟨552237, by decide⟩,⟨552245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75106_552246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75106 ⟨552246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75106
    ⟨552246, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨552211, by decide⟩,⟨552237, by decide⟩,⟨552245, by decide⟩]) unmarked_context_12_75106_552246 node_context_12_75106_552246
  intro a
  fin_cases a
  · exact context_13_300424_3444
  · exact context_13_300425_552211
  · exact context_13_300426_552237
  · exact context_13_300427_552245

theorem selected_cut_21608 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 300428) = some ⟨13, 1, 0, 3444, 300428, 1, 16384⟩ := by
  decide +kernel

theorem context_13_300428_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300428 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 300428 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 300428, 1, 16384⟩
    (by decide) selected_cut_21608

theorem selected_cut_21609 : selected 8 ⟨552263, by decide⟩
    (prefixPartial 13 300429) = some ⟨13, 2, 0, 552263, 300429, 1181, 16384⟩ := by
  decide +kernel

theorem context_13_300429_552263 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300429 ⟨552263, by decide⟩ :=
  accepted_of_selected 13 300429 ⟨552263, by decide⟩ ⟨13, 2, 0, 552263, 300429, 1181, 16384⟩
    (by decide) selected_cut_21609

theorem selected_cut_21610 : selected 8 ⟨552293, by decide⟩
    (prefixPartial 13 300430) = some ⟨13, 2, 0, 552293, 300430, 2157, 16384⟩ := by
  decide +kernel

theorem context_13_300430_552293 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300430 ⟨552293, by decide⟩ :=
  accepted_of_selected 13 300430 ⟨552293, by decide⟩ ⟨13, 2, 0, 552293, 300430, 2157, 16384⟩
    (by decide) selected_cut_21610

theorem selected_cut_21611 : selected 8 ⟨552302, by decide⟩
    (prefixPartial 13 300431) = some ⟨13, 2, 0, 552302, 300431, 909, 16384⟩ := by
  decide +kernel

theorem context_13_300431_552302 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 300431 ⟨552302, by decide⟩ :=
  accepted_of_selected 13 300431 ⟨552302, by decide⟩ ⟨13, 2, 0, 552302, 300431, 909, 16384⟩
    (by decide) selected_cut_21611

theorem unmarked_context_12_75107_552303 : frontier 9 ⟨552303, by decide⟩
    (prefixCache 12 75107) (prefixPartial 12 75107) = false := by
  decide +kernel

theorem node_context_12_75107_552303 : EJMOriginalGlobalDAGData.nodes 9 ⟨552303, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨552263, by decide⟩,⟨552293, by decide⟩,⟨552302, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_75107_552303 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75107 ⟨552303, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 75107
    ⟨552303, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨552263, by decide⟩,⟨552293, by decide⟩,⟨552302, by decide⟩]) unmarked_context_12_75107_552303 node_context_12_75107_552303
  intro a
  fin_cases a
  · exact context_13_300428_3444
  · exact context_13_300429_552263
  · exact context_13_300430_552293
  · exact context_13_300431_552302

theorem unmarked_context_11_18776_552304 : frontier 10 ⟨552304, by decide⟩
    (prefixCache 11 18776) (prefixPartial 11 18776) = false := by
  decide +kernel

theorem node_context_11_18776_552304 : EJMOriginalGlobalDAGData.nodes 10 ⟨552304, by decide⟩ =
    .split (coordinate 11) (![⟨552155, by decide⟩,⟨552192, by decide⟩,⟨552246, by decide⟩,⟨552303, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18776_552304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18776 ⟨552304, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18776
    ⟨552304, by decide⟩ (by decide) (![⟨552155, by decide⟩,⟨552192, by decide⟩,⟨552246, by decide⟩,⟨552303, by decide⟩]) unmarked_context_11_18776_552304 node_context_11_18776_552304
  intro a
  fin_cases a
  · exact context_12_75104_552155
  · exact context_12_75105_552192
  · exact context_12_75106_552246
  · exact context_12_75107_552303

theorem selected_cut_21612 : selected 9 ⟨552343, by decide⟩
    (prefixPartial 12 75108) = some ⟨12, 2, 0, 552343, 75108, 3077, 65536⟩ := by
  decide +kernel

theorem context_12_75108_552343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75108 ⟨552343, by decide⟩ :=
  accepted_of_selected 12 75108 ⟨552343, by decide⟩ ⟨12, 2, 0, 552343, 75108, 3077, 65536⟩
    (by decide) selected_cut_21612

theorem selected_cut_21613 : selected 9 ⟨365907, by decide⟩
    (prefixPartial 12 75109) = some ⟨12, 1, 0, 365907, 75109, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75109_365907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75109 ⟨365907, by decide⟩ :=
  accepted_of_selected 12 75109 ⟨365907, by decide⟩ ⟨12, 1, 0, 365907, 75109, 1, 65536⟩
    (by decide) selected_cut_21613

theorem selected_cut_21614 : selected 9 ⟨552389, by decide⟩
    (prefixPartial 12 75110) = some ⟨12, 2, 0, 552389, 75110, 3377, 65536⟩ := by
  decide +kernel

theorem context_12_75110_552389 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75110 ⟨552389, by decide⟩ :=
  accepted_of_selected 12 75110 ⟨552389, by decide⟩ ⟨12, 2, 0, 552389, 75110, 3377, 65536⟩
    (by decide) selected_cut_21614

theorem selected_cut_21615 : selected 9 ⟨552441, by decide⟩
    (prefixPartial 12 75111) = some ⟨12, 2, 0, 552441, 75111, 3681, 65536⟩ := by
  decide +kernel

theorem context_12_75111_552441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75111 ⟨552441, by decide⟩ :=
  accepted_of_selected 12 75111 ⟨552441, by decide⟩ ⟨12, 2, 0, 552441, 75111, 3681, 65536⟩
    (by decide) selected_cut_21615

theorem unmarked_context_11_18777_552442 : frontier 10 ⟨552442, by decide⟩
    (prefixCache 11 18777) (prefixPartial 11 18777) = false := by
  decide +kernel

theorem node_context_11_18777_552442 : EJMOriginalGlobalDAGData.nodes 10 ⟨552442, by decide⟩ =
    .split (coordinate 11) (![⟨552343, by decide⟩,⟨365907, by decide⟩,⟨552389, by decide⟩,⟨552441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18777_552442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18777 ⟨552442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18777
    ⟨552442, by decide⟩ (by decide) (![⟨552343, by decide⟩,⟨365907, by decide⟩,⟨552389, by decide⟩,⟨552441, by decide⟩]) unmarked_context_11_18777_552442 node_context_11_18777_552442
  intro a
  fin_cases a
  · exact context_12_75108_552343
  · exact context_12_75109_365907
  · exact context_12_75110_552389
  · exact context_12_75111_552441

theorem selected_cut_21616 : selected 9 ⟨552499, by decide⟩
    (prefixPartial 12 75112) = some ⟨12, 2, 0, 552499, 75112, 3701, 65536⟩ := by
  decide +kernel

theorem context_12_75112_552499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75112 ⟨552499, by decide⟩ :=
  accepted_of_selected 12 75112 ⟨552499, by decide⟩ ⟨12, 2, 0, 552499, 75112, 3701, 65536⟩
    (by decide) selected_cut_21616

theorem selected_cut_21617 : selected 9 ⟨552547, by decide⟩
    (prefixPartial 12 75113) = some ⟨12, 2, 0, 552547, 75113, 3305, 65536⟩ := by
  decide +kernel

theorem context_12_75113_552547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75113 ⟨552547, by decide⟩ :=
  accepted_of_selected 12 75113 ⟨552547, by decide⟩ ⟨12, 2, 0, 552547, 75113, 3305, 65536⟩
    (by decide) selected_cut_21617

theorem selected_cut_21618 : selected 9 ⟨552597, by decide⟩
    (prefixPartial 12 75114) = some ⟨12, 2, 0, 552597, 75114, 3761, 65536⟩ := by
  decide +kernel

theorem context_12_75114_552597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75114 ⟨552597, by decide⟩ :=
  accepted_of_selected 12 75114 ⟨552597, by decide⟩ ⟨12, 2, 0, 552597, 75114, 3761, 65536⟩
    (by decide) selected_cut_21618

theorem selected_cut_21619 : selected 9 ⟨552660, by decide⟩
    (prefixPartial 12 75115) = some ⟨12, 2, 0, 552660, 75115, 3997, 65536⟩ := by
  decide +kernel

theorem context_12_75115_552660 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75115 ⟨552660, by decide⟩ :=
  accepted_of_selected 12 75115 ⟨552660, by decide⟩ ⟨12, 2, 0, 552660, 75115, 3997, 65536⟩
    (by decide) selected_cut_21619

theorem unmarked_context_11_18778_552661 : frontier 10 ⟨552661, by decide⟩
    (prefixCache 11 18778) (prefixPartial 11 18778) = false := by
  decide +kernel

theorem node_context_11_18778_552661 : EJMOriginalGlobalDAGData.nodes 10 ⟨552661, by decide⟩ =
    .split (coordinate 11) (![⟨552499, by decide⟩,⟨552547, by decide⟩,⟨552597, by decide⟩,⟨552660, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18778_552661 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18778 ⟨552661, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18778
    ⟨552661, by decide⟩ (by decide) (![⟨552499, by decide⟩,⟨552547, by decide⟩,⟨552597, by decide⟩,⟨552660, by decide⟩]) unmarked_context_11_18778_552661 node_context_11_18778_552661
  intro a
  fin_cases a
  · exact context_12_75112_552499
  · exact context_12_75113_552547
  · exact context_12_75114_552597
  · exact context_12_75115_552660

theorem selected_cut_21620 : selected 9 ⟨552716, by decide⟩
    (prefixPartial 12 75116) = some ⟨12, 2, 0, 552716, 75116, 3965, 65536⟩ := by
  decide +kernel

theorem context_12_75116_552716 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75116 ⟨552716, by decide⟩ :=
  accepted_of_selected 12 75116 ⟨552716, by decide⟩ ⟨12, 2, 0, 552716, 75116, 3965, 65536⟩
    (by decide) selected_cut_21620

theorem selected_cut_21621 : selected 9 ⟨552759, by decide⟩
    (prefixPartial 12 75117) = some ⟨12, 2, 0, 552759, 75117, 3337, 65536⟩ := by
  decide +kernel

theorem context_12_75117_552759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75117 ⟨552759, by decide⟩ :=
  accepted_of_selected 12 75117 ⟨552759, by decide⟩ ⟨12, 2, 0, 552759, 75117, 3337, 65536⟩
    (by decide) selected_cut_21621

theorem selected_cut_21622 : selected 9 ⟨552807, by decide⟩
    (prefixPartial 12 75118) = some ⟨12, 2, 0, 552807, 75118, 3973, 65536⟩ := by
  decide +kernel

theorem context_12_75118_552807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75118 ⟨552807, by decide⟩ :=
  accepted_of_selected 12 75118 ⟨552807, by decide⟩ ⟨12, 2, 0, 552807, 75118, 3973, 65536⟩
    (by decide) selected_cut_21622

theorem selected_cut_21623 : selected 9 ⟨552860, by decide⟩
    (prefixPartial 12 75119) = some ⟨12, 2, 0, 552860, 75119, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_75119_552860 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75119 ⟨552860, by decide⟩ :=
  accepted_of_selected 12 75119 ⟨552860, by decide⟩ ⟨12, 2, 0, 552860, 75119, 4065, 65536⟩
    (by decide) selected_cut_21623

theorem unmarked_context_11_18779_552861 : frontier 10 ⟨552861, by decide⟩
    (prefixCache 11 18779) (prefixPartial 11 18779) = false := by
  decide +kernel

theorem node_context_11_18779_552861 : EJMOriginalGlobalDAGData.nodes 10 ⟨552861, by decide⟩ =
    .split (coordinate 11) (![⟨552716, by decide⟩,⟨552759, by decide⟩,⟨552807, by decide⟩,⟨552860, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18779_552861 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18779 ⟨552861, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18779
    ⟨552861, by decide⟩ (by decide) (![⟨552716, by decide⟩,⟨552759, by decide⟩,⟨552807, by decide⟩,⟨552860, by decide⟩]) unmarked_context_11_18779_552861 node_context_11_18779_552861
  intro a
  fin_cases a
  · exact context_12_75116_552716
  · exact context_12_75117_552759
  · exact context_12_75118_552807
  · exact context_12_75119_552860

theorem unmarked_context_10_4694_552862 : frontier 11 ⟨552862, by decide⟩
    (prefixCache 10 4694) (prefixPartial 10 4694) = false := by
  decide +kernel

theorem node_context_10_4694_552862 : EJMOriginalGlobalDAGData.nodes 11 ⟨552862, by decide⟩ =
    .split (coordinate 10) (![⟨552304, by decide⟩,⟨552442, by decide⟩,⟨552661, by decide⟩,⟨552861, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4694_552862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4694 ⟨552862, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4694
    ⟨552862, by decide⟩ (by decide) (![⟨552304, by decide⟩,⟨552442, by decide⟩,⟨552661, by decide⟩,⟨552861, by decide⟩]) unmarked_context_10_4694_552862 node_context_10_4694_552862
  intro a
  fin_cases a
  · exact context_11_18776_552304
  · exact context_11_18777_552442
  · exact context_11_18778_552661
  · exact context_11_18779_552861

theorem selected_cut_21624 : selected 9 ⟨552909, by decide⟩
    (prefixPartial 12 75120) = some ⟨12, 2, 0, 552909, 75120, 3253, 65536⟩ := by
  decide +kernel

theorem context_12_75120_552909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75120 ⟨552909, by decide⟩ :=
  accepted_of_selected 12 75120 ⟨552909, by decide⟩ ⟨12, 2, 0, 552909, 75120, 3253, 65536⟩
    (by decide) selected_cut_21624

theorem selected_cut_21625 : selected 9 ⟨552948, by decide⟩
    (prefixPartial 12 75121) = some ⟨12, 2, 0, 552948, 75121, 2937, 65536⟩ := by
  decide +kernel

theorem context_12_75121_552948 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75121 ⟨552948, by decide⟩ :=
  accepted_of_selected 12 75121 ⟨552948, by decide⟩ ⟨12, 2, 0, 552948, 75121, 2937, 65536⟩
    (by decide) selected_cut_21625

theorem selected_cut_21626 : selected 9 ⟨553002, by decide⟩
    (prefixPartial 12 75122) = some ⟨12, 2, 0, 553002, 75122, 3873, 65536⟩ := by
  decide +kernel

theorem context_12_75122_553002 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75122 ⟨553002, by decide⟩ :=
  accepted_of_selected 12 75122 ⟨553002, by decide⟩ ⟨12, 2, 0, 553002, 75122, 3873, 65536⟩
    (by decide) selected_cut_21626

theorem selected_cut_21627 : selected 9 ⟨553047, by decide⟩
    (prefixPartial 12 75123) = some ⟨12, 2, 0, 553047, 75123, 3557, 65536⟩ := by
  decide +kernel

theorem context_12_75123_553047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75123 ⟨553047, by decide⟩ :=
  accepted_of_selected 12 75123 ⟨553047, by decide⟩ ⟨12, 2, 0, 553047, 75123, 3557, 65536⟩
    (by decide) selected_cut_21627

theorem unmarked_context_11_18780_553048 : frontier 10 ⟨553048, by decide⟩
    (prefixCache 11 18780) (prefixPartial 11 18780) = false := by
  decide +kernel

theorem node_context_11_18780_553048 : EJMOriginalGlobalDAGData.nodes 10 ⟨553048, by decide⟩ =
    .split (coordinate 11) (![⟨552909, by decide⟩,⟨552948, by decide⟩,⟨553002, by decide⟩,⟨553047, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18780_553048 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18780 ⟨553048, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18780
    ⟨553048, by decide⟩ (by decide) (![⟨552909, by decide⟩,⟨552948, by decide⟩,⟨553002, by decide⟩,⟨553047, by decide⟩]) unmarked_context_11_18780_553048 node_context_11_18780_553048
  intro a
  fin_cases a
  · exact context_12_75120_552909
  · exact context_12_75121_552948
  · exact context_12_75122_553002
  · exact context_12_75123_553047

theorem selected_cut_21628 : selected 9 ⟨553092, by decide⟩
    (prefixPartial 12 75124) = some ⟨12, 2, 0, 553092, 75124, 2905, 65536⟩ := by
  decide +kernel

theorem context_12_75124_553092 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75124 ⟨553092, by decide⟩ :=
  accepted_of_selected 12 75124 ⟨553092, by decide⟩ ⟨12, 2, 0, 553092, 75124, 2905, 65536⟩
    (by decide) selected_cut_21628

theorem selected_cut_21629 : selected 9 ⟨410616, by decide⟩
    (prefixPartial 12 75125) = some ⟨12, 1, 0, 410616, 75125, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75125_410616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75125 ⟨410616, by decide⟩ :=
  accepted_of_selected 12 75125 ⟨410616, by decide⟩ ⟨12, 1, 0, 410616, 75125, 1, 65536⟩
    (by decide) selected_cut_21629

theorem selected_cut_21630 : selected 9 ⟨553133, by decide⟩
    (prefixPartial 12 75126) = some ⟨12, 2, 0, 553133, 75126, 3385, 65536⟩ := by
  decide +kernel

theorem context_12_75126_553133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75126 ⟨553133, by decide⟩ :=
  accepted_of_selected 12 75126 ⟨553133, by decide⟩ ⟨12, 2, 0, 553133, 75126, 3385, 65536⟩
    (by decide) selected_cut_21630

theorem selected_cut_21631 : selected 9 ⟨553187, by decide⟩
    (prefixPartial 12 75127) = some ⟨12, 2, 0, 553187, 75127, 3261, 65536⟩ := by
  decide +kernel

theorem context_12_75127_553187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75127 ⟨553187, by decide⟩ :=
  accepted_of_selected 12 75127 ⟨553187, by decide⟩ ⟨12, 2, 0, 553187, 75127, 3261, 65536⟩
    (by decide) selected_cut_21631

theorem unmarked_context_11_18781_553188 : frontier 10 ⟨553188, by decide⟩
    (prefixCache 11 18781) (prefixPartial 11 18781) = false := by
  decide +kernel

theorem node_context_11_18781_553188 : EJMOriginalGlobalDAGData.nodes 10 ⟨553188, by decide⟩ =
    .split (coordinate 11) (![⟨553092, by decide⟩,⟨410616, by decide⟩,⟨553133, by decide⟩,⟨553187, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18781_553188 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18781 ⟨553188, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18781
    ⟨553188, by decide⟩ (by decide) (![⟨553092, by decide⟩,⟨410616, by decide⟩,⟨553133, by decide⟩,⟨553187, by decide⟩]) unmarked_context_11_18781_553188 node_context_11_18781_553188
  intro a
  fin_cases a
  · exact context_12_75124_553092
  · exact context_12_75125_410616
  · exact context_12_75126_553133
  · exact context_12_75127_553187

theorem selected_cut_21632 : selected 9 ⟨553249, by decide⟩
    (prefixPartial 12 75128) = some ⟨12, 2, 0, 553249, 75128, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_75128_553249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75128 ⟨553249, by decide⟩ :=
  accepted_of_selected 12 75128 ⟨553249, by decide⟩ ⟨12, 2, 0, 553249, 75128, 3585, 65536⟩
    (by decide) selected_cut_21632

theorem selected_cut_21633 : selected 9 ⟨553292, by decide⟩
    (prefixPartial 12 75129) = some ⟨12, 2, 0, 553292, 75129, 3229, 65536⟩ := by
  decide +kernel

theorem context_12_75129_553292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75129 ⟨553292, by decide⟩ :=
  accepted_of_selected 12 75129 ⟨553292, by decide⟩ ⟨12, 2, 0, 553292, 75129, 3229, 65536⟩
    (by decide) selected_cut_21633

theorem selected_cut_21634 : selected 9 ⟨553345, by decide⟩
    (prefixPartial 12 75130) = some ⟨12, 2, 0, 553345, 75130, 3745, 65536⟩ := by
  decide +kernel

theorem context_12_75130_553345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75130 ⟨553345, by decide⟩ :=
  accepted_of_selected 12 75130 ⟨553345, by decide⟩ ⟨12, 2, 0, 553345, 75130, 3745, 65536⟩
    (by decide) selected_cut_21634

theorem selected_cut_21635 : selected 9 ⟨553397, by decide⟩
    (prefixPartial 12 75131) = some ⟨12, 2, 0, 553397, 75131, 3493, 65536⟩ := by
  decide +kernel

theorem context_12_75131_553397 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75131 ⟨553397, by decide⟩ :=
  accepted_of_selected 12 75131 ⟨553397, by decide⟩ ⟨12, 2, 0, 553397, 75131, 3493, 65536⟩
    (by decide) selected_cut_21635

theorem unmarked_context_11_18782_553398 : frontier 10 ⟨553398, by decide⟩
    (prefixCache 11 18782) (prefixPartial 11 18782) = false := by
  decide +kernel

theorem node_context_11_18782_553398 : EJMOriginalGlobalDAGData.nodes 10 ⟨553398, by decide⟩ =
    .split (coordinate 11) (![⟨553249, by decide⟩,⟨553292, by decide⟩,⟨553345, by decide⟩,⟨553397, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18782_553398 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18782 ⟨553398, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18782
    ⟨553398, by decide⟩ (by decide) (![⟨553249, by decide⟩,⟨553292, by decide⟩,⟨553345, by decide⟩,⟨553397, by decide⟩]) unmarked_context_11_18782_553398 node_context_11_18782_553398
  intro a
  fin_cases a
  · exact context_12_75128_553249
  · exact context_12_75129_553292
  · exact context_12_75130_553345
  · exact context_12_75131_553397

theorem selected_cut_21636 : selected 9 ⟨553447, by decide⟩
    (prefixPartial 12 75132) = some ⟨12, 2, 0, 553447, 75132, 3257, 65536⟩ := by
  decide +kernel

theorem context_12_75132_553447 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75132 ⟨553447, by decide⟩ :=
  accepted_of_selected 12 75132 ⟨553447, by decide⟩ ⟨12, 2, 0, 553447, 75132, 3257, 65536⟩
    (by decide) selected_cut_21636

theorem selected_cut_21637 : selected 9 ⟨553479, by decide⟩
    (prefixPartial 12 75133) = some ⟨12, 2, 0, 553479, 75133, 2877, 65536⟩ := by
  decide +kernel

theorem context_12_75133_553479 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75133 ⟨553479, by decide⟩ :=
  accepted_of_selected 12 75133 ⟨553479, by decide⟩ ⟨12, 2, 0, 553479, 75133, 2877, 65536⟩
    (by decide) selected_cut_21637

theorem selected_cut_21638 : selected 9 ⟨553522, by decide⟩
    (prefixPartial 12 75134) = some ⟨12, 2, 0, 553522, 75134, 3505, 65536⟩ := by
  decide +kernel

theorem context_12_75134_553522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75134 ⟨553522, by decide⟩ :=
  accepted_of_selected 12 75134 ⟨553522, by decide⟩ ⟨12, 2, 0, 553522, 75134, 3505, 65536⟩
    (by decide) selected_cut_21638

theorem selected_cut_21639 : selected 9 ⟨553561, by decide⟩
    (prefixPartial 12 75135) = some ⟨12, 2, 0, 553561, 75135, 3217, 65536⟩ := by
  decide +kernel

theorem context_12_75135_553561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75135 ⟨553561, by decide⟩ :=
  accepted_of_selected 12 75135 ⟨553561, by decide⟩ ⟨12, 2, 0, 553561, 75135, 3217, 65536⟩
    (by decide) selected_cut_21639

theorem unmarked_context_11_18783_553562 : frontier 10 ⟨553562, by decide⟩
    (prefixCache 11 18783) (prefixPartial 11 18783) = false := by
  decide +kernel

theorem node_context_11_18783_553562 : EJMOriginalGlobalDAGData.nodes 10 ⟨553562, by decide⟩ =
    .split (coordinate 11) (![⟨553447, by decide⟩,⟨553479, by decide⟩,⟨553522, by decide⟩,⟨553561, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18783_553562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18783 ⟨553562, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18783
    ⟨553562, by decide⟩ (by decide) (![⟨553447, by decide⟩,⟨553479, by decide⟩,⟨553522, by decide⟩,⟨553561, by decide⟩]) unmarked_context_11_18783_553562 node_context_11_18783_553562
  intro a
  fin_cases a
  · exact context_12_75132_553447
  · exact context_12_75133_553479
  · exact context_12_75134_553522
  · exact context_12_75135_553561

theorem unmarked_context_10_4695_553563 : frontier 11 ⟨553563, by decide⟩
    (prefixCache 10 4695) (prefixPartial 10 4695) = false := by
  decide +kernel

theorem node_context_10_4695_553563 : EJMOriginalGlobalDAGData.nodes 11 ⟨553563, by decide⟩ =
    .split (coordinate 10) (![⟨553048, by decide⟩,⟨553188, by decide⟩,⟨553398, by decide⟩,⟨553562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4695_553563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4695 ⟨553563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4695
    ⟨553563, by decide⟩ (by decide) (![⟨553048, by decide⟩,⟨553188, by decide⟩,⟨553398, by decide⟩,⟨553562, by decide⟩]) unmarked_context_10_4695_553563 node_context_10_4695_553563
  intro a
  fin_cases a
  · exact context_11_18780_553048
  · exact context_11_18781_553188
  · exact context_11_18782_553398
  · exact context_11_18783_553562

theorem unmarked_context_9_1173_553564 : frontier 12 ⟨553564, by decide⟩
    (prefixCache 9 1173) (prefixPartial 9 1173) = false := by
  decide +kernel

theorem node_context_9_1173_553564 : EJMOriginalGlobalDAGData.nodes 12 ⟨553564, by decide⟩ =
    .split (coordinate 9) (![⟨551548, by decide⟩,⟨552105, by decide⟩,⟨552862, by decide⟩,⟨553563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1173_553564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1173 ⟨553564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1173
    ⟨553564, by decide⟩ (by decide) (![⟨551548, by decide⟩,⟨552105, by decide⟩,⟨552862, by decide⟩,⟨553563, by decide⟩]) unmarked_context_9_1173_553564 node_context_9_1173_553564
  intro a
  fin_cases a
  · exact context_10_4692_551548
  · exact context_10_4693_552105
  · exact context_10_4694_552862
  · exact context_10_4695_553563

theorem selected_cut_21640 : selected 9 ⟨553589, by decide⟩
    (prefixPartial 12 75136) = some ⟨12, 2, 0, 553589, 75136, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_75136_553589 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75136 ⟨553589, by decide⟩ :=
  accepted_of_selected 12 75136 ⟨553589, by decide⟩ ⟨12, 2, 0, 553589, 75136, 2149, 65536⟩
    (by decide) selected_cut_21640

theorem selected_cut_21641 : selected 9 ⟨553612, by decide⟩
    (prefixPartial 12 75137) = some ⟨12, 2, 0, 553612, 75137, 2017, 65536⟩ := by
  decide +kernel

theorem context_12_75137_553612 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75137 ⟨553612, by decide⟩ :=
  accepted_of_selected 12 75137 ⟨553612, by decide⟩ ⟨12, 2, 0, 553612, 75137, 2017, 65536⟩
    (by decide) selected_cut_21641

theorem selected_cut_21642 : selected 9 ⟨553645, by decide⟩
    (prefixPartial 12 75138) = some ⟨12, 2, 0, 553645, 75138, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_75138_553645 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75138 ⟨553645, by decide⟩ :=
  accepted_of_selected 12 75138 ⟨553645, by decide⟩ ⟨12, 2, 0, 553645, 75138, 2421, 65536⟩
    (by decide) selected_cut_21642

theorem selected_cut_21643 : selected 9 ⟨553677, by decide⟩
    (prefixPartial 12 75139) = some ⟨12, 2, 0, 553677, 75139, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_75139_553677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75139 ⟨553677, by decide⟩ :=
  accepted_of_selected 12 75139 ⟨553677, by decide⟩ ⟨12, 2, 0, 553677, 75139, 2613, 65536⟩
    (by decide) selected_cut_21643

theorem unmarked_context_11_18784_553678 : frontier 10 ⟨553678, by decide⟩
    (prefixCache 11 18784) (prefixPartial 11 18784) = false := by
  decide +kernel

theorem node_context_11_18784_553678 : EJMOriginalGlobalDAGData.nodes 10 ⟨553678, by decide⟩ =
    .split (coordinate 11) (![⟨553589, by decide⟩,⟨553612, by decide⟩,⟨553645, by decide⟩,⟨553677, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18784_553678 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18784 ⟨553678, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18784
    ⟨553678, by decide⟩ (by decide) (![⟨553589, by decide⟩,⟨553612, by decide⟩,⟨553645, by decide⟩,⟨553677, by decide⟩]) unmarked_context_11_18784_553678 node_context_11_18784_553678
  intro a
  fin_cases a
  · exact context_12_75136_553589
  · exact context_12_75137_553612
  · exact context_12_75138_553645
  · exact context_12_75139_553677

theorem selected_cut_21644 : selected 9 ⟨553701, by decide⟩
    (prefixPartial 12 75140) = some ⟨12, 2, 0, 553701, 75140, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_75140_553701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75140 ⟨553701, by decide⟩ :=
  accepted_of_selected 12 75140 ⟨553701, by decide⟩ ⟨12, 2, 0, 553701, 75140, 1917, 65536⟩
    (by decide) selected_cut_21644

theorem selected_cut_21645 : selected 9 ⟨553763, by decide⟩
    (prefixPartial 12 75141) = some ⟨12, 2, 0, 553763, 75141, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_75141_553763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75141 ⟨553763, by decide⟩ :=
  accepted_of_selected 12 75141 ⟨553763, by decide⟩ ⟨12, 2, 0, 553763, 75141, 1049, 65536⟩
    (by decide) selected_cut_21645

theorem selected_cut_21646 : selected 9 ⟨553794, by decide⟩
    (prefixPartial 12 75142) = some ⟨12, 2, 0, 553794, 75142, 2157, 65536⟩ := by
  decide +kernel

theorem context_12_75142_553794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75142 ⟨553794, by decide⟩ :=
  accepted_of_selected 12 75142 ⟨553794, by decide⟩ ⟨12, 2, 0, 553794, 75142, 2157, 65536⟩
    (by decide) selected_cut_21646

theorem selected_cut_21647 : selected 9 ⟨553829, by decide⟩
    (prefixPartial 12 75143) = some ⟨12, 2, 0, 553829, 75143, 2353, 65536⟩ := by
  decide +kernel

theorem context_12_75143_553829 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75143 ⟨553829, by decide⟩ :=
  accepted_of_selected 12 75143 ⟨553829, by decide⟩ ⟨12, 2, 0, 553829, 75143, 2353, 65536⟩
    (by decide) selected_cut_21647

theorem unmarked_context_11_18785_553830 : frontier 10 ⟨553830, by decide⟩
    (prefixCache 11 18785) (prefixPartial 11 18785) = false := by
  decide +kernel

theorem node_context_11_18785_553830 : EJMOriginalGlobalDAGData.nodes 10 ⟨553830, by decide⟩ =
    .split (coordinate 11) (![⟨553701, by decide⟩,⟨553763, by decide⟩,⟨553794, by decide⟩,⟨553829, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18785_553830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18785 ⟨553830, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18785
    ⟨553830, by decide⟩ (by decide) (![⟨553701, by decide⟩,⟨553763, by decide⟩,⟨553794, by decide⟩,⟨553829, by decide⟩]) unmarked_context_11_18785_553830 node_context_11_18785_553830
  intro a
  fin_cases a
  · exact context_12_75140_553701
  · exact context_12_75141_553763
  · exact context_12_75142_553794
  · exact context_12_75143_553829

theorem selected_cut_21648 : selected 9 ⟨553865, by decide⟩
    (prefixPartial 12 75144) = some ⟨12, 2, 0, 553865, 75144, 2545, 65536⟩ := by
  decide +kernel

theorem context_12_75144_553865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75144 ⟨553865, by decide⟩ :=
  accepted_of_selected 12 75144 ⟨553865, by decide⟩ ⟨12, 2, 0, 553865, 75144, 2545, 65536⟩
    (by decide) selected_cut_21648

theorem selected_cut_21649 : selected 9 ⟨553909, by decide⟩
    (prefixPartial 12 75145) = some ⟨12, 2, 0, 553909, 75145, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_75145_553909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75145 ⟨553909, by decide⟩ :=
  accepted_of_selected 12 75145 ⟨553909, by decide⟩ ⟨12, 2, 0, 553909, 75145, 2397, 65536⟩
    (by decide) selected_cut_21649

theorem selected_cut_21650 : selected 9 ⟨553952, by decide⟩
    (prefixPartial 12 75146) = some ⟨12, 2, 0, 553952, 75146, 2569, 65536⟩ := by
  decide +kernel

theorem context_12_75146_553952 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75146 ⟨553952, by decide⟩ :=
  accepted_of_selected 12 75146 ⟨553952, by decide⟩ ⟨12, 2, 0, 553952, 75146, 2569, 65536⟩
    (by decide) selected_cut_21650

theorem selected_cut_21651 : selected 9 ⟨554006, by decide⟩
    (prefixPartial 12 75147) = some ⟨12, 2, 0, 554006, 75147, 2785, 65536⟩ := by
  decide +kernel

theorem context_12_75147_554006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75147 ⟨554006, by decide⟩ :=
  accepted_of_selected 12 75147 ⟨554006, by decide⟩ ⟨12, 2, 0, 554006, 75147, 2785, 65536⟩
    (by decide) selected_cut_21651

theorem unmarked_context_11_18786_554007 : frontier 10 ⟨554007, by decide⟩
    (prefixCache 11 18786) (prefixPartial 11 18786) = false := by
  decide +kernel

theorem node_context_11_18786_554007 : EJMOriginalGlobalDAGData.nodes 10 ⟨554007, by decide⟩ =
    .split (coordinate 11) (![⟨553865, by decide⟩,⟨553909, by decide⟩,⟨553952, by decide⟩,⟨554006, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18786_554007 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18786 ⟨554007, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18786
    ⟨554007, by decide⟩ (by decide) (![⟨553865, by decide⟩,⟨553909, by decide⟩,⟨553952, by decide⟩,⟨554006, by decide⟩]) unmarked_context_11_18786_554007 node_context_11_18786_554007
  intro a
  fin_cases a
  · exact context_12_75144_553865
  · exact context_12_75145_553909
  · exact context_12_75146_553952
  · exact context_12_75147_554006

theorem selected_cut_21652 : selected 9 ⟨554040, by decide⟩
    (prefixPartial 12 75148) = some ⟨12, 2, 0, 554040, 75148, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_75148_554040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75148 ⟨554040, by decide⟩ :=
  accepted_of_selected 12 75148 ⟨554040, by decide⟩ ⟨12, 2, 0, 554040, 75148, 2265, 65536⟩
    (by decide) selected_cut_21652

theorem selected_cut_21653 : selected 9 ⟨554065, by decide⟩
    (prefixPartial 12 75149) = some ⟨12, 2, 0, 554065, 75149, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_75149_554065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75149 ⟨554065, by decide⟩ :=
  accepted_of_selected 12 75149 ⟨554065, by decide⟩ ⟨12, 2, 0, 554065, 75149, 2069, 65536⟩
    (by decide) selected_cut_21653

theorem selected_cut_21654 : selected 9 ⟨554101, by decide⟩
    (prefixPartial 12 75150) = some ⟨12, 2, 0, 554101, 75150, 2453, 65536⟩ := by
  decide +kernel

theorem context_12_75150_554101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75150 ⟨554101, by decide⟩ :=
  accepted_of_selected 12 75150 ⟨554101, by decide⟩ ⟨12, 2, 0, 554101, 75150, 2453, 65536⟩
    (by decide) selected_cut_21654

theorem selected_cut_21655 : selected 9 ⟨554131, by decide⟩
    (prefixPartial 12 75151) = some ⟨12, 2, 0, 554131, 75151, 2469, 65536⟩ := by
  decide +kernel

theorem context_12_75151_554131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75151 ⟨554131, by decide⟩ :=
  accepted_of_selected 12 75151 ⟨554131, by decide⟩ ⟨12, 2, 0, 554131, 75151, 2469, 65536⟩
    (by decide) selected_cut_21655

theorem unmarked_context_11_18787_554132 : frontier 10 ⟨554132, by decide⟩
    (prefixCache 11 18787) (prefixPartial 11 18787) = false := by
  decide +kernel

theorem node_context_11_18787_554132 : EJMOriginalGlobalDAGData.nodes 10 ⟨554132, by decide⟩ =
    .split (coordinate 11) (![⟨554040, by decide⟩,⟨554065, by decide⟩,⟨554101, by decide⟩,⟨554131, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18787_554132 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18787 ⟨554132, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18787
    ⟨554132, by decide⟩ (by decide) (![⟨554040, by decide⟩,⟨554065, by decide⟩,⟨554101, by decide⟩,⟨554131, by decide⟩]) unmarked_context_11_18787_554132 node_context_11_18787_554132
  intro a
  fin_cases a
  · exact context_12_75148_554040
  · exact context_12_75149_554065
  · exact context_12_75150_554101
  · exact context_12_75151_554131

theorem unmarked_context_10_4696_554133 : frontier 11 ⟨554133, by decide⟩
    (prefixCache 10 4696) (prefixPartial 10 4696) = false := by
  decide +kernel

theorem node_context_10_4696_554133 : EJMOriginalGlobalDAGData.nodes 11 ⟨554133, by decide⟩ =
    .split (coordinate 10) (![⟨553678, by decide⟩,⟨553830, by decide⟩,⟨554007, by decide⟩,⟨554132, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4696_554133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4696 ⟨554133, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4696
    ⟨554133, by decide⟩ (by decide) (![⟨553678, by decide⟩,⟨553830, by decide⟩,⟨554007, by decide⟩,⟨554132, by decide⟩]) unmarked_context_10_4696_554133 node_context_10_4696_554133
  intro a
  fin_cases a
  · exact context_11_18784_553678
  · exact context_11_18785_553830
  · exact context_11_18786_554007
  · exact context_11_18787_554132

theorem selected_cut_21656 : selected 9 ⟨554156, by decide⟩
    (prefixPartial 12 75152) = some ⟨12, 2, 0, 554156, 75152, 2181, 65536⟩ := by
  decide +kernel

theorem context_12_75152_554156 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75152 ⟨554156, by decide⟩ :=
  accepted_of_selected 12 75152 ⟨554156, by decide⟩ ⟨12, 2, 0, 554156, 75152, 2181, 65536⟩
    (by decide) selected_cut_21656

theorem selected_cut_21657 : selected 9 ⟨554176, by decide⟩
    (prefixPartial 12 75153) = some ⟨12, 2, 0, 554176, 75153, 1873, 65536⟩ := by
  decide +kernel

theorem context_12_75153_554176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75153 ⟨554176, by decide⟩ :=
  accepted_of_selected 12 75153 ⟨554176, by decide⟩ ⟨12, 2, 0, 554176, 75153, 1873, 65536⟩
    (by decide) selected_cut_21657

theorem selected_cut_21658 : selected 9 ⟨554202, by decide⟩
    (prefixPartial 12 75154) = some ⟨12, 2, 0, 554202, 75154, 2317, 65536⟩ := by
  decide +kernel

theorem context_12_75154_554202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75154 ⟨554202, by decide⟩ :=
  accepted_of_selected 12 75154 ⟨554202, by decide⟩ ⟨12, 2, 0, 554202, 75154, 2317, 65536⟩
    (by decide) selected_cut_21658

theorem selected_cut_21659 : selected 9 ⟨554227, by decide⟩
    (prefixPartial 12 75155) = some ⟨12, 2, 0, 554227, 75155, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_75155_554227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75155 ⟨554227, by decide⟩ :=
  accepted_of_selected 12 75155 ⟨554227, by decide⟩ ⟨12, 2, 0, 554227, 75155, 2345, 65536⟩
    (by decide) selected_cut_21659

theorem unmarked_context_11_18788_554228 : frontier 10 ⟨554228, by decide⟩
    (prefixCache 11 18788) (prefixPartial 11 18788) = false := by
  decide +kernel

theorem node_context_11_18788_554228 : EJMOriginalGlobalDAGData.nodes 10 ⟨554228, by decide⟩ =
    .split (coordinate 11) (![⟨554156, by decide⟩,⟨554176, by decide⟩,⟨554202, by decide⟩,⟨554227, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18788_554228 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18788 ⟨554228, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18788
    ⟨554228, by decide⟩ (by decide) (![⟨554156, by decide⟩,⟨554176, by decide⟩,⟨554202, by decide⟩,⟨554227, by decide⟩]) unmarked_context_11_18788_554228 node_context_11_18788_554228
  intro a
  fin_cases a
  · exact context_12_75152_554156
  · exact context_12_75153_554176
  · exact context_12_75154_554202
  · exact context_12_75155_554227

theorem selected_cut_21660 : selected 10 ⟨554314, by decide⟩
    (prefixPartial 11 18789) = some ⟨11, 2, 0, 554314, 18789, 3753, 262144⟩ := by
  decide +kernel

theorem context_11_18789_554314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18789 ⟨554314, by decide⟩ :=
  accepted_of_selected 11 18789 ⟨554314, by decide⟩ ⟨11, 2, 0, 554314, 18789, 3753, 262144⟩
    (by decide) selected_cut_21660

theorem selected_cut_21661 : selected 9 ⟨554343, by decide⟩
    (prefixPartial 12 75160) = some ⟨12, 2, 0, 554343, 75160, 2481, 65536⟩ := by
  decide +kernel

theorem context_12_75160_554343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75160 ⟨554343, by decide⟩ :=
  accepted_of_selected 12 75160 ⟨554343, by decide⟩ ⟨12, 2, 0, 554343, 75160, 2481, 65536⟩
    (by decide) selected_cut_21661

theorem selected_cut_21662 : selected 9 ⟨554365, by decide⟩
    (prefixPartial 12 75161) = some ⟨12, 2, 0, 554365, 75161, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_75161_554365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75161 ⟨554365, by decide⟩ :=
  accepted_of_selected 12 75161 ⟨554365, by decide⟩ ⟨12, 2, 0, 554365, 75161, 2145, 65536⟩
    (by decide) selected_cut_21662

theorem selected_cut_21663 : selected 9 ⟨554392, by decide⟩
    (prefixPartial 12 75162) = some ⟨12, 2, 0, 554392, 75162, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_75162_554392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75162 ⟨554392, by decide⟩ :=
  accepted_of_selected 12 75162 ⟨554392, by decide⟩ ⟨12, 2, 0, 554392, 75162, 2373, 65536⟩
    (by decide) selected_cut_21663

theorem selected_cut_21664 : selected 9 ⟨554430, by decide⟩
    (prefixPartial 12 75163) = some ⟨12, 2, 0, 554430, 75163, 2425, 65536⟩ := by
  decide +kernel

theorem context_12_75163_554430 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75163 ⟨554430, by decide⟩ :=
  accepted_of_selected 12 75163 ⟨554430, by decide⟩ ⟨12, 2, 0, 554430, 75163, 2425, 65536⟩
    (by decide) selected_cut_21664

theorem unmarked_context_11_18790_554431 : frontier 10 ⟨554431, by decide⟩
    (prefixCache 11 18790) (prefixPartial 11 18790) = false := by
  decide +kernel

theorem node_context_11_18790_554431 : EJMOriginalGlobalDAGData.nodes 10 ⟨554431, by decide⟩ =
    .split (coordinate 11) (![⟨554343, by decide⟩,⟨554365, by decide⟩,⟨554392, by decide⟩,⟨554430, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18790_554431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18790 ⟨554431, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18790
    ⟨554431, by decide⟩ (by decide) (![⟨554343, by decide⟩,⟨554365, by decide⟩,⟨554392, by decide⟩,⟨554430, by decide⟩]) unmarked_context_11_18790_554431 node_context_11_18790_554431
  intro a
  fin_cases a
  · exact context_12_75160_554343
  · exact context_12_75161_554365
  · exact context_12_75162_554392
  · exact context_12_75163_554430

theorem selected_cut_21665 : selected 9 ⟨554453, by decide⟩
    (prefixPartial 12 75164) = some ⟨12, 2, 0, 554453, 75164, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_75164_554453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75164 ⟨554453, by decide⟩ :=
  accepted_of_selected 12 75164 ⟨554453, by decide⟩ ⟨12, 2, 0, 554453, 75164, 2221, 65536⟩
    (by decide) selected_cut_21665

theorem selected_cut_21666 : selected 9 ⟨554472, by decide⟩
    (prefixPartial 12 75165) = some ⟨12, 2, 0, 554472, 75165, 1777, 65536⟩ := by
  decide +kernel

theorem context_12_75165_554472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75165 ⟨554472, by decide⟩ :=
  accepted_of_selected 12 75165 ⟨554472, by decide⟩ ⟨12, 2, 0, 554472, 75165, 1777, 65536⟩
    (by decide) selected_cut_21666

theorem selected_cut_21667 : selected 9 ⟨554501, by decide⟩
    (prefixPartial 12 75166) = some ⟨12, 2, 0, 554501, 75166, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_75166_554501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75166 ⟨554501, by decide⟩ :=
  accepted_of_selected 12 75166 ⟨554501, by decide⟩ ⟨12, 2, 0, 554501, 75166, 2229, 65536⟩
    (by decide) selected_cut_21667

theorem selected_cut_21668 : selected 9 ⟨554517, by decide⟩
    (prefixPartial 12 75167) = some ⟨12, 2, 0, 554517, 75167, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_75167_554517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75167 ⟨554517, by decide⟩ :=
  accepted_of_selected 12 75167 ⟨554517, by decide⟩ ⟨12, 2, 0, 554517, 75167, 2177, 65536⟩
    (by decide) selected_cut_21668

theorem unmarked_context_11_18791_554518 : frontier 10 ⟨554518, by decide⟩
    (prefixCache 11 18791) (prefixPartial 11 18791) = false := by
  decide +kernel

theorem node_context_11_18791_554518 : EJMOriginalGlobalDAGData.nodes 10 ⟨554518, by decide⟩ =
    .split (coordinate 11) (![⟨554453, by decide⟩,⟨554472, by decide⟩,⟨554501, by decide⟩,⟨554517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18791_554518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18791 ⟨554518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18791
    ⟨554518, by decide⟩ (by decide) (![⟨554453, by decide⟩,⟨554472, by decide⟩,⟨554501, by decide⟩,⟨554517, by decide⟩]) unmarked_context_11_18791_554518 node_context_11_18791_554518
  intro a
  fin_cases a
  · exact context_12_75164_554453
  · exact context_12_75165_554472
  · exact context_12_75166_554501
  · exact context_12_75167_554517

theorem unmarked_context_10_4697_554519 : frontier 11 ⟨554519, by decide⟩
    (prefixCache 10 4697) (prefixPartial 10 4697) = false := by
  decide +kernel

theorem node_context_10_4697_554519 : EJMOriginalGlobalDAGData.nodes 11 ⟨554519, by decide⟩ =
    .split (coordinate 10) (![⟨554228, by decide⟩,⟨554314, by decide⟩,⟨554431, by decide⟩,⟨554518, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4697_554519 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4697 ⟨554519, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4697
    ⟨554519, by decide⟩ (by decide) (![⟨554228, by decide⟩,⟨554314, by decide⟩,⟨554431, by decide⟩,⟨554518, by decide⟩]) unmarked_context_10_4697_554519 node_context_10_4697_554519
  intro a
  fin_cases a
  · exact context_11_18788_554228
  · exact context_11_18789_554314
  · exact context_11_18790_554431
  · exact context_11_18791_554518

theorem selected_cut_21669 : selected 9 ⟨554540, by decide⟩
    (prefixPartial 12 75168) = some ⟨12, 2, 0, 554540, 75168, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_75168_554540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75168 ⟨554540, by decide⟩ :=
  accepted_of_selected 12 75168 ⟨554540, by decide⟩ ⟨12, 2, 0, 554540, 75168, 1617, 65536⟩
    (by decide) selected_cut_21669

theorem selected_cut_21670 : selected 9 ⟨554552, by decide⟩
    (prefixPartial 12 75169) = some ⟨12, 2, 0, 554552, 75169, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_75169_554552 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75169 ⟨554552, by decide⟩ :=
  accepted_of_selected 12 75169 ⟨554552, by decide⟩ ⟨12, 2, 0, 554552, 75169, 1349, 65536⟩
    (by decide) selected_cut_21670

theorem selected_cut_21671 : selected 9 ⟨554578, by decide⟩
    (prefixPartial 12 75170) = some ⟨12, 2, 0, 554578, 75170, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_75170_554578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75170 ⟨554578, by decide⟩ :=
  accepted_of_selected 12 75170 ⟨554578, by decide⟩ ⟨12, 2, 0, 554578, 75170, 1517, 65536⟩
    (by decide) selected_cut_21671

theorem selected_cut_21672 : selected 9 ⟨554599, by decide⟩
    (prefixPartial 12 75171) = some ⟨12, 2, 0, 554599, 75171, 1705, 65536⟩ := by
  decide +kernel

theorem context_12_75171_554599 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75171 ⟨554599, by decide⟩ :=
  accepted_of_selected 12 75171 ⟨554599, by decide⟩ ⟨12, 2, 0, 554599, 75171, 1705, 65536⟩
    (by decide) selected_cut_21672

theorem unmarked_context_11_18792_554600 : frontier 10 ⟨554600, by decide⟩
    (prefixCache 11 18792) (prefixPartial 11 18792) = false := by
  decide +kernel

theorem node_context_11_18792_554600 : EJMOriginalGlobalDAGData.nodes 10 ⟨554600, by decide⟩ =
    .split (coordinate 11) (![⟨554540, by decide⟩,⟨554552, by decide⟩,⟨554578, by decide⟩,⟨554599, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18792_554600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18792 ⟨554600, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18792
    ⟨554600, by decide⟩ (by decide) (![⟨554540, by decide⟩,⟨554552, by decide⟩,⟨554578, by decide⟩,⟨554599, by decide⟩]) unmarked_context_11_18792_554600 node_context_11_18792_554600
  intro a
  fin_cases a
  · exact context_12_75168_554540
  · exact context_12_75169_554552
  · exact context_12_75170_554578
  · exact context_12_75171_554599

theorem selected_cut_21673 : selected 9 ⟨554618, by decide⟩
    (prefixPartial 12 75172) = some ⟨12, 2, 0, 554618, 75172, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_75172_554618 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75172 ⟨554618, by decide⟩ :=
  accepted_of_selected 12 75172 ⟨554618, by decide⟩ ⟨12, 2, 0, 554618, 75172, 1585, 65536⟩
    (by decide) selected_cut_21673

theorem selected_cut_21674 : selected 9 ⟨365907, by decide⟩
    (prefixPartial 12 75173) = some ⟨12, 1, 0, 365907, 75173, 1, 65536⟩ := by
  decide +kernel

theorem context_12_75173_365907 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75173 ⟨365907, by decide⟩ :=
  accepted_of_selected 12 75173 ⟨365907, by decide⟩ ⟨12, 1, 0, 365907, 75173, 1, 65536⟩
    (by decide) selected_cut_21674

theorem selected_cut_21675 : selected 9 ⟨554638, by decide⟩
    (prefixPartial 12 75174) = some ⟨12, 2, 0, 554638, 75174, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_75174_554638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75174 ⟨554638, by decide⟩ :=
  accepted_of_selected 12 75174 ⟨554638, by decide⟩ ⟨12, 2, 0, 554638, 75174, 1493, 65536⟩
    (by decide) selected_cut_21675

theorem selected_cut_21676 : selected 9 ⟨554652, by decide⟩
    (prefixPartial 12 75175) = some ⟨12, 2, 0, 554652, 75175, 1657, 65536⟩ := by
  decide +kernel

theorem context_12_75175_554652 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75175 ⟨554652, by decide⟩ :=
  accepted_of_selected 12 75175 ⟨554652, by decide⟩ ⟨12, 2, 0, 554652, 75175, 1657, 65536⟩
    (by decide) selected_cut_21676

theorem unmarked_context_11_18793_554653 : frontier 10 ⟨554653, by decide⟩
    (prefixCache 11 18793) (prefixPartial 11 18793) = false := by
  decide +kernel

theorem node_context_11_18793_554653 : EJMOriginalGlobalDAGData.nodes 10 ⟨554653, by decide⟩ =
    .split (coordinate 11) (![⟨554618, by decide⟩,⟨365907, by decide⟩,⟨554638, by decide⟩,⟨554652, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18793_554653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18793 ⟨554653, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18793
    ⟨554653, by decide⟩ (by decide) (![⟨554618, by decide⟩,⟨365907, by decide⟩,⟨554638, by decide⟩,⟨554652, by decide⟩]) unmarked_context_11_18793_554653 node_context_11_18793_554653
  intro a
  fin_cases a
  · exact context_12_75172_554618
  · exact context_12_75173_365907
  · exact context_12_75174_554638
  · exact context_12_75175_554652

theorem selected_cut_21677 : selected 9 ⟨554687, by decide⟩
    (prefixPartial 12 75176) = some ⟨12, 2, 0, 554687, 75176, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_75176_554687 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75176 ⟨554687, by decide⟩ :=
  accepted_of_selected 12 75176 ⟨554687, by decide⟩ ⟨12, 2, 0, 554687, 75176, 1769, 65536⟩
    (by decide) selected_cut_21677

theorem selected_cut_21678 : selected 9 ⟨554703, by decide⟩
    (prefixPartial 12 75177) = some ⟨12, 2, 0, 554703, 75177, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_75177_554703 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75177 ⟨554703, by decide⟩ :=
  accepted_of_selected 12 75177 ⟨554703, by decide⟩ ⟨12, 2, 0, 554703, 75177, 1445, 65536⟩
    (by decide) selected_cut_21678

theorem selected_cut_21679 : selected 9 ⟨554723, by decide⟩
    (prefixPartial 12 75178) = some ⟨12, 2, 0, 554723, 75178, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_75178_554723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75178 ⟨554723, by decide⟩ :=
  accepted_of_selected 12 75178 ⟨554723, by decide⟩ ⟨12, 2, 0, 554723, 75178, 1477, 65536⟩
    (by decide) selected_cut_21679

theorem selected_cut_21680 : selected 9 ⟨554746, by decide⟩
    (prefixPartial 12 75179) = some ⟨12, 2, 0, 554746, 75179, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_75179_554746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75179 ⟨554746, by decide⟩ :=
  accepted_of_selected 12 75179 ⟨554746, by decide⟩ ⟨12, 2, 0, 554746, 75179, 1621, 65536⟩
    (by decide) selected_cut_21680

theorem unmarked_context_11_18794_554747 : frontier 10 ⟨554747, by decide⟩
    (prefixCache 11 18794) (prefixPartial 11 18794) = false := by
  decide +kernel

theorem node_context_11_18794_554747 : EJMOriginalGlobalDAGData.nodes 10 ⟨554747, by decide⟩ =
    .split (coordinate 11) (![⟨554687, by decide⟩,⟨554703, by decide⟩,⟨554723, by decide⟩,⟨554746, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18794_554747 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18794 ⟨554747, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18794
    ⟨554747, by decide⟩ (by decide) (![⟨554687, by decide⟩,⟨554703, by decide⟩,⟨554723, by decide⟩,⟨554746, by decide⟩]) unmarked_context_11_18794_554747 node_context_11_18794_554747
  intro a
  fin_cases a
  · exact context_12_75176_554687
  · exact context_12_75177_554703
  · exact context_12_75178_554723
  · exact context_12_75179_554746

theorem selected_cut_21681 : selected 9 ⟨554765, by decide⟩
    (prefixPartial 12 75180) = some ⟨12, 2, 0, 554765, 75180, 1585, 65536⟩ := by
  decide +kernel

theorem context_12_75180_554765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75180 ⟨554765, by decide⟩ :=
  accepted_of_selected 12 75180 ⟨554765, by decide⟩ ⟨12, 2, 0, 554765, 75180, 1585, 65536⟩
    (by decide) selected_cut_21681

theorem selected_cut_21682 : selected 9 ⟨554781, by decide⟩
    (prefixPartial 12 75181) = some ⟨12, 2, 0, 554781, 75181, 1285, 65536⟩ := by
  decide +kernel

theorem context_12_75181_554781 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75181 ⟨554781, by decide⟩ :=
  accepted_of_selected 12 75181 ⟨554781, by decide⟩ ⟨12, 2, 0, 554781, 75181, 1285, 65536⟩
    (by decide) selected_cut_21682

theorem selected_cut_21683 : selected 9 ⟨554799, by decide⟩
    (prefixPartial 12 75182) = some ⟨12, 2, 0, 554799, 75182, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_75182_554799 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75182 ⟨554799, by decide⟩ :=
  accepted_of_selected 12 75182 ⟨554799, by decide⟩ ⟨12, 2, 0, 554799, 75182, 1437, 65536⟩
    (by decide) selected_cut_21683

theorem selected_cut_21684 : selected 9 ⟨554819, by decide⟩
    (prefixPartial 12 75183) = some ⟨12, 2, 0, 554819, 75183, 1489, 65536⟩ := by
  decide +kernel

theorem context_12_75183_554819 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75183 ⟨554819, by decide⟩ :=
  accepted_of_selected 12 75183 ⟨554819, by decide⟩ ⟨12, 2, 0, 554819, 75183, 1489, 65536⟩
    (by decide) selected_cut_21684

theorem unmarked_context_11_18795_554820 : frontier 10 ⟨554820, by decide⟩
    (prefixCache 11 18795) (prefixPartial 11 18795) = false := by
  decide +kernel

theorem node_context_11_18795_554820 : EJMOriginalGlobalDAGData.nodes 10 ⟨554820, by decide⟩ =
    .split (coordinate 11) (![⟨554765, by decide⟩,⟨554781, by decide⟩,⟨554799, by decide⟩,⟨554819, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18795_554820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18795 ⟨554820, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18795
    ⟨554820, by decide⟩ (by decide) (![⟨554765, by decide⟩,⟨554781, by decide⟩,⟨554799, by decide⟩,⟨554819, by decide⟩]) unmarked_context_11_18795_554820 node_context_11_18795_554820
  intro a
  fin_cases a
  · exact context_12_75180_554765
  · exact context_12_75181_554781
  · exact context_12_75182_554799
  · exact context_12_75183_554819

theorem unmarked_context_10_4698_554821 : frontier 11 ⟨554821, by decide⟩
    (prefixCache 10 4698) (prefixPartial 10 4698) = false := by
  decide +kernel

theorem node_context_10_4698_554821 : EJMOriginalGlobalDAGData.nodes 11 ⟨554821, by decide⟩ =
    .split (coordinate 10) (![⟨554600, by decide⟩,⟨554653, by decide⟩,⟨554747, by decide⟩,⟨554820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_4698_554821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 4698 ⟨554821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 4698
    ⟨554821, by decide⟩ (by decide) (![⟨554600, by decide⟩,⟨554653, by decide⟩,⟨554747, by decide⟩,⟨554820, by decide⟩]) unmarked_context_10_4698_554821 node_context_10_4698_554821
  intro a
  fin_cases a
  · exact context_11_18792_554600
  · exact context_11_18793_554653
  · exact context_11_18794_554747
  · exact context_11_18795_554820

theorem selected_cut_21685 : selected 9 ⟨554837, by decide⟩
    (prefixPartial 12 75184) = some ⟨12, 2, 0, 554837, 75184, 1217, 65536⟩ := by
  decide +kernel

theorem context_12_75184_554837 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75184 ⟨554837, by decide⟩ :=
  accepted_of_selected 12 75184 ⟨554837, by decide⟩ ⟨12, 2, 0, 554837, 75184, 1217, 65536⟩
    (by decide) selected_cut_21685

theorem selected_cut_21686 : selected 9 ⟨554848, by decide⟩
    (prefixPartial 12 75185) = some ⟨12, 2, 0, 554848, 75185, 1077, 65536⟩ := by
  decide +kernel

theorem context_12_75185_554848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75185 ⟨554848, by decide⟩ :=
  accepted_of_selected 12 75185 ⟨554848, by decide⟩ ⟨12, 2, 0, 554848, 75185, 1077, 65536⟩
    (by decide) selected_cut_21686

theorem selected_cut_21687 : selected 9 ⟨554867, by decide⟩
    (prefixPartial 12 75186) = some ⟨12, 2, 0, 554867, 75186, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_75186_554867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75186 ⟨554867, by decide⟩ :=
  accepted_of_selected 12 75186 ⟨554867, by decide⟩ ⟨12, 2, 0, 554867, 75186, 1369, 65536⟩
    (by decide) selected_cut_21687

theorem selected_cut_21688 : selected 9 ⟨554882, by decide⟩
    (prefixPartial 12 75187) = some ⟨12, 2, 0, 554882, 75187, 1189, 65536⟩ := by
  decide +kernel

theorem context_12_75187_554882 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75187 ⟨554882, by decide⟩ :=
  accepted_of_selected 12 75187 ⟨554882, by decide⟩ ⟨12, 2, 0, 554882, 75187, 1189, 65536⟩
    (by decide) selected_cut_21688

theorem unmarked_context_11_18796_554883 : frontier 10 ⟨554883, by decide⟩
    (prefixCache 11 18796) (prefixPartial 11 18796) = false := by
  decide +kernel

theorem node_context_11_18796_554883 : EJMOriginalGlobalDAGData.nodes 10 ⟨554883, by decide⟩ =
    .split (coordinate 11) (![⟨554837, by decide⟩,⟨554848, by decide⟩,⟨554867, by decide⟩,⟨554882, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18796_554883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18796 ⟨554883, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18796
    ⟨554883, by decide⟩ (by decide) (![⟨554837, by decide⟩,⟨554848, by decide⟩,⟨554867, by decide⟩,⟨554882, by decide⟩]) unmarked_context_11_18796_554883 node_context_11_18796_554883
  intro a
  fin_cases a
  · exact context_12_75184_554837
  · exact context_12_75185_554848
  · exact context_12_75186_554867
  · exact context_12_75187_554882

theorem selected_cut_21689 : selected 9 ⟨554898, by decide⟩
    (prefixPartial 12 75188) = some ⟨12, 2, 0, 554898, 75188, 1197, 65536⟩ := by
  decide +kernel

theorem context_12_75188_554898 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75188 ⟨554898, by decide⟩ :=
  accepted_of_selected 12 75188 ⟨554898, by decide⟩ ⟨12, 2, 0, 554898, 75188, 1197, 65536⟩
    (by decide) selected_cut_21689

theorem selected_cut_21690 : selected 9 ⟨554917, by decide⟩
    (prefixPartial 12 75189) = some ⟨12, 2, 0, 554917, 75189, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_75189_554917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75189 ⟨554917, by decide⟩ :=
  accepted_of_selected 12 75189 ⟨554917, by decide⟩ ⟨12, 2, 0, 554917, 75189, 1541, 65536⟩
    (by decide) selected_cut_21690

theorem selected_cut_21691 : selected 9 ⟨554931, by decide⟩
    (prefixPartial 12 75190) = some ⟨12, 2, 0, 554931, 75190, 1305, 65536⟩ := by
  decide +kernel

theorem context_12_75190_554931 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75190 ⟨554931, by decide⟩ :=
  accepted_of_selected 12 75190 ⟨554931, by decide⟩ ⟨12, 2, 0, 554931, 75190, 1305, 65536⟩
    (by decide) selected_cut_21691

theorem selected_cut_21692 : selected 9 ⟨554946, by decide⟩
    (prefixPartial 12 75191) = some ⟨12, 2, 0, 554946, 75191, 1089, 65536⟩ := by
  decide +kernel

theorem context_12_75191_554946 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75191 ⟨554946, by decide⟩ :=
  accepted_of_selected 12 75191 ⟨554946, by decide⟩ ⟨12, 2, 0, 554946, 75191, 1089, 65536⟩
    (by decide) selected_cut_21692

theorem unmarked_context_11_18797_554947 : frontier 10 ⟨554947, by decide⟩
    (prefixCache 11 18797) (prefixPartial 11 18797) = false := by
  decide +kernel

theorem node_context_11_18797_554947 : EJMOriginalGlobalDAGData.nodes 10 ⟨554947, by decide⟩ =
    .split (coordinate 11) (![⟨554898, by decide⟩,⟨554917, by decide⟩,⟨554931, by decide⟩,⟨554946, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18797_554947 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18797 ⟨554947, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18797
    ⟨554947, by decide⟩ (by decide) (![⟨554898, by decide⟩,⟨554917, by decide⟩,⟨554931, by decide⟩,⟨554946, by decide⟩]) unmarked_context_11_18797_554947 node_context_11_18797_554947
  intro a
  fin_cases a
  · exact context_12_75188_554898
  · exact context_12_75189_554917
  · exact context_12_75190_554931
  · exact context_12_75191_554946

theorem selected_cut_21693 : selected 9 ⟨554971, by decide⟩
    (prefixPartial 12 75192) = some ⟨12, 2, 0, 554971, 75192, 1393, 65536⟩ := by
  decide +kernel

theorem context_12_75192_554971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75192 ⟨554971, by decide⟩ :=
  accepted_of_selected 12 75192 ⟨554971, by decide⟩ ⟨12, 2, 0, 554971, 75192, 1393, 65536⟩
    (by decide) selected_cut_21693

theorem selected_cut_21694 : selected 9 ⟨554986, by decide⟩
    (prefixPartial 12 75193) = some ⟨12, 2, 0, 554986, 75193, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_75193_554986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75193 ⟨554986, by decide⟩ :=
  accepted_of_selected 12 75193 ⟨554986, by decide⟩ ⟨12, 2, 0, 554986, 75193, 1181, 65536⟩
    (by decide) selected_cut_21694

theorem selected_cut_21695 : selected 9 ⟨555006, by decide⟩
    (prefixPartial 12 75194) = some ⟨12, 2, 0, 555006, 75194, 1325, 65536⟩ := by
  decide +kernel

theorem context_12_75194_555006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75194 ⟨555006, by decide⟩ :=
  accepted_of_selected 12 75194 ⟨555006, by decide⟩ ⟨12, 2, 0, 555006, 75194, 1325, 65536⟩
    (by decide) selected_cut_21695

theorem selected_cut_21696 : selected 9 ⟨555027, by decide⟩
    (prefixPartial 12 75195) = some ⟨12, 2, 0, 555027, 75195, 1169, 65536⟩ := by
  decide +kernel

theorem context_12_75195_555027 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75195 ⟨555027, by decide⟩ :=
  accepted_of_selected 12 75195 ⟨555027, by decide⟩ ⟨12, 2, 0, 555027, 75195, 1169, 65536⟩
    (by decide) selected_cut_21696

theorem unmarked_context_11_18798_555028 : frontier 10 ⟨555028, by decide⟩
    (prefixCache 11 18798) (prefixPartial 11 18798) = false := by
  decide +kernel

theorem node_context_11_18798_555028 : EJMOriginalGlobalDAGData.nodes 10 ⟨555028, by decide⟩ =
    .split (coordinate 11) (![⟨554971, by decide⟩,⟨554986, by decide⟩,⟨555006, by decide⟩,⟨555027, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_18798_555028 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 18798 ⟨555028, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 18798
    ⟨555028, by decide⟩ (by decide) (![⟨554971, by decide⟩,⟨554986, by decide⟩,⟨555006, by decide⟩,⟨555027, by decide⟩]) unmarked_context_11_18798_555028 node_context_11_18798_555028
  intro a
  fin_cases a
  · exact context_12_75192_554971
  · exact context_12_75193_554986
  · exact context_12_75194_555006
  · exact context_12_75195_555027

theorem selected_cut_21697 : selected 9 ⟨555038, by decide⟩
    (prefixPartial 12 75196) = some ⟨12, 2, 0, 555038, 75196, 1105, 65536⟩ := by
  decide +kernel

theorem context_12_75196_555038 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75196 ⟨555038, by decide⟩ :=
  accepted_of_selected 12 75196 ⟨555038, by decide⟩ ⟨12, 2, 0, 555038, 75196, 1105, 65536⟩
    (by decide) selected_cut_21697

theorem selected_cut_21698 : selected 9 ⟨555047, by decide⟩
    (prefixPartial 12 75197) = some ⟨12, 2, 0, 555047, 75197, 885, 65536⟩ := by
  decide +kernel

theorem context_12_75197_555047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75197 ⟨555047, by decide⟩ :=
  accepted_of_selected 12 75197 ⟨555047, by decide⟩ ⟨12, 2, 0, 555047, 75197, 885, 65536⟩
    (by decide) selected_cut_21698

theorem selected_cut_21699 : selected 9 ⟨555062, by decide⟩
    (prefixPartial 12 75198) = some ⟨12, 2, 0, 555062, 75198, 1181, 65536⟩ := by
  decide +kernel

theorem context_12_75198_555062 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 75198 ⟨555062, by decide⟩ :=
  accepted_of_selected 12 75198 ⟨555062, by decide⟩ ⟨12, 2, 0, 555062, 75198, 1181, 65536⟩
    (by decide) selected_cut_21699

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
