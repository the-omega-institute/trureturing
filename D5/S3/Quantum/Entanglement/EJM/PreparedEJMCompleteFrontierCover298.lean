/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover297
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_28611 : selected 9 ⟨721795, by decide⟩
    (prefixPartial 12 92550) = some ⟨12, 2, 0, 721795, 92550, 2233, 65536⟩ := by
  decide +kernel

theorem context_12_92550_721795 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92550 ⟨721795, by decide⟩ :=
  accepted_of_selected 12 92550 ⟨721795, by decide⟩ ⟨12, 2, 0, 721795, 92550, 2233, 65536⟩
    (by decide) selected_cut_28611

theorem selected_cut_28612 : selected 9 ⟨721820, by decide⟩
    (prefixPartial 12 92551) = some ⟨12, 2, 0, 721820, 92551, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_92551_721820 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92551 ⟨721820, by decide⟩ :=
  accepted_of_selected 12 92551 ⟨721820, by decide⟩ ⟨12, 2, 0, 721820, 92551, 1913, 65536⟩
    (by decide) selected_cut_28612

theorem unmarked_context_11_23137_721821 : frontier 10 ⟨721821, by decide⟩
    (prefixCache 11 23137) (prefixPartial 11 23137) = false := by
  decide +kernel

theorem node_context_11_23137_721821 : EJMOriginalGlobalDAGData.nodes 10 ⟨721821, by decide⟩ =
    .split (coordinate 11) (![⟨721770, by decide⟩,⟨721771, by decide⟩,⟨721795, by decide⟩,⟨721820, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23137_721821 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23137 ⟨721821, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23137
    ⟨721821, by decide⟩ (by decide) (![⟨721770, by decide⟩,⟨721771, by decide⟩,⟨721795, by decide⟩,⟨721820, by decide⟩]) unmarked_context_11_23137_721821 node_context_11_23137_721821
  intro a
  fin_cases a
  · exact context_12_92548_721770
  · exact context_12_92549_721771
  · exact context_12_92550_721795
  · exact context_12_92551_721820

theorem selected_cut_28613 : selected 9 ⟨721853, by decide⟩
    (prefixPartial 12 92552) = some ⟨12, 2, 0, 721853, 92552, 2125, 65536⟩ := by
  decide +kernel

theorem context_12_92552_721853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92552 ⟨721853, by decide⟩ :=
  accepted_of_selected 12 92552 ⟨721853, by decide⟩ ⟨12, 2, 0, 721853, 92552, 2125, 65536⟩
    (by decide) selected_cut_28613

theorem selected_cut_28614 : selected 9 ⟨721879, by decide⟩
    (prefixPartial 12 92553) = some ⟨12, 2, 0, 721879, 92553, 1785, 65536⟩ := by
  decide +kernel

theorem context_12_92553_721879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92553 ⟨721879, by decide⟩ :=
  accepted_of_selected 12 92553 ⟨721879, by decide⟩ ⟨12, 2, 0, 721879, 92553, 1785, 65536⟩
    (by decide) selected_cut_28614

theorem selected_cut_28615 : selected 9 ⟨721909, by decide⟩
    (prefixPartial 12 92554) = some ⟨12, 2, 0, 721909, 92554, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_92554_721909 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92554 ⟨721909, by decide⟩ :=
  accepted_of_selected 12 92554 ⟨721909, by decide⟩ ⟨12, 2, 0, 721909, 92554, 2113, 65536⟩
    (by decide) selected_cut_28615

theorem selected_cut_28616 : selected 9 ⟨721936, by decide⟩
    (prefixPartial 12 92555) = some ⟨12, 2, 0, 721936, 92555, 1869, 65536⟩ := by
  decide +kernel

theorem context_12_92555_721936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92555 ⟨721936, by decide⟩ :=
  accepted_of_selected 12 92555 ⟨721936, by decide⟩ ⟨12, 2, 0, 721936, 92555, 1869, 65536⟩
    (by decide) selected_cut_28616

theorem unmarked_context_11_23138_721937 : frontier 10 ⟨721937, by decide⟩
    (prefixCache 11 23138) (prefixPartial 11 23138) = false := by
  decide +kernel

theorem node_context_11_23138_721937 : EJMOriginalGlobalDAGData.nodes 10 ⟨721937, by decide⟩ =
    .split (coordinate 11) (![⟨721853, by decide⟩,⟨721879, by decide⟩,⟨721909, by decide⟩,⟨721936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23138_721937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23138 ⟨721937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23138
    ⟨721937, by decide⟩ (by decide) (![⟨721853, by decide⟩,⟨721879, by decide⟩,⟨721909, by decide⟩,⟨721936, by decide⟩]) unmarked_context_11_23138_721937 node_context_11_23138_721937
  intro a
  fin_cases a
  · exact context_12_92552_721853
  · exact context_12_92553_721879
  · exact context_12_92554_721909
  · exact context_12_92555_721936

theorem selected_cut_28617 : selected 9 ⟨721963, by decide⟩
    (prefixPartial 12 92556) = some ⟨12, 2, 0, 721963, 92556, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_92556_721963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92556 ⟨721963, by decide⟩ :=
  accepted_of_selected 12 92556 ⟨721963, by decide⟩ ⟨12, 2, 0, 721963, 92556, 2229, 65536⟩
    (by decide) selected_cut_28617

theorem selected_cut_28618 : selected 9 ⟨721990, by decide⟩
    (prefixPartial 12 92557) = some ⟨12, 2, 0, 721990, 92557, 1817, 65536⟩ := by
  decide +kernel

theorem context_12_92557_721990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92557 ⟨721990, by decide⟩ :=
  accepted_of_selected 12 92557 ⟨721990, by decide⟩ ⟨12, 2, 0, 721990, 92557, 1817, 65536⟩
    (by decide) selected_cut_28618

theorem selected_cut_28619 : selected 9 ⟨722016, by decide⟩
    (prefixPartial 12 92558) = some ⟨12, 2, 0, 722016, 92558, 2345, 65536⟩ := by
  decide +kernel

theorem context_12_92558_722016 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92558 ⟨722016, by decide⟩ :=
  accepted_of_selected 12 92558 ⟨722016, by decide⟩ ⟨12, 2, 0, 722016, 92558, 2345, 65536⟩
    (by decide) selected_cut_28619

theorem selected_cut_28620 : selected 9 ⟨722043, by decide⟩
    (prefixPartial 12 92559) = some ⟨12, 2, 0, 722043, 92559, 1969, 65536⟩ := by
  decide +kernel

theorem context_12_92559_722043 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92559 ⟨722043, by decide⟩ :=
  accepted_of_selected 12 92559 ⟨722043, by decide⟩ ⟨12, 2, 0, 722043, 92559, 1969, 65536⟩
    (by decide) selected_cut_28620

theorem unmarked_context_11_23139_722044 : frontier 10 ⟨722044, by decide⟩
    (prefixCache 11 23139) (prefixPartial 11 23139) = false := by
  decide +kernel

theorem node_context_11_23139_722044 : EJMOriginalGlobalDAGData.nodes 10 ⟨722044, by decide⟩ =
    .split (coordinate 11) (![⟨721963, by decide⟩,⟨721990, by decide⟩,⟨722016, by decide⟩,⟨722043, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23139_722044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23139 ⟨722044, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23139
    ⟨722044, by decide⟩ (by decide) (![⟨721963, by decide⟩,⟨721990, by decide⟩,⟨722016, by decide⟩,⟨722043, by decide⟩]) unmarked_context_11_23139_722044 node_context_11_23139_722044
  intro a
  fin_cases a
  · exact context_12_92556_721963
  · exact context_12_92557_721990
  · exact context_12_92558_722016
  · exact context_12_92559_722043

theorem unmarked_context_10_5784_722045 : frontier 11 ⟨722045, by decide⟩
    (prefixCache 10 5784) (prefixPartial 10 5784) = false := by
  decide +kernel

theorem node_context_10_5784_722045 : EJMOriginalGlobalDAGData.nodes 11 ⟨722045, by decide⟩ =
    .split (coordinate 10) (![⟨721742, by decide⟩,⟨721821, by decide⟩,⟨721937, by decide⟩,⟨722044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5784_722045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5784 ⟨722045, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5784
    ⟨722045, by decide⟩ (by decide) (![⟨721742, by decide⟩,⟨721821, by decide⟩,⟨721937, by decide⟩,⟨722044, by decide⟩]) unmarked_context_10_5784_722045 node_context_10_5784_722045
  intro a
  fin_cases a
  · exact context_11_23136_721742
  · exact context_11_23137_721821
  · exact context_11_23138_721937
  · exact context_11_23139_722044

theorem selected_cut_28621 : selected 9 ⟨722063, by decide⟩
    (prefixPartial 12 92560) = some ⟨12, 2, 0, 722063, 92560, 1769, 65536⟩ := by
  decide +kernel

theorem context_12_92560_722063 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92560 ⟨722063, by decide⟩ :=
  accepted_of_selected 12 92560 ⟨722063, by decide⟩ ⟨12, 2, 0, 722063, 92560, 1769, 65536⟩
    (by decide) selected_cut_28621

theorem selected_cut_28622 : selected 9 ⟨722080, by decide⟩
    (prefixPartial 12 92561) = some ⟨12, 2, 0, 722080, 92561, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_92561_722080 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92561 ⟨722080, by decide⟩ :=
  accepted_of_selected 12 92561 ⟨722080, by decide⟩ ⟨12, 2, 0, 722080, 92561, 1673, 65536⟩
    (by decide) selected_cut_28622

theorem selected_cut_28623 : selected 9 ⟨722107, by decide⟩
    (prefixPartial 12 92562) = some ⟨12, 2, 0, 722107, 92562, 2053, 65536⟩ := by
  decide +kernel

theorem context_12_92562_722107 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92562 ⟨722107, by decide⟩ :=
  accepted_of_selected 12 92562 ⟨722107, by decide⟩ ⟨12, 2, 0, 722107, 92562, 2053, 65536⟩
    (by decide) selected_cut_28623

theorem selected_cut_28624 : selected 9 ⟨722129, by decide⟩
    (prefixPartial 12 92563) = some ⟨12, 2, 0, 722129, 92563, 1781, 65536⟩ := by
  decide +kernel

theorem context_12_92563_722129 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92563 ⟨722129, by decide⟩ :=
  accepted_of_selected 12 92563 ⟨722129, by decide⟩ ⟨12, 2, 0, 722129, 92563, 1781, 65536⟩
    (by decide) selected_cut_28624

theorem unmarked_context_11_23140_722130 : frontier 10 ⟨722130, by decide⟩
    (prefixCache 11 23140) (prefixPartial 11 23140) = false := by
  decide +kernel

theorem node_context_11_23140_722130 : EJMOriginalGlobalDAGData.nodes 10 ⟨722130, by decide⟩ =
    .split (coordinate 11) (![⟨722063, by decide⟩,⟨722080, by decide⟩,⟨722107, by decide⟩,⟨722129, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23140_722130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23140 ⟨722130, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23140
    ⟨722130, by decide⟩ (by decide) (![⟨722063, by decide⟩,⟨722080, by decide⟩,⟨722107, by decide⟩,⟨722129, by decide⟩]) unmarked_context_11_23140_722130 node_context_11_23140_722130
  intro a
  fin_cases a
  · exact context_12_92560_722063
  · exact context_12_92561_722080
  · exact context_12_92562_722107
  · exact context_12_92563_722129

theorem selected_cut_28625 : selected 9 ⟨722148, by decide⟩
    (prefixPartial 12 92564) = some ⟨12, 2, 0, 722148, 92564, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_92564_722148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92564 ⟨722148, by decide⟩ :=
  accepted_of_selected 12 92564 ⟨722148, by decide⟩ ⟨12, 2, 0, 722148, 92564, 1517, 65536⟩
    (by decide) selected_cut_28625

theorem selected_cut_28626 : selected 9 ⟨439069, by decide⟩
    (prefixPartial 12 92565) = some ⟨12, 1, 0, 439069, 92565, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92565_439069 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92565 ⟨439069, by decide⟩ :=
  accepted_of_selected 12 92565 ⟨439069, by decide⟩ ⟨12, 1, 0, 439069, 92565, 1, 65536⟩
    (by decide) selected_cut_28626

theorem selected_cut_28627 : selected 9 ⟨722166, by decide⟩
    (prefixPartial 12 92566) = some ⟨12, 2, 0, 722166, 92566, 1745, 65536⟩ := by
  decide +kernel

theorem context_12_92566_722166 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92566 ⟨722166, by decide⟩ :=
  accepted_of_selected 12 92566 ⟨722166, by decide⟩ ⟨12, 2, 0, 722166, 92566, 1745, 65536⟩
    (by decide) selected_cut_28627

theorem selected_cut_28628 : selected 9 ⟨722181, by decide⟩
    (prefixPartial 12 92567) = some ⟨12, 2, 0, 722181, 92567, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_92567_722181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92567 ⟨722181, by decide⟩ :=
  accepted_of_selected 12 92567 ⟨722181, by decide⟩ ⟨12, 2, 0, 722181, 92567, 1465, 65536⟩
    (by decide) selected_cut_28628

theorem unmarked_context_11_23141_722182 : frontier 10 ⟨722182, by decide⟩
    (prefixCache 11 23141) (prefixPartial 11 23141) = false := by
  decide +kernel

theorem node_context_11_23141_722182 : EJMOriginalGlobalDAGData.nodes 10 ⟨722182, by decide⟩ =
    .split (coordinate 11) (![⟨722148, by decide⟩,⟨439069, by decide⟩,⟨722166, by decide⟩,⟨722181, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23141_722182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23141 ⟨722182, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23141
    ⟨722182, by decide⟩ (by decide) (![⟨722148, by decide⟩,⟨439069, by decide⟩,⟨722166, by decide⟩,⟨722181, by decide⟩]) unmarked_context_11_23141_722182 node_context_11_23141_722182
  intro a
  fin_cases a
  · exact context_12_92564_722148
  · exact context_12_92565_439069
  · exact context_12_92566_722166
  · exact context_12_92567_722181

theorem selected_cut_28629 : selected 9 ⟨722200, by decide⟩
    (prefixPartial 12 92568) = some ⟨12, 2, 0, 722200, 92568, 1593, 65536⟩ := by
  decide +kernel

theorem context_12_92568_722200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92568 ⟨722200, by decide⟩ :=
  accepted_of_selected 12 92568 ⟨722200, by decide⟩ ⟨12, 2, 0, 722200, 92568, 1593, 65536⟩
    (by decide) selected_cut_28629

theorem selected_cut_28630 : selected 9 ⟨722222, by decide⟩
    (prefixPartial 12 92569) = some ⟨12, 2, 0, 722222, 92569, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_92569_722222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92569 ⟨722222, by decide⟩ :=
  accepted_of_selected 12 92569 ⟨722222, by decide⟩ ⟨12, 2, 0, 722222, 92569, 1525, 65536⟩
    (by decide) selected_cut_28630

theorem selected_cut_28631 : selected 9 ⟨722243, by decide⟩
    (prefixPartial 12 92570) = some ⟨12, 2, 0, 722243, 92570, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_92570_722243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92570 ⟨722243, by decide⟩ :=
  accepted_of_selected 12 92570 ⟨722243, by decide⟩ ⟨12, 2, 0, 722243, 92570, 1673, 65536⟩
    (by decide) selected_cut_28631

theorem selected_cut_28632 : selected 9 ⟨722258, by decide⟩
    (prefixPartial 12 92571) = some ⟨12, 2, 0, 722258, 92571, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_92571_722258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92571 ⟨722258, by decide⟩ :=
  accepted_of_selected 12 92571 ⟨722258, by decide⟩ ⟨12, 2, 0, 722258, 92571, 1385, 65536⟩
    (by decide) selected_cut_28632

theorem unmarked_context_11_23142_722259 : frontier 10 ⟨722259, by decide⟩
    (prefixCache 11 23142) (prefixPartial 11 23142) = false := by
  decide +kernel

theorem node_context_11_23142_722259 : EJMOriginalGlobalDAGData.nodes 10 ⟨722259, by decide⟩ =
    .split (coordinate 11) (![⟨722200, by decide⟩,⟨722222, by decide⟩,⟨722243, by decide⟩,⟨722258, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23142_722259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23142 ⟨722259, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23142
    ⟨722259, by decide⟩ (by decide) (![⟨722200, by decide⟩,⟨722222, by decide⟩,⟨722243, by decide⟩,⟨722258, by decide⟩]) unmarked_context_11_23142_722259 node_context_11_23142_722259
  intro a
  fin_cases a
  · exact context_12_92568_722200
  · exact context_12_92569_722222
  · exact context_12_92570_722243
  · exact context_12_92571_722258

theorem selected_cut_28633 : selected 9 ⟨722275, by decide⟩
    (prefixPartial 12 92572) = some ⟨12, 2, 0, 722275, 92572, 1677, 65536⟩ := by
  decide +kernel

theorem context_12_92572_722275 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92572 ⟨722275, by decide⟩ :=
  accepted_of_selected 12 92572 ⟨722275, by decide⟩ ⟨12, 2, 0, 722275, 92572, 1677, 65536⟩
    (by decide) selected_cut_28633

theorem selected_cut_28634 : selected 9 ⟨722292, by decide⟩
    (prefixPartial 12 92573) = some ⟨12, 2, 0, 722292, 92573, 1497, 65536⟩ := by
  decide +kernel

theorem context_12_92573_722292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92573 ⟨722292, by decide⟩ :=
  accepted_of_selected 12 92573 ⟨722292, by decide⟩ ⟨12, 2, 0, 722292, 92573, 1497, 65536⟩
    (by decide) selected_cut_28634

theorem selected_cut_28635 : selected 9 ⟨722320, by decide⟩
    (prefixPartial 12 92574) = some ⟨12, 2, 0, 722320, 92574, 1737, 65536⟩ := by
  decide +kernel

theorem context_12_92574_722320 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92574 ⟨722320, by decide⟩ :=
  accepted_of_selected 12 92574 ⟨722320, by decide⟩ ⟨12, 2, 0, 722320, 92574, 1737, 65536⟩
    (by decide) selected_cut_28635

theorem selected_cut_28636 : selected 9 ⟨722337, by decide⟩
    (prefixPartial 12 92575) = some ⟨12, 2, 0, 722337, 92575, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_92575_722337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92575 ⟨722337, by decide⟩ :=
  accepted_of_selected 12 92575 ⟨722337, by decide⟩ ⟨12, 2, 0, 722337, 92575, 1493, 65536⟩
    (by decide) selected_cut_28636

theorem unmarked_context_11_23143_722338 : frontier 10 ⟨722338, by decide⟩
    (prefixCache 11 23143) (prefixPartial 11 23143) = false := by
  decide +kernel

theorem node_context_11_23143_722338 : EJMOriginalGlobalDAGData.nodes 10 ⟨722338, by decide⟩ =
    .split (coordinate 11) (![⟨722275, by decide⟩,⟨722292, by decide⟩,⟨722320, by decide⟩,⟨722337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23143_722338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23143 ⟨722338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23143
    ⟨722338, by decide⟩ (by decide) (![⟨722275, by decide⟩,⟨722292, by decide⟩,⟨722320, by decide⟩,⟨722337, by decide⟩]) unmarked_context_11_23143_722338 node_context_11_23143_722338
  intro a
  fin_cases a
  · exact context_12_92572_722275
  · exact context_12_92573_722292
  · exact context_12_92574_722320
  · exact context_12_92575_722337

theorem unmarked_context_10_5785_722339 : frontier 11 ⟨722339, by decide⟩
    (prefixCache 10 5785) (prefixPartial 10 5785) = false := by
  decide +kernel

theorem node_context_10_5785_722339 : EJMOriginalGlobalDAGData.nodes 11 ⟨722339, by decide⟩ =
    .split (coordinate 10) (![⟨722130, by decide⟩,⟨722182, by decide⟩,⟨722259, by decide⟩,⟨722338, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5785_722339 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5785 ⟨722339, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5785
    ⟨722339, by decide⟩ (by decide) (![⟨722130, by decide⟩,⟨722182, by decide⟩,⟨722259, by decide⟩,⟨722338, by decide⟩]) unmarked_context_10_5785_722339 node_context_10_5785_722339
  intro a
  fin_cases a
  · exact context_11_23140_722130
  · exact context_11_23141_722182
  · exact context_11_23142_722259
  · exact context_11_23143_722338

theorem selected_cut_28637 : selected 9 ⟨722355, by decide⟩
    (prefixPartial 12 92576) = some ⟨12, 2, 0, 722355, 92576, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_92576_722355 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92576 ⟨722355, by decide⟩ :=
  accepted_of_selected 12 92576 ⟨722355, by decide⟩ ⟨12, 2, 0, 722355, 92576, 1357, 65536⟩
    (by decide) selected_cut_28637

theorem selected_cut_28638 : selected 9 ⟨722372, by decide⟩
    (prefixPartial 12 92577) = some ⟨12, 2, 0, 722372, 92577, 1221, 65536⟩ := by
  decide +kernel

theorem context_12_92577_722372 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92577 ⟨722372, by decide⟩ :=
  accepted_of_selected 12 92577 ⟨722372, by decide⟩ ⟨12, 2, 0, 722372, 92577, 1221, 65536⟩
    (by decide) selected_cut_28638

theorem selected_cut_28639 : selected 9 ⟨722392, by decide⟩
    (prefixPartial 12 92578) = some ⟨12, 2, 0, 722392, 92578, 1525, 65536⟩ := by
  decide +kernel

theorem context_12_92578_722392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92578 ⟨722392, by decide⟩ :=
  accepted_of_selected 12 92578 ⟨722392, by decide⟩ ⟨12, 2, 0, 722392, 92578, 1525, 65536⟩
    (by decide) selected_cut_28639

theorem selected_cut_28640 : selected 9 ⟨722405, by decide⟩
    (prefixPartial 12 92579) = some ⟨12, 2, 0, 722405, 92579, 1261, 65536⟩ := by
  decide +kernel

theorem context_12_92579_722405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92579 ⟨722405, by decide⟩ :=
  accepted_of_selected 12 92579 ⟨722405, by decide⟩ ⟨12, 2, 0, 722405, 92579, 1261, 65536⟩
    (by decide) selected_cut_28640

theorem unmarked_context_11_23144_722406 : frontier 10 ⟨722406, by decide⟩
    (prefixCache 11 23144) (prefixPartial 11 23144) = false := by
  decide +kernel

theorem node_context_11_23144_722406 : EJMOriginalGlobalDAGData.nodes 10 ⟨722406, by decide⟩ =
    .split (coordinate 11) (![⟨722355, by decide⟩,⟨722372, by decide⟩,⟨722392, by decide⟩,⟨722405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23144_722406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23144 ⟨722406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23144
    ⟨722406, by decide⟩ (by decide) (![⟨722355, by decide⟩,⟨722372, by decide⟩,⟨722392, by decide⟩,⟨722405, by decide⟩]) unmarked_context_11_23144_722406 node_context_11_23144_722406
  intro a
  fin_cases a
  · exact context_12_92576_722355
  · exact context_12_92577_722372
  · exact context_12_92578_722392
  · exact context_12_92579_722405

theorem selected_cut_28641 : selected 10 ⟨722455, by decide⟩
    (prefixPartial 11 23145) = some ⟨11, 2, 0, 722455, 23145, 3677, 262144⟩ := by
  decide +kernel

theorem context_11_23145_722455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23145 ⟨722455, by decide⟩ :=
  accepted_of_selected 11 23145 ⟨722455, by decide⟩ ⟨11, 2, 0, 722455, 23145, 3677, 262144⟩
    (by decide) selected_cut_28641

theorem selected_cut_28642 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 23146) = some ⟨11, 1, 0, 479708, 23146, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23146_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23146 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 23146 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 23146, 1, 262144⟩
    (by decide) selected_cut_28642

theorem selected_cut_28643 : selected 9 ⟨722469, by decide⟩
    (prefixPartial 12 92588) = some ⟨12, 2, 0, 722469, 92588, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_92588_722469 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92588 ⟨722469, by decide⟩ :=
  accepted_of_selected 12 92588 ⟨722469, by decide⟩ ⟨12, 2, 0, 722469, 92588, 1433, 65536⟩
    (by decide) selected_cut_28643

theorem selected_cut_28644 : selected 9 ⟨722485, by decide⟩
    (prefixPartial 12 92589) = some ⟨12, 2, 0, 722485, 92589, 1193, 65536⟩ := by
  decide +kernel

theorem context_12_92589_722485 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92589 ⟨722485, by decide⟩ :=
  accepted_of_selected 12 92589 ⟨722485, by decide⟩ ⟨12, 2, 0, 722485, 92589, 1193, 65536⟩
    (by decide) selected_cut_28644

theorem selected_cut_28645 : selected 9 ⟨722500, by decide⟩
    (prefixPartial 12 92590) = some ⟨12, 2, 0, 722500, 92590, 1425, 65536⟩ := by
  decide +kernel

theorem context_12_92590_722500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92590 ⟨722500, by decide⟩ :=
  accepted_of_selected 12 92590 ⟨722500, by decide⟩ ⟨12, 2, 0, 722500, 92590, 1425, 65536⟩
    (by decide) selected_cut_28645

theorem selected_cut_28646 : selected 9 ⟨722515, by decide⟩
    (prefixPartial 12 92591) = some ⟨12, 2, 0, 722515, 92591, 1153, 65536⟩ := by
  decide +kernel

theorem context_12_92591_722515 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92591 ⟨722515, by decide⟩ :=
  accepted_of_selected 12 92591 ⟨722515, by decide⟩ ⟨12, 2, 0, 722515, 92591, 1153, 65536⟩
    (by decide) selected_cut_28646

theorem unmarked_context_11_23147_722516 : frontier 10 ⟨722516, by decide⟩
    (prefixCache 11 23147) (prefixPartial 11 23147) = false := by
  decide +kernel

theorem node_context_11_23147_722516 : EJMOriginalGlobalDAGData.nodes 10 ⟨722516, by decide⟩ =
    .split (coordinate 11) (![⟨722469, by decide⟩,⟨722485, by decide⟩,⟨722500, by decide⟩,⟨722515, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23147_722516 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23147 ⟨722516, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23147
    ⟨722516, by decide⟩ (by decide) (![⟨722469, by decide⟩,⟨722485, by decide⟩,⟨722500, by decide⟩,⟨722515, by decide⟩]) unmarked_context_11_23147_722516 node_context_11_23147_722516
  intro a
  fin_cases a
  · exact context_12_92588_722469
  · exact context_12_92589_722485
  · exact context_12_92590_722500
  · exact context_12_92591_722515

theorem unmarked_context_10_5786_722517 : frontier 11 ⟨722517, by decide⟩
    (prefixCache 10 5786) (prefixPartial 10 5786) = false := by
  decide +kernel

theorem node_context_10_5786_722517 : EJMOriginalGlobalDAGData.nodes 11 ⟨722517, by decide⟩ =
    .split (coordinate 10) (![⟨722406, by decide⟩,⟨722455, by decide⟩,⟨479708, by decide⟩,⟨722516, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5786_722517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5786 ⟨722517, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5786
    ⟨722517, by decide⟩ (by decide) (![⟨722406, by decide⟩,⟨722455, by decide⟩,⟨479708, by decide⟩,⟨722516, by decide⟩]) unmarked_context_10_5786_722517 node_context_10_5786_722517
  intro a
  fin_cases a
  · exact context_11_23144_722406
  · exact context_11_23145_722455
  · exact context_11_23146_479708
  · exact context_11_23147_722516

theorem selected_cut_28647 : selected 9 ⟨722532, by decide⟩
    (prefixPartial 12 92592) = some ⟨12, 2, 0, 722532, 92592, 1341, 65536⟩ := by
  decide +kernel

theorem context_12_92592_722532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92592 ⟨722532, by decide⟩ :=
  accepted_of_selected 12 92592 ⟨722532, by decide⟩ ⟨12, 2, 0, 722532, 92592, 1341, 65536⟩
    (by decide) selected_cut_28647

theorem selected_cut_28648 : selected 9 ⟨722545, by decide⟩
    (prefixPartial 12 92593) = some ⟨12, 2, 0, 722545, 92593, 1309, 65536⟩ := by
  decide +kernel

theorem context_12_92593_722545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92593 ⟨722545, by decide⟩ :=
  accepted_of_selected 12 92593 ⟨722545, by decide⟩ ⟨12, 2, 0, 722545, 92593, 1309, 65536⟩
    (by decide) selected_cut_28648

theorem selected_cut_28649 : selected 9 ⟨722557, by decide⟩
    (prefixPartial 12 92594) = some ⟨12, 2, 0, 722557, 92594, 1461, 65536⟩ := by
  decide +kernel

theorem context_12_92594_722557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92594 ⟨722557, by decide⟩ :=
  accepted_of_selected 12 92594 ⟨722557, by decide⟩ ⟨12, 2, 0, 722557, 92594, 1461, 65536⟩
    (by decide) selected_cut_28649

theorem selected_cut_28650 : selected 9 ⟨722574, by decide⟩
    (prefixPartial 12 92595) = some ⟨12, 2, 0, 722574, 92595, 1241, 65536⟩ := by
  decide +kernel

theorem context_12_92595_722574 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92595 ⟨722574, by decide⟩ :=
  accepted_of_selected 12 92595 ⟨722574, by decide⟩ ⟨12, 2, 0, 722574, 92595, 1241, 65536⟩
    (by decide) selected_cut_28650

theorem unmarked_context_11_23148_722575 : frontier 10 ⟨722575, by decide⟩
    (prefixCache 11 23148) (prefixPartial 11 23148) = false := by
  decide +kernel

theorem node_context_11_23148_722575 : EJMOriginalGlobalDAGData.nodes 10 ⟨722575, by decide⟩ =
    .split (coordinate 11) (![⟨722532, by decide⟩,⟨722545, by decide⟩,⟨722557, by decide⟩,⟨722574, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23148_722575 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23148 ⟨722575, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23148
    ⟨722575, by decide⟩ (by decide) (![⟨722532, by decide⟩,⟨722545, by decide⟩,⟨722557, by decide⟩,⟨722574, by decide⟩]) unmarked_context_11_23148_722575 node_context_11_23148_722575
  intro a
  fin_cases a
  · exact context_12_92592_722532
  · exact context_12_92593_722545
  · exact context_12_92594_722557
  · exact context_12_92595_722574

theorem selected_cut_28651 : selected 10 ⟨722607, by decide⟩
    (prefixPartial 11 23149) = some ⟨11, 2, 0, 722607, 23149, 3397, 262144⟩ := by
  decide +kernel

theorem context_11_23149_722607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23149 ⟨722607, by decide⟩ :=
  accepted_of_selected 11 23149 ⟨722607, by decide⟩ ⟨11, 2, 0, 722607, 23149, 3397, 262144⟩
    (by decide) selected_cut_28651

theorem selected_cut_28652 : selected 10 ⟨722653, by decide⟩
    (prefixPartial 11 23150) = some ⟨11, 2, 0, 722653, 23150, 4017, 262144⟩ := by
  decide +kernel

theorem context_11_23150_722653 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23150 ⟨722653, by decide⟩ :=
  accepted_of_selected 11 23150 ⟨722653, by decide⟩ ⟨11, 2, 0, 722653, 23150, 4017, 262144⟩
    (by decide) selected_cut_28652

theorem selected_cut_28653 : selected 9 ⟨722666, by decide⟩
    (prefixPartial 12 92604) = some ⟨12, 2, 0, 722666, 92604, 1185, 65536⟩ := by
  decide +kernel

theorem context_12_92604_722666 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92604 ⟨722666, by decide⟩ :=
  accepted_of_selected 12 92604 ⟨722666, by decide⟩ ⟨12, 2, 0, 722666, 92604, 1185, 65536⟩
    (by decide) selected_cut_28653

theorem selected_cut_28654 : selected 9 ⟨722680, by decide⟩
    (prefixPartial 12 92605) = some ⟨12, 2, 0, 722680, 92605, 1037, 65536⟩ := by
  decide +kernel

theorem context_12_92605_722680 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92605 ⟨722680, by decide⟩ :=
  accepted_of_selected 12 92605 ⟨722680, by decide⟩ ⟨12, 2, 0, 722680, 92605, 1037, 65536⟩
    (by decide) selected_cut_28654

theorem selected_cut_28655 : selected 9 ⟨722696, by decide⟩
    (prefixPartial 12 92606) = some ⟨12, 2, 0, 722696, 92606, 1161, 65536⟩ := by
  decide +kernel

theorem context_12_92606_722696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92606 ⟨722696, by decide⟩ :=
  accepted_of_selected 12 92606 ⟨722696, by decide⟩ ⟨12, 2, 0, 722696, 92606, 1161, 65536⟩
    (by decide) selected_cut_28655

theorem selected_cut_28656 : selected 9 ⟨722705, by decide⟩
    (prefixPartial 12 92607) = some ⟨12, 2, 0, 722705, 92607, 981, 65536⟩ := by
  decide +kernel

theorem context_12_92607_722705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92607 ⟨722705, by decide⟩ :=
  accepted_of_selected 12 92607 ⟨722705, by decide⟩ ⟨12, 2, 0, 722705, 92607, 981, 65536⟩
    (by decide) selected_cut_28656

theorem unmarked_context_11_23151_722706 : frontier 10 ⟨722706, by decide⟩
    (prefixCache 11 23151) (prefixPartial 11 23151) = false := by
  decide +kernel

theorem node_context_11_23151_722706 : EJMOriginalGlobalDAGData.nodes 10 ⟨722706, by decide⟩ =
    .split (coordinate 11) (![⟨722666, by decide⟩,⟨722680, by decide⟩,⟨722696, by decide⟩,⟨722705, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23151_722706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23151 ⟨722706, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23151
    ⟨722706, by decide⟩ (by decide) (![⟨722666, by decide⟩,⟨722680, by decide⟩,⟨722696, by decide⟩,⟨722705, by decide⟩]) unmarked_context_11_23151_722706 node_context_11_23151_722706
  intro a
  fin_cases a
  · exact context_12_92604_722666
  · exact context_12_92605_722680
  · exact context_12_92606_722696
  · exact context_12_92607_722705

theorem unmarked_context_10_5787_722707 : frontier 11 ⟨722707, by decide⟩
    (prefixCache 10 5787) (prefixPartial 10 5787) = false := by
  decide +kernel

theorem node_context_10_5787_722707 : EJMOriginalGlobalDAGData.nodes 11 ⟨722707, by decide⟩ =
    .split (coordinate 10) (![⟨722575, by decide⟩,⟨722607, by decide⟩,⟨722653, by decide⟩,⟨722706, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5787_722707 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5787 ⟨722707, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5787
    ⟨722707, by decide⟩ (by decide) (![⟨722575, by decide⟩,⟨722607, by decide⟩,⟨722653, by decide⟩,⟨722706, by decide⟩]) unmarked_context_10_5787_722707 node_context_10_5787_722707
  intro a
  fin_cases a
  · exact context_11_23148_722575
  · exact context_11_23149_722607
  · exact context_11_23150_722653
  · exact context_11_23151_722706

theorem unmarked_context_9_1446_722708 : frontier 12 ⟨722708, by decide⟩
    (prefixCache 9 1446) (prefixPartial 9 1446) = false := by
  decide +kernel

theorem node_context_9_1446_722708 : EJMOriginalGlobalDAGData.nodes 12 ⟨722708, by decide⟩ =
    .split (coordinate 9) (![⟨722045, by decide⟩,⟨722339, by decide⟩,⟨722517, by decide⟩,⟨722707, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1446_722708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1446 ⟨722708, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1446
    ⟨722708, by decide⟩ (by decide) (![⟨722045, by decide⟩,⟨722339, by decide⟩,⟨722517, by decide⟩,⟨722707, by decide⟩]) unmarked_context_9_1446_722708 node_context_9_1446_722708
  intro a
  fin_cases a
  · exact context_10_5784_722045
  · exact context_10_5785_722339
  · exact context_10_5786_722517
  · exact context_10_5787_722707

theorem selected_cut_28657 : selected 10 ⟨722742, by decide⟩
    (prefixPartial 11 23152) = some ⟨11, 2, 0, 722742, 23152, 3469, 262144⟩ := by
  decide +kernel

theorem context_11_23152_722742 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23152 ⟨722742, by decide⟩ :=
  accepted_of_selected 11 23152 ⟨722742, by decide⟩ ⟨11, 2, 0, 722742, 23152, 3469, 262144⟩
    (by decide) selected_cut_28657

theorem selected_cut_28658 : selected 10 ⟨722768, by decide⟩
    (prefixPartial 11 23153) = some ⟨11, 2, 0, 722768, 23153, 2453, 262144⟩ := by
  decide +kernel

theorem context_11_23153_722768 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23153 ⟨722768, by decide⟩ :=
  accepted_of_selected 11 23153 ⟨722768, by decide⟩ ⟨11, 2, 0, 722768, 23153, 2453, 262144⟩
    (by decide) selected_cut_28658

theorem selected_cut_28659 : selected 10 ⟨722798, by decide⟩
    (prefixPartial 11 23154) = some ⟨11, 2, 0, 722798, 23154, 3005, 262144⟩ := by
  decide +kernel

theorem context_11_23154_722798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23154 ⟨722798, by decide⟩ :=
  accepted_of_selected 11 23154 ⟨722798, by decide⟩ ⟨11, 2, 0, 722798, 23154, 3005, 262144⟩
    (by decide) selected_cut_28659

theorem selected_cut_28660 : selected 10 ⟨722848, by decide⟩
    (prefixPartial 11 23155) = some ⟨11, 2, 0, 722848, 23155, 3261, 262144⟩ := by
  decide +kernel

theorem context_11_23155_722848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23155 ⟨722848, by decide⟩ :=
  accepted_of_selected 11 23155 ⟨722848, by decide⟩ ⟨11, 2, 0, 722848, 23155, 3261, 262144⟩
    (by decide) selected_cut_28660

theorem unmarked_context_10_5788_722849 : frontier 11 ⟨722849, by decide⟩
    (prefixCache 10 5788) (prefixPartial 10 5788) = false := by
  decide +kernel

theorem node_context_10_5788_722849 : EJMOriginalGlobalDAGData.nodes 11 ⟨722849, by decide⟩ =
    .split (coordinate 10) (![⟨722742, by decide⟩,⟨722768, by decide⟩,⟨722798, by decide⟩,⟨722848, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5788_722849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5788 ⟨722849, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5788
    ⟨722849, by decide⟩ (by decide) (![⟨722742, by decide⟩,⟨722768, by decide⟩,⟨722798, by decide⟩,⟨722848, by decide⟩]) unmarked_context_10_5788_722849 node_context_10_5788_722849
  intro a
  fin_cases a
  · exact context_11_23152_722742
  · exact context_11_23153_722768
  · exact context_11_23154_722798
  · exact context_11_23155_722848

theorem selected_cut_28661 : selected 10 ⟨722867, by decide⟩
    (prefixPartial 11 23156) = some ⟨11, 2, 0, 722867, 23156, 2425, 262144⟩ := by
  decide +kernel

theorem context_11_23156_722867 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23156 ⟨722867, by decide⟩ :=
  accepted_of_selected 11 23156 ⟨722867, by decide⟩ ⟨11, 2, 0, 722867, 23156, 2425, 262144⟩
    (by decide) selected_cut_28661

theorem selected_cut_28662 : selected 10 ⟨722883, by decide⟩
    (prefixPartial 11 23157) = some ⟨11, 2, 0, 722883, 23157, 1645, 262144⟩ := by
  decide +kernel

theorem context_11_23157_722883 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23157 ⟨722883, by decide⟩ :=
  accepted_of_selected 11 23157 ⟨722883, by decide⟩ ⟨11, 2, 0, 722883, 23157, 1645, 262144⟩
    (by decide) selected_cut_28662

theorem selected_cut_28663 : selected 10 ⟨722902, by decide⟩
    (prefixPartial 11 23158) = some ⟨11, 2, 0, 722902, 23158, 2041, 262144⟩ := by
  decide +kernel

theorem context_11_23158_722902 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23158 ⟨722902, by decide⟩ :=
  accepted_of_selected 11 23158 ⟨722902, by decide⟩ ⟨11, 2, 0, 722902, 23158, 2041, 262144⟩
    (by decide) selected_cut_28663

theorem selected_cut_28664 : selected 10 ⟨722926, by decide⟩
    (prefixPartial 11 23159) = some ⟨11, 2, 0, 722926, 23159, 1933, 262144⟩ := by
  decide +kernel

theorem context_11_23159_722926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23159 ⟨722926, by decide⟩ :=
  accepted_of_selected 11 23159 ⟨722926, by decide⟩ ⟨11, 2, 0, 722926, 23159, 1933, 262144⟩
    (by decide) selected_cut_28664

theorem unmarked_context_10_5789_722927 : frontier 11 ⟨722927, by decide⟩
    (prefixCache 10 5789) (prefixPartial 10 5789) = false := by
  decide +kernel

theorem node_context_10_5789_722927 : EJMOriginalGlobalDAGData.nodes 11 ⟨722927, by decide⟩ =
    .split (coordinate 10) (![⟨722867, by decide⟩,⟨722883, by decide⟩,⟨722902, by decide⟩,⟨722926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5789_722927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5789 ⟨722927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5789
    ⟨722927, by decide⟩ (by decide) (![⟨722867, by decide⟩,⟨722883, by decide⟩,⟨722902, by decide⟩,⟨722926, by decide⟩]) unmarked_context_10_5789_722927 node_context_10_5789_722927
  intro a
  fin_cases a
  · exact context_11_23156_722867
  · exact context_11_23157_722883
  · exact context_11_23158_722902
  · exact context_11_23159_722926

theorem selected_cut_28665 : selected 10 ⟨722941, by decide⟩
    (prefixPartial 11 23160) = some ⟨11, 2, 0, 722941, 23160, 1517, 262144⟩ := by
  decide +kernel

theorem context_11_23160_722941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23160 ⟨722941, by decide⟩ :=
  accepted_of_selected 11 23160 ⟨722941, by decide⟩ ⟨11, 2, 0, 722941, 23160, 1517, 262144⟩
    (by decide) selected_cut_28665

theorem selected_cut_28666 : selected 10 ⟨722953, by decide⟩
    (prefixPartial 11 23161) = some ⟨11, 2, 0, 722953, 23161, 1033, 262144⟩ := by
  decide +kernel

theorem context_11_23161_722953 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23161 ⟨722953, by decide⟩ :=
  accepted_of_selected 11 23161 ⟨722953, by decide⟩ ⟨11, 2, 0, 722953, 23161, 1033, 262144⟩
    (by decide) selected_cut_28666

theorem selected_cut_28667 : selected 10 ⟨722970, by decide⟩
    (prefixPartial 11 23162) = some ⟨11, 2, 0, 722970, 23162, 1009, 262144⟩ := by
  decide +kernel

theorem context_11_23162_722970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23162 ⟨722970, by decide⟩ :=
  accepted_of_selected 11 23162 ⟨722970, by decide⟩ ⟨11, 2, 0, 722970, 23162, 1009, 262144⟩
    (by decide) selected_cut_28667

theorem selected_cut_28668 : selected 10 ⟨722987, by decide⟩
    (prefixPartial 11 23163) = some ⟨11, 2, 0, 722987, 23163, 953, 262144⟩ := by
  decide +kernel

theorem context_11_23163_722987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23163 ⟨722987, by decide⟩ :=
  accepted_of_selected 11 23163 ⟨722987, by decide⟩ ⟨11, 2, 0, 722987, 23163, 953, 262144⟩
    (by decide) selected_cut_28668

theorem unmarked_context_10_5790_722988 : frontier 11 ⟨722988, by decide⟩
    (prefixCache 10 5790) (prefixPartial 10 5790) = false := by
  decide +kernel

theorem node_context_10_5790_722988 : EJMOriginalGlobalDAGData.nodes 11 ⟨722988, by decide⟩ =
    .split (coordinate 10) (![⟨722941, by decide⟩,⟨722953, by decide⟩,⟨722970, by decide⟩,⟨722987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5790_722988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5790 ⟨722988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5790
    ⟨722988, by decide⟩ (by decide) (![⟨722941, by decide⟩,⟨722953, by decide⟩,⟨722970, by decide⟩,⟨722987, by decide⟩]) unmarked_context_10_5790_722988 node_context_10_5790_722988
  intro a
  fin_cases a
  · exact context_11_23160_722941
  · exact context_11_23161_722953
  · exact context_11_23162_722970
  · exact context_11_23163_722987

theorem selected_cut_28669 : selected 11 ⟨723011, by decide⟩
    (prefixPartial 10 5791) = some ⟨10, 2, 0, 723011, 5791, 1725, 1048576⟩ := by
  decide +kernel

theorem context_10_5791_723011 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5791 ⟨723011, by decide⟩ :=
  accepted_of_selected 10 5791 ⟨723011, by decide⟩ ⟨10, 2, 0, 723011, 5791, 1725, 1048576⟩
    (by decide) selected_cut_28669

theorem unmarked_context_9_1447_723012 : frontier 12 ⟨723012, by decide⟩
    (prefixCache 9 1447) (prefixPartial 9 1447) = false := by
  decide +kernel

theorem node_context_9_1447_723012 : EJMOriginalGlobalDAGData.nodes 12 ⟨723012, by decide⟩ =
    .split (coordinate 9) (![⟨722849, by decide⟩,⟨722927, by decide⟩,⟨722988, by decide⟩,⟨723011, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1447_723012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1447 ⟨723012, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1447
    ⟨723012, by decide⟩ (by decide) (![⟨722849, by decide⟩,⟨722927, by decide⟩,⟨722988, by decide⟩,⟨723011, by decide⟩]) unmarked_context_9_1447_723012 node_context_9_1447_723012
  intro a
  fin_cases a
  · exact context_10_5788_722849
  · exact context_10_5789_722927
  · exact context_10_5790_722988
  · exact context_10_5791_723011

theorem unmarked_context_8_361_723013 : frontier 13 ⟨723013, by decide⟩
    (prefixCache 8 361) (prefixPartial 8 361) = false := by
  decide +kernel

theorem node_context_8_361_723013 : EJMOriginalGlobalDAGData.nodes 13 ⟨723013, by decide⟩ =
    .split (coordinate 8) (![⟨719714, by decide⟩,⟨721630, by decide⟩,⟨722708, by decide⟩,⟨723012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_361_723013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 361 ⟨723013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 361
    ⟨723013, by decide⟩ (by decide) (![⟨719714, by decide⟩,⟨721630, by decide⟩,⟨722708, by decide⟩,⟨723012, by decide⟩]) unmarked_context_8_361_723013 node_context_8_361_723013
  intro a
  fin_cases a
  · exact context_9_1444_719714
  · exact context_9_1445_721630
  · exact context_9_1446_722708
  · exact context_9_1447_723012

theorem selected_cut_28670 : selected 13 ⟨158379, by decide⟩
    (prefixPartial 8 362) = some ⟨8, 1, 0, 158379, 362, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_362_158379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 362 ⟨158379, by decide⟩ :=
  accepted_of_selected 8 362 ⟨158379, by decide⟩ ⟨8, 1, 0, 158379, 362, 1, 16777216⟩
    (by decide) selected_cut_28670

theorem selected_cut_28671 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 23232) = some ⟨11, 1, 0, 434745, 23232, 1, 262144⟩ := by
  decide +kernel

theorem context_11_23232_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23232 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 23232 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 23232, 1, 262144⟩
    (by decide) selected_cut_28671

theorem selected_cut_28672 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92932) = some ⟨12, 1, 0, 4595, 92932, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92932_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92932 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92932 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92932, 1, 65536⟩
    (by decide) selected_cut_28672

theorem selected_cut_28673 : selected 9 ⟨34034, by decide⟩
    (prefixPartial 12 92933) = some ⟨12, 1, 0, 34034, 92933, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92933_34034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92933 ⟨34034, by decide⟩ :=
  accepted_of_selected 12 92933 ⟨34034, by decide⟩ ⟨12, 1, 0, 34034, 92933, 1, 65536⟩
    (by decide) selected_cut_28673

theorem selected_cut_28674 : selected 8 ⟨723106, by decide⟩
    (prefixPartial 13 371736) = some ⟨13, 2, 0, 723106, 371736, 3469, 16384⟩ := by
  decide +kernel

theorem context_13_371736_723106 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371736 ⟨723106, by decide⟩ :=
  accepted_of_selected 13 371736 ⟨723106, by decide⟩ ⟨13, 2, 0, 723106, 371736, 3469, 16384⟩
    (by decide) selected_cut_28674

theorem selected_cut_28675 : selected 8 ⟨723158, by decide⟩
    (prefixPartial 13 371737) = some ⟨13, 2, 0, 723158, 371737, 1525, 16384⟩ := by
  decide +kernel

theorem context_13_371737_723158 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371737 ⟨723158, by decide⟩ :=
  accepted_of_selected 13 371737 ⟨723158, by decide⟩ ⟨13, 2, 0, 723158, 371737, 1525, 16384⟩
    (by decide) selected_cut_28675

theorem selected_cut_28676 : selected 8 ⟨723185, by decide⟩
    (prefixPartial 13 371738) = some ⟨13, 2, 0, 723185, 371738, 737, 16384⟩ := by
  decide +kernel

theorem context_13_371738_723185 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371738 ⟨723185, by decide⟩ :=
  accepted_of_selected 13 371738 ⟨723185, by decide⟩ ⟨13, 2, 0, 723185, 371738, 737, 16384⟩
    (by decide) selected_cut_28676

theorem selected_cut_28677 : selected 8 ⟨531816, by decide⟩
    (prefixPartial 13 371739) = some ⟨13, 2, 0, 531816, 371739, 97, 16384⟩ := by
  decide +kernel

theorem context_13_371739_531816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371739 ⟨531816, by decide⟩ :=
  accepted_of_selected 13 371739 ⟨531816, by decide⟩ ⟨13, 2, 0, 531816, 371739, 97, 16384⟩
    (by decide) selected_cut_28677

theorem unmarked_context_12_92934_723186 : frontier 9 ⟨723186, by decide⟩
    (prefixCache 12 92934) (prefixPartial 12 92934) = false := by
  decide +kernel

theorem node_context_12_92934_723186 : EJMOriginalGlobalDAGData.nodes 9 ⟨723186, by decide⟩ =
    .split (coordinate 12) (![⟨723106, by decide⟩,⟨723158, by decide⟩,⟨723185, by decide⟩,⟨531816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92934_723186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92934 ⟨723186, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92934
    ⟨723186, by decide⟩ (by decide) (![⟨723106, by decide⟩,⟨723158, by decide⟩,⟨723185, by decide⟩,⟨531816, by decide⟩]) unmarked_context_12_92934_723186 node_context_12_92934_723186
  intro a
  fin_cases a
  · exact context_13_371736_723106
  · exact context_13_371737_723158
  · exact context_13_371738_723185
  · exact context_13_371739_531816

theorem selected_cut_28678 : selected 8 ⟨723252, by decide⟩
    (prefixPartial 13 371740) = some ⟨13, 2, 0, 723252, 371740, 3149, 16384⟩ := by
  decide +kernel

theorem context_13_371740_723252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371740 ⟨723252, by decide⟩ :=
  accepted_of_selected 13 371740 ⟨723252, by decide⟩ ⟨13, 2, 0, 723252, 371740, 3149, 16384⟩
    (by decide) selected_cut_28678

theorem selected_cut_28679 : selected 8 ⟨723304, by decide⟩
    (prefixPartial 13 371741) = some ⟨13, 2, 0, 723304, 371741, 2817, 16384⟩ := by
  decide +kernel

theorem context_13_371741_723304 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371741 ⟨723304, by decide⟩ :=
  accepted_of_selected 13 371741 ⟨723304, by decide⟩ ⟨13, 2, 0, 723304, 371741, 2817, 16384⟩
    (by decide) selected_cut_28679

theorem selected_cut_28680 : selected 8 ⟨723332, by decide⟩
    (prefixPartial 13 371742) = some ⟨13, 2, 0, 723332, 371742, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_371742_723332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371742 ⟨723332, by decide⟩ :=
  accepted_of_selected 13 371742 ⟨723332, by decide⟩ ⟨13, 2, 0, 723332, 371742, 2329, 16384⟩
    (by decide) selected_cut_28680

theorem selected_cut_28681 : selected 8 ⟨723340, by decide⟩
    (prefixPartial 13 371743) = some ⟨13, 2, 0, 723340, 371743, 885, 16384⟩ := by
  decide +kernel

theorem context_13_371743_723340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371743 ⟨723340, by decide⟩ :=
  accepted_of_selected 13 371743 ⟨723340, by decide⟩ ⟨13, 2, 0, 723340, 371743, 885, 16384⟩
    (by decide) selected_cut_28681

theorem unmarked_context_12_92935_723341 : frontier 9 ⟨723341, by decide⟩
    (prefixCache 12 92935) (prefixPartial 12 92935) = false := by
  decide +kernel

theorem node_context_12_92935_723341 : EJMOriginalGlobalDAGData.nodes 9 ⟨723341, by decide⟩ =
    .split (coordinate 12) (![⟨723252, by decide⟩,⟨723304, by decide⟩,⟨723332, by decide⟩,⟨723340, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92935_723341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92935 ⟨723341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92935
    ⟨723341, by decide⟩ (by decide) (![⟨723252, by decide⟩,⟨723304, by decide⟩,⟨723332, by decide⟩,⟨723340, by decide⟩]) unmarked_context_12_92935_723341 node_context_12_92935_723341
  intro a
  fin_cases a
  · exact context_13_371740_723252
  · exact context_13_371741_723304
  · exact context_13_371742_723332
  · exact context_13_371743_723340

theorem unmarked_context_11_23233_723342 : frontier 10 ⟨723342, by decide⟩
    (prefixCache 11 23233) (prefixPartial 11 23233) = false := by
  decide +kernel

theorem node_context_11_23233_723342 : EJMOriginalGlobalDAGData.nodes 10 ⟨723342, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨34034, by decide⟩,⟨723186, by decide⟩,⟨723341, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23233_723342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23233 ⟨723342, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23233
    ⟨723342, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨34034, by decide⟩,⟨723186, by decide⟩,⟨723341, by decide⟩]) unmarked_context_11_23233_723342 node_context_11_23233_723342
  intro a
  fin_cases a
  · exact context_12_92932_4595
  · exact context_12_92933_34034
  · exact context_12_92934_723186
  · exact context_12_92935_723341

theorem selected_cut_28682 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92936) = some ⟨12, 1, 0, 4595, 92936, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92936_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92936 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92936 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92936, 1, 65536⟩
    (by decide) selected_cut_28682

theorem selected_cut_28683 : selected 8 ⟨723433, by decide⟩
    (prefixPartial 13 371748) = some ⟨13, 2, 0, 723433, 371748, 3345, 16384⟩ := by
  decide +kernel

theorem context_13_371748_723433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371748 ⟨723433, by decide⟩ :=
  accepted_of_selected 13 371748 ⟨723433, by decide⟩ ⟨13, 2, 0, 723433, 371748, 3345, 16384⟩
    (by decide) selected_cut_28683

theorem selected_cut_28684 : selected 8 ⟨723483, by decide⟩
    (prefixPartial 13 371749) = some ⟨13, 2, 0, 723483, 371749, 1293, 16384⟩ := by
  decide +kernel

theorem context_13_371749_723483 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371749 ⟨723483, by decide⟩ :=
  accepted_of_selected 13 371749 ⟨723483, by decide⟩ ⟨13, 2, 0, 723483, 371749, 1293, 16384⟩
    (by decide) selected_cut_28684

theorem selected_cut_28685 : selected 8 ⟨723499, by decide⟩
    (prefixPartial 13 371750) = some ⟨13, 2, 0, 723499, 371750, 601, 16384⟩ := by
  decide +kernel

theorem context_13_371750_723499 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371750 ⟨723499, by decide⟩ :=
  accepted_of_selected 13 371750 ⟨723499, by decide⟩ ⟨13, 2, 0, 723499, 371750, 601, 16384⟩
    (by decide) selected_cut_28685

theorem selected_cut_28686 : selected 8 ⟨531816, by decide⟩
    (prefixPartial 13 371751) = some ⟨13, 2, 0, 531816, 371751, 97, 16384⟩ := by
  decide +kernel

theorem context_13_371751_531816 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371751 ⟨531816, by decide⟩ :=
  accepted_of_selected 13 371751 ⟨531816, by decide⟩ ⟨13, 2, 0, 531816, 371751, 97, 16384⟩
    (by decide) selected_cut_28686

theorem unmarked_context_12_92937_723500 : frontier 9 ⟨723500, by decide⟩
    (prefixCache 12 92937) (prefixPartial 12 92937) = false := by
  decide +kernel

theorem node_context_12_92937_723500 : EJMOriginalGlobalDAGData.nodes 9 ⟨723500, by decide⟩ =
    .split (coordinate 12) (![⟨723433, by decide⟩,⟨723483, by decide⟩,⟨723499, by decide⟩,⟨531816, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92937_723500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92937 ⟨723500, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92937
    ⟨723500, by decide⟩ (by decide) (![⟨723433, by decide⟩,⟨723483, by decide⟩,⟨723499, by decide⟩,⟨531816, by decide⟩]) unmarked_context_12_92937_723500 node_context_12_92937_723500
  intro a
  fin_cases a
  · exact context_13_371748_723433
  · exact context_13_371749_723483
  · exact context_13_371750_723499
  · exact context_13_371751_531816

theorem selected_cut_28687 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92938) = some ⟨12, 1, 0, 4595, 92938, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92938_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92938 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92938 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92938, 1, 65536⟩
    (by decide) selected_cut_28687

theorem selected_cut_28688 : selected 8 ⟨723551, by decide⟩
    (prefixPartial 13 371756) = some ⟨13, 2, 0, 723551, 371756, 2905, 16384⟩ := by
  decide +kernel

theorem context_13_371756_723551 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371756 ⟨723551, by decide⟩ :=
  accepted_of_selected 13 371756 ⟨723551, by decide⟩ ⟨13, 2, 0, 723551, 371756, 2905, 16384⟩
    (by decide) selected_cut_28688

theorem selected_cut_28689 : selected 8 ⟨723605, by decide⟩
    (prefixPartial 13 371757) = some ⟨13, 2, 0, 723605, 371757, 2969, 16384⟩ := by
  decide +kernel

theorem context_13_371757_723605 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371757 ⟨723605, by decide⟩ :=
  accepted_of_selected 13 371757 ⟨723605, by decide⟩ ⟨13, 2, 0, 723605, 371757, 2969, 16384⟩
    (by decide) selected_cut_28689

theorem selected_cut_28690 : selected 8 ⟨723627, by decide⟩
    (prefixPartial 13 371758) = some ⟨13, 2, 0, 723627, 371758, 2033, 16384⟩ := by
  decide +kernel

theorem context_13_371758_723627 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371758 ⟨723627, by decide⟩ :=
  accepted_of_selected 13 371758 ⟨723627, by decide⟩ ⟨13, 2, 0, 723627, 371758, 2033, 16384⟩
    (by decide) selected_cut_28690

theorem selected_cut_28691 : selected 8 ⟨723635, by decide⟩
    (prefixPartial 13 371759) = some ⟨13, 2, 0, 723635, 371759, 841, 16384⟩ := by
  decide +kernel

theorem context_13_371759_723635 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371759 ⟨723635, by decide⟩ :=
  accepted_of_selected 13 371759 ⟨723635, by decide⟩ ⟨13, 2, 0, 723635, 371759, 841, 16384⟩
    (by decide) selected_cut_28691

theorem unmarked_context_12_92939_723636 : frontier 9 ⟨723636, by decide⟩
    (prefixCache 12 92939) (prefixPartial 12 92939) = false := by
  decide +kernel

theorem node_context_12_92939_723636 : EJMOriginalGlobalDAGData.nodes 9 ⟨723636, by decide⟩ =
    .split (coordinate 12) (![⟨723551, by decide⟩,⟨723605, by decide⟩,⟨723627, by decide⟩,⟨723635, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92939_723636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92939 ⟨723636, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92939
    ⟨723636, by decide⟩ (by decide) (![⟨723551, by decide⟩,⟨723605, by decide⟩,⟨723627, by decide⟩,⟨723635, by decide⟩]) unmarked_context_12_92939_723636 node_context_12_92939_723636
  intro a
  fin_cases a
  · exact context_13_371756_723551
  · exact context_13_371757_723605
  · exact context_13_371758_723627
  · exact context_13_371759_723635

theorem unmarked_context_11_23234_723637 : frontier 10 ⟨723637, by decide⟩
    (prefixCache 11 23234) (prefixPartial 11 23234) = false := by
  decide +kernel

theorem node_context_11_23234_723637 : EJMOriginalGlobalDAGData.nodes 10 ⟨723637, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨723500, by decide⟩,⟨4595, by decide⟩,⟨723636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23234_723637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23234 ⟨723637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23234
    ⟨723637, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨723500, by decide⟩,⟨4595, by decide⟩,⟨723636, by decide⟩]) unmarked_context_11_23234_723637 node_context_11_23234_723637
  intro a
  fin_cases a
  · exact context_12_92936_4595
  · exact context_12_92937_723500
  · exact context_12_92938_4595
  · exact context_12_92939_723636

theorem selected_cut_28692 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92940) = some ⟨12, 1, 0, 4595, 92940, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92940_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92940 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92940 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92940, 1, 65536⟩
    (by decide) selected_cut_28692

theorem selected_cut_28693 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92941) = some ⟨12, 1, 0, 4595, 92941, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92941_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92941 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92941 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92941, 1, 65536⟩
    (by decide) selected_cut_28693

theorem selected_cut_28694 : selected 9 ⟨4595, by decide⟩
    (prefixPartial 12 92942) = some ⟨12, 1, 0, 4595, 92942, 1, 65536⟩ := by
  decide +kernel

theorem context_12_92942_4595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92942 ⟨4595, by decide⟩ :=
  accepted_of_selected 12 92942 ⟨4595, by decide⟩ ⟨12, 1, 0, 4595, 92942, 1, 65536⟩
    (by decide) selected_cut_28694

theorem selected_cut_28695 : selected 7 ⟨723648, by decide⟩
    (prefixPartial 14 1487088) = some ⟨14, 2, 0, 723648, 1487088, 201, 4096⟩ := by
  decide +kernel

theorem context_14_1487088_723648 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1487088 ⟨723648, by decide⟩ :=
  accepted_of_selected 14 1487088 ⟨723648, by decide⟩ ⟨14, 2, 0, 723648, 1487088, 201, 4096⟩
    (by decide) selected_cut_28695

theorem selected_cut_28696 : selected 7 ⟨723695, by decide⟩
    (prefixPartial 14 1487089) = some ⟨14, 2, 0, 723695, 1487089, 2041, 4096⟩ := by
  decide +kernel

theorem context_14_1487089_723695 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1487089 ⟨723695, by decide⟩ :=
  accepted_of_selected 14 1487089 ⟨723695, by decide⟩ ⟨14, 2, 0, 723695, 1487089, 2041, 4096⟩
    (by decide) selected_cut_28696

theorem selected_cut_28697 : selected 7 ⟨723728, by decide⟩
    (prefixPartial 14 1487090) = some ⟨14, 2, 0, 723728, 1487090, 1297, 4096⟩ := by
  decide +kernel

theorem context_14_1487090_723728 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1487090 ⟨723728, by decide⟩ :=
  accepted_of_selected 14 1487090 ⟨723728, by decide⟩ ⟨14, 2, 0, 723728, 1487090, 1297, 4096⟩
    (by decide) selected_cut_28697

theorem selected_cut_28698 : selected 7 ⟨723759, by decide⟩
    (prefixPartial 14 1487091) = some ⟨14, 2, 0, 723759, 1487091, 1217, 4096⟩ := by
  decide +kernel

theorem context_14_1487091_723759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 14 1487091 ⟨723759, by decide⟩ :=
  accepted_of_selected 14 1487091 ⟨723759, by decide⟩ ⟨14, 2, 0, 723759, 1487091, 1217, 4096⟩
    (by decide) selected_cut_28698

theorem unmarked_context_13_371772_723760 : frontier 8 ⟨723760, by decide⟩
    (prefixCache 13 371772) (prefixPartial 13 371772) = false := by
  decide +kernel

theorem node_context_13_371772_723760 : EJMOriginalGlobalDAGData.nodes 8 ⟨723760, by decide⟩ =
    .split (coordinate 13) (![⟨723648, by decide⟩,⟨723695, by decide⟩,⟨723728, by decide⟩,⟨723759, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_13_371772_723760 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371772 ⟨723760, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 13 371772
    ⟨723760, by decide⟩ (by decide) (![⟨723648, by decide⟩,⟨723695, by decide⟩,⟨723728, by decide⟩,⟨723759, by decide⟩]) unmarked_context_13_371772_723760 node_context_13_371772_723760
  intro a
  fin_cases a
  · exact context_14_1487088_723648
  · exact context_14_1487089_723695
  · exact context_14_1487090_723728
  · exact context_14_1487091_723759

theorem selected_cut_28699 : selected 8 ⟨723862, by decide⟩
    (prefixPartial 13 371773) = some ⟨13, 2, 0, 723862, 371773, 2289, 16384⟩ := by
  decide +kernel

theorem context_13_371773_723862 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371773 ⟨723862, by decide⟩ :=
  accepted_of_selected 13 371773 ⟨723862, by decide⟩ ⟨13, 2, 0, 723862, 371773, 2289, 16384⟩
    (by decide) selected_cut_28699

theorem selected_cut_28700 : selected 8 ⟨723915, by decide⟩
    (prefixPartial 13 371774) = some ⟨13, 2, 0, 723915, 371774, 1077, 16384⟩ := by
  decide +kernel

theorem context_13_371774_723915 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371774 ⟨723915, by decide⟩ :=
  accepted_of_selected 13 371774 ⟨723915, by decide⟩ ⟨13, 2, 0, 723915, 371774, 1077, 16384⟩
    (by decide) selected_cut_28700

theorem selected_cut_28701 : selected 8 ⟨723917, by decide⟩
    (prefixPartial 13 371775) = some ⟨13, 2, 0, 723917, 371775, 117, 16384⟩ := by
  decide +kernel

theorem context_13_371775_723917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371775 ⟨723917, by decide⟩ :=
  accepted_of_selected 13 371775 ⟨723917, by decide⟩ ⟨13, 2, 0, 723917, 371775, 117, 16384⟩
    (by decide) selected_cut_28701

theorem unmarked_context_12_92943_723918 : frontier 9 ⟨723918, by decide⟩
    (prefixCache 12 92943) (prefixPartial 12 92943) = false := by
  decide +kernel

theorem node_context_12_92943_723918 : EJMOriginalGlobalDAGData.nodes 9 ⟨723918, by decide⟩ =
    .split (coordinate 12) (![⟨723760, by decide⟩,⟨723862, by decide⟩,⟨723915, by decide⟩,⟨723917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92943_723918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92943 ⟨723918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92943
    ⟨723918, by decide⟩ (by decide) (![⟨723760, by decide⟩,⟨723862, by decide⟩,⟨723915, by decide⟩,⟨723917, by decide⟩]) unmarked_context_12_92943_723918 node_context_12_92943_723918
  intro a
  fin_cases a
  · exact context_13_371772_723760
  · exact context_13_371773_723862
  · exact context_13_371774_723915
  · exact context_13_371775_723917

theorem unmarked_context_11_23235_723919 : frontier 10 ⟨723919, by decide⟩
    (prefixCache 11 23235) (prefixPartial 11 23235) = false := by
  decide +kernel

theorem node_context_11_23235_723919 : EJMOriginalGlobalDAGData.nodes 10 ⟨723919, by decide⟩ =
    .split (coordinate 11) (![⟨4595, by decide⟩,⟨4595, by decide⟩,⟨4595, by decide⟩,⟨723918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23235_723919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23235 ⟨723919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23235
    ⟨723919, by decide⟩ (by decide) (![⟨4595, by decide⟩,⟨4595, by decide⟩,⟨4595, by decide⟩,⟨723918, by decide⟩]) unmarked_context_11_23235_723919 node_context_11_23235_723919
  intro a
  fin_cases a
  · exact context_12_92940_4595
  · exact context_12_92941_4595
  · exact context_12_92942_4595
  · exact context_12_92943_723918

theorem unmarked_context_10_5808_723920 : frontier 11 ⟨723920, by decide⟩
    (prefixCache 10 5808) (prefixPartial 10 5808) = false := by
  decide +kernel

theorem node_context_10_5808_723920 : EJMOriginalGlobalDAGData.nodes 11 ⟨723920, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨723342, by decide⟩,⟨723637, by decide⟩,⟨723919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5808_723920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5808 ⟨723920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5808
    ⟨723920, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨723342, by decide⟩,⟨723637, by decide⟩,⟨723919, by decide⟩]) unmarked_context_10_5808_723920 node_context_10_5808_723920
  intro a
  fin_cases a
  · exact context_11_23232_434745
  · exact context_11_23233_723342
  · exact context_11_23234_723637
  · exact context_11_23235_723919

theorem selected_cut_28702 : selected 8 ⟨723950, by decide⟩
    (prefixPartial 13 371776) = some ⟨13, 2, 0, 723950, 371776, 2229, 16384⟩ := by
  decide +kernel

theorem context_13_371776_723950 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371776 ⟨723950, by decide⟩ :=
  accepted_of_selected 13 371776 ⟨723950, by decide⟩ ⟨13, 2, 0, 723950, 371776, 2229, 16384⟩
    (by decide) selected_cut_28702

theorem selected_cut_28703 : selected 8 ⟨723972, by decide⟩
    (prefixPartial 13 371777) = some ⟨13, 2, 0, 723972, 371777, 1741, 16384⟩ := by
  decide +kernel

theorem context_13_371777_723972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371777 ⟨723972, by decide⟩ :=
  accepted_of_selected 13 371777 ⟨723972, by decide⟩ ⟨13, 2, 0, 723972, 371777, 1741, 16384⟩
    (by decide) selected_cut_28703

theorem selected_cut_28704 : selected 8 ⟨723990, by decide⟩
    (prefixPartial 13 371778) = some ⟨13, 2, 0, 723990, 371778, 1533, 16384⟩ := by
  decide +kernel

theorem context_13_371778_723990 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371778 ⟨723990, by decide⟩ :=
  accepted_of_selected 13 371778 ⟨723990, by decide⟩ ⟨13, 2, 0, 723990, 371778, 1533, 16384⟩
    (by decide) selected_cut_28704

theorem selected_cut_28705 : selected 8 ⟨723994, by decide⟩
    (prefixPartial 13 371779) = some ⟨13, 2, 0, 723994, 371779, 689, 16384⟩ := by
  decide +kernel

theorem context_13_371779_723994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371779 ⟨723994, by decide⟩ :=
  accepted_of_selected 13 371779 ⟨723994, by decide⟩ ⟨13, 2, 0, 723994, 371779, 689, 16384⟩
    (by decide) selected_cut_28705

theorem unmarked_context_12_92944_723995 : frontier 9 ⟨723995, by decide⟩
    (prefixCache 12 92944) (prefixPartial 12 92944) = false := by
  decide +kernel

theorem node_context_12_92944_723995 : EJMOriginalGlobalDAGData.nodes 9 ⟨723995, by decide⟩ =
    .split (coordinate 12) (![⟨723950, by decide⟩,⟨723972, by decide⟩,⟨723990, by decide⟩,⟨723994, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_92944_723995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 92944 ⟨723995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 92944
    ⟨723995, by decide⟩ (by decide) (![⟨723950, by decide⟩,⟨723972, by decide⟩,⟨723990, by decide⟩,⟨723994, by decide⟩]) unmarked_context_12_92944_723995 node_context_12_92944_723995
  intro a
  fin_cases a
  · exact context_13_371776_723950
  · exact context_13_371777_723972
  · exact context_13_371778_723990
  · exact context_13_371779_723994

theorem selected_cut_28706 : selected 8 ⟨724035, by decide⟩
    (prefixPartial 13 371780) = some ⟨13, 2, 0, 724035, 371780, 2485, 16384⟩ := by
  decide +kernel

theorem context_13_371780_724035 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 371780 ⟨724035, by decide⟩ :=
  accepted_of_selected 13 371780 ⟨724035, by decide⟩ ⟨13, 2, 0, 724035, 371780, 2485, 16384⟩
    (by decide) selected_cut_28706

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
