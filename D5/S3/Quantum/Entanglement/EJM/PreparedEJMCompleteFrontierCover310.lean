/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover309
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_29765 : selected 8 ⟨750788, by decide⟩
    (prefixPartial 13 375023) = some ⟨13, 2, 0, 750788, 375023, 937, 16384⟩ := by
  decide +kernel

theorem context_13_375023_750788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375023 ⟨750788, by decide⟩ :=
  accepted_of_selected 13 375023 ⟨750788, by decide⟩ ⟨13, 2, 0, 750788, 375023, 937, 16384⟩
    (by decide) selected_cut_29765

theorem unmarked_context_12_93755_750789 : frontier 9 ⟨750789, by decide⟩
    (prefixCache 12 93755) (prefixPartial 12 93755) = false := by
  decide +kernel

theorem node_context_12_93755_750789 : EJMOriginalGlobalDAGData.nodes 9 ⟨750789, by decide⟩ =
    .split (coordinate 12) (![⟨750720, by decide⟩,⟨750760, by decide⟩,⟨750781, by decide⟩,⟨750788, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93755_750789 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93755 ⟨750789, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93755
    ⟨750789, by decide⟩ (by decide) (![⟨750720, by decide⟩,⟨750760, by decide⟩,⟨750781, by decide⟩,⟨750788, by decide⟩]) unmarked_context_12_93755_750789 node_context_12_93755_750789
  intro a
  fin_cases a
  · exact context_13_375020_750720
  · exact context_13_375021_750760
  · exact context_13_375022_750781
  · exact context_13_375023_750788

theorem unmarked_context_11_23438_750790 : frontier 10 ⟨750790, by decide⟩
    (prefixCache 11 23438) (prefixPartial 11 23438) = false := by
  decide +kernel

theorem node_context_11_23438_750790 : EJMOriginalGlobalDAGData.nodes 10 ⟨750790, by decide⟩ =
    .split (coordinate 11) (![⟨750528, by decide⟩,⟨750593, by decide⟩,⟨750716, by decide⟩,⟨750789, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23438_750790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23438 ⟨750790, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23438
    ⟨750790, by decide⟩ (by decide) (![⟨750528, by decide⟩,⟨750593, by decide⟩,⟨750716, by decide⟩,⟨750789, by decide⟩]) unmarked_context_11_23438_750790 node_context_11_23438_750790
  intro a
  fin_cases a
  · exact context_12_93752_750528
  · exact context_12_93753_750593
  · exact context_12_93754_750716
  · exact context_12_93755_750789

theorem selected_cut_29766 : selected 9 ⟨399383, by decide⟩
    (prefixPartial 12 93756) = some ⟨12, 1, 0, 399383, 93756, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93756_399383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93756 ⟨399383, by decide⟩ :=
  accepted_of_selected 12 93756 ⟨399383, by decide⟩ ⟨12, 1, 0, 399383, 93756, 1, 65536⟩
    (by decide) selected_cut_29766

theorem selected_cut_29767 : selected 8 ⟨750793, by decide⟩
    (prefixPartial 13 375028) = some ⟨13, 2, 0, 750793, 375028, 9, 16384⟩ := by
  decide +kernel

theorem context_13_375028_750793 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375028 ⟨750793, by decide⟩ :=
  accepted_of_selected 13 375028 ⟨750793, by decide⟩ ⟨13, 2, 0, 750793, 375028, 9, 16384⟩
    (by decide) selected_cut_29767

theorem selected_cut_29768 : selected 8 ⟨750880, by decide⟩
    (prefixPartial 13 375029) = some ⟨13, 2, 0, 750880, 375029, 1653, 16384⟩ := by
  decide +kernel

theorem context_13_375029_750880 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375029 ⟨750880, by decide⟩ :=
  accepted_of_selected 13 375029 ⟨750880, by decide⟩ ⟨13, 2, 0, 750880, 375029, 1653, 16384⟩
    (by decide) selected_cut_29768

theorem selected_cut_29769 : selected 8 ⟨750937, by decide⟩
    (prefixPartial 13 375030) = some ⟨13, 2, 0, 750937, 375030, 1509, 16384⟩ := by
  decide +kernel

theorem context_13_375030_750937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375030 ⟨750937, by decide⟩ :=
  accepted_of_selected 13 375030 ⟨750937, by decide⟩ ⟨13, 2, 0, 750937, 375030, 1509, 16384⟩
    (by decide) selected_cut_29769

theorem selected_cut_29770 : selected 8 ⟨750980, by decide⟩
    (prefixPartial 13 375031) = some ⟨13, 2, 0, 750980, 375031, 945, 16384⟩ := by
  decide +kernel

theorem context_13_375031_750980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375031 ⟨750980, by decide⟩ :=
  accepted_of_selected 13 375031 ⟨750980, by decide⟩ ⟨13, 2, 0, 750980, 375031, 945, 16384⟩
    (by decide) selected_cut_29770

theorem unmarked_context_12_93757_750981 : frontier 9 ⟨750981, by decide⟩
    (prefixCache 12 93757) (prefixPartial 12 93757) = false := by
  decide +kernel

theorem node_context_12_93757_750981 : EJMOriginalGlobalDAGData.nodes 9 ⟨750981, by decide⟩ =
    .split (coordinate 12) (![⟨750793, by decide⟩,⟨750880, by decide⟩,⟨750937, by decide⟩,⟨750980, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93757_750981 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93757 ⟨750981, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93757
    ⟨750981, by decide⟩ (by decide) (![⟨750793, by decide⟩,⟨750880, by decide⟩,⟨750937, by decide⟩,⟨750980, by decide⟩]) unmarked_context_12_93757_750981 node_context_12_93757_750981
  intro a
  fin_cases a
  · exact context_13_375028_750793
  · exact context_13_375029_750880
  · exact context_13_375030_750937
  · exact context_13_375031_750980

theorem selected_cut_29771 : selected 9 ⟨399385, by decide⟩
    (prefixPartial 12 93758) = some ⟨12, 1, 0, 399385, 93758, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93758_399385 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93758 ⟨399385, by decide⟩ :=
  accepted_of_selected 12 93758 ⟨399385, by decide⟩ ⟨12, 1, 0, 399385, 93758, 1, 65536⟩
    (by decide) selected_cut_29771

theorem selected_cut_29772 : selected 9 ⟨399383, by decide⟩
    (prefixPartial 12 93759) = some ⟨12, 1, 0, 399383, 93759, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93759_399383 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93759 ⟨399383, by decide⟩ :=
  accepted_of_selected 12 93759 ⟨399383, by decide⟩ ⟨12, 1, 0, 399383, 93759, 1, 65536⟩
    (by decide) selected_cut_29772

theorem unmarked_context_11_23439_750982 : frontier 10 ⟨750982, by decide⟩
    (prefixCache 11 23439) (prefixPartial 11 23439) = false := by
  decide +kernel

theorem node_context_11_23439_750982 : EJMOriginalGlobalDAGData.nodes 10 ⟨750982, by decide⟩ =
    .split (coordinate 11) (![⟨399383, by decide⟩,⟨750981, by decide⟩,⟨399385, by decide⟩,⟨399383, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23439_750982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23439 ⟨750982, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23439
    ⟨750982, by decide⟩ (by decide) (![⟨399383, by decide⟩,⟨750981, by decide⟩,⟨399385, by decide⟩,⟨399383, by decide⟩]) unmarked_context_11_23439_750982 node_context_11_23439_750982
  intro a
  fin_cases a
  · exact context_12_93756_399383
  · exact context_12_93757_750981
  · exact context_12_93758_399385
  · exact context_12_93759_399383

theorem unmarked_context_10_5859_750983 : frontier 11 ⟨750983, by decide⟩
    (prefixCache 10 5859) (prefixPartial 10 5859) = false := by
  decide +kernel

theorem node_context_10_5859_750983 : EJMOriginalGlobalDAGData.nodes 11 ⟨750983, by decide⟩ =
    .split (coordinate 10) (![⟨750232, by decide⟩,⟨750466, by decide⟩,⟨750790, by decide⟩,⟨750982, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5859_750983 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5859 ⟨750983, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5859
    ⟨750983, by decide⟩ (by decide) (![⟨750232, by decide⟩,⟨750466, by decide⟩,⟨750790, by decide⟩,⟨750982, by decide⟩]) unmarked_context_10_5859_750983 node_context_10_5859_750983
  intro a
  fin_cases a
  · exact context_11_23436_750232
  · exact context_11_23437_750466
  · exact context_11_23438_750790
  · exact context_11_23439_750982

theorem unmarked_context_9_1464_750984 : frontier 12 ⟨750984, by decide⟩
    (prefixCache 9 1464) (prefixPartial 9 1464) = false := by
  decide +kernel

theorem node_context_9_1464_750984 : EJMOriginalGlobalDAGData.nodes 12 ⟨750984, by decide⟩ =
    .split (coordinate 9) (![⟨747473, by decide⟩,⟨748982, by decide⟩,⟨749973, by decide⟩,⟨750983, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1464_750984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1464 ⟨750984, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1464
    ⟨750984, by decide⟩ (by decide) (![⟨747473, by decide⟩,⟨748982, by decide⟩,⟨749973, by decide⟩,⟨750983, by decide⟩]) unmarked_context_9_1464_750984 node_context_9_1464_750984
  intro a
  fin_cases a
  · exact context_10_5856_747473
  · exact context_10_5857_748982
  · exact context_10_5858_749973
  · exact context_10_5859_750983

theorem selected_cut_29773 : selected 9 ⟨751051, by decide⟩
    (prefixPartial 12 93760) = some ⟨12, 2, 0, 751051, 93760, 4065, 65536⟩ := by
  decide +kernel

theorem context_12_93760_751051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93760 ⟨751051, by decide⟩ :=
  accepted_of_selected 12 93760 ⟨751051, by decide⟩ ⟨12, 2, 0, 751051, 93760, 4065, 65536⟩
    (by decide) selected_cut_29773

theorem selected_cut_29774 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 93761) = some ⟨12, 1, 0, 170504, 93761, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93761_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93761 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 93761 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 93761, 1, 65536⟩
    (by decide) selected_cut_29774

theorem selected_cut_29775 : selected 9 ⟨751102, by decide⟩
    (prefixPartial 12 93762) = some ⟨12, 2, 0, 751102, 93762, 3585, 65536⟩ := by
  decide +kernel

theorem context_12_93762_751102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93762 ⟨751102, by decide⟩ :=
  accepted_of_selected 12 93762 ⟨751102, by decide⟩ ⟨12, 2, 0, 751102, 93762, 3585, 65536⟩
    (by decide) selected_cut_29775

theorem selected_cut_29776 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 375052) = some ⟨13, 1, 0, 3444, 375052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_375052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 375052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 375052, 1, 16384⟩
    (by decide) selected_cut_29776

theorem selected_cut_29777 : selected 8 ⟨751130, by decide⟩
    (prefixPartial 13 375053) = some ⟨13, 2, 0, 751130, 375053, 2001, 16384⟩ := by
  decide +kernel

theorem context_13_375053_751130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375053 ⟨751130, by decide⟩ :=
  accepted_of_selected 13 375053 ⟨751130, by decide⟩ ⟨13, 2, 0, 751130, 375053, 2001, 16384⟩
    (by decide) selected_cut_29777

theorem selected_cut_29778 : selected 8 ⟨751152, by decide⟩
    (prefixPartial 13 375054) = some ⟨13, 2, 0, 751152, 375054, 1413, 16384⟩ := by
  decide +kernel

theorem context_13_375054_751152 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375054 ⟨751152, by decide⟩ :=
  accepted_of_selected 13 375054 ⟨751152, by decide⟩ ⟨13, 2, 0, 751152, 375054, 1413, 16384⟩
    (by decide) selected_cut_29778

theorem selected_cut_29779 : selected 8 ⟨751163, by decide⟩
    (prefixPartial 13 375055) = some ⟨13, 2, 0, 751163, 375055, 853, 16384⟩ := by
  decide +kernel

theorem context_13_375055_751163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375055 ⟨751163, by decide⟩ :=
  accepted_of_selected 13 375055 ⟨751163, by decide⟩ ⟨13, 2, 0, 751163, 375055, 853, 16384⟩
    (by decide) selected_cut_29779

theorem unmarked_context_12_93763_751164 : frontier 9 ⟨751164, by decide⟩
    (prefixCache 12 93763) (prefixPartial 12 93763) = false := by
  decide +kernel

theorem node_context_12_93763_751164 : EJMOriginalGlobalDAGData.nodes 9 ⟨751164, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨751130, by decide⟩,⟨751152, by decide⟩,⟨751163, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93763_751164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93763 ⟨751164, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93763
    ⟨751164, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨751130, by decide⟩,⟨751152, by decide⟩,⟨751163, by decide⟩]) unmarked_context_12_93763_751164 node_context_12_93763_751164
  intro a
  fin_cases a
  · exact context_13_375052_3444
  · exact context_13_375053_751130
  · exact context_13_375054_751152
  · exact context_13_375055_751163

theorem unmarked_context_11_23440_751165 : frontier 10 ⟨751165, by decide⟩
    (prefixCache 11 23440) (prefixPartial 11 23440) = false := by
  decide +kernel

theorem node_context_11_23440_751165 : EJMOriginalGlobalDAGData.nodes 10 ⟨751165, by decide⟩ =
    .split (coordinate 11) (![⟨751051, by decide⟩,⟨170504, by decide⟩,⟨751102, by decide⟩,⟨751164, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23440_751165 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23440 ⟨751165, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23440
    ⟨751165, by decide⟩ (by decide) (![⟨751051, by decide⟩,⟨170504, by decide⟩,⟨751102, by decide⟩,⟨751164, by decide⟩]) unmarked_context_11_23440_751165 node_context_11_23440_751165
  intro a
  fin_cases a
  · exact context_12_93760_751051
  · exact context_12_93761_170504
  · exact context_12_93762_751102
  · exact context_12_93763_751164

theorem selected_cut_29780 : selected 9 ⟨751220, by decide⟩
    (prefixPartial 12 93764) = some ⟨12, 2, 0, 751220, 93764, 3897, 65536⟩ := by
  decide +kernel

theorem context_12_93764_751220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93764 ⟨751220, by decide⟩ :=
  accepted_of_selected 12 93764 ⟨751220, by decide⟩ ⟨12, 2, 0, 751220, 93764, 3897, 65536⟩
    (by decide) selected_cut_29780

theorem selected_cut_29781 : selected 9 ⟨170504, by decide⟩
    (prefixPartial 12 93765) = some ⟨12, 1, 0, 170504, 93765, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93765_170504 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93765 ⟨170504, by decide⟩ :=
  accepted_of_selected 12 93765 ⟨170504, by decide⟩ ⟨12, 1, 0, 170504, 93765, 1, 65536⟩
    (by decide) selected_cut_29781

theorem selected_cut_29782 : selected 9 ⟨751270, by decide⟩
    (prefixPartial 12 93766) = some ⟨12, 2, 0, 751270, 93766, 3481, 65536⟩ := by
  decide +kernel

theorem context_12_93766_751270 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93766 ⟨751270, by decide⟩ :=
  accepted_of_selected 12 93766 ⟨751270, by decide⟩ ⟨12, 2, 0, 751270, 93766, 3481, 65536⟩
    (by decide) selected_cut_29782

theorem selected_cut_29783 : selected 9 ⟨751322, by decide⟩
    (prefixPartial 12 93767) = some ⟨12, 2, 0, 751322, 93767, 4013, 65536⟩ := by
  decide +kernel

theorem context_12_93767_751322 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93767 ⟨751322, by decide⟩ :=
  accepted_of_selected 12 93767 ⟨751322, by decide⟩ ⟨12, 2, 0, 751322, 93767, 4013, 65536⟩
    (by decide) selected_cut_29783

theorem unmarked_context_11_23441_751323 : frontier 10 ⟨751323, by decide⟩
    (prefixCache 11 23441) (prefixPartial 11 23441) = false := by
  decide +kernel

theorem node_context_11_23441_751323 : EJMOriginalGlobalDAGData.nodes 10 ⟨751323, by decide⟩ =
    .split (coordinate 11) (![⟨751220, by decide⟩,⟨170504, by decide⟩,⟨751270, by decide⟩,⟨751322, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23441_751323 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23441 ⟨751323, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23441
    ⟨751323, by decide⟩ (by decide) (![⟨751220, by decide⟩,⟨170504, by decide⟩,⟨751270, by decide⟩,⟨751322, by decide⟩]) unmarked_context_11_23441_751323 node_context_11_23441_751323
  intro a
  fin_cases a
  · exact context_12_93764_751220
  · exact context_12_93765_170504
  · exact context_12_93766_751270
  · exact context_12_93767_751322

theorem selected_cut_29784 : selected 9 ⟨751371, by decide⟩
    (prefixPartial 12 93768) = some ⟨12, 2, 0, 751371, 93768, 3365, 65536⟩ := by
  decide +kernel

theorem context_12_93768_751371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93768 ⟨751371, by decide⟩ :=
  accepted_of_selected 12 93768 ⟨751371, by decide⟩ ⟨12, 2, 0, 751371, 93768, 3365, 65536⟩
    (by decide) selected_cut_29784

theorem selected_cut_29785 : selected 9 ⟨126371, by decide⟩
    (prefixPartial 12 93769) = some ⟨12, 1, 0, 126371, 93769, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93769_126371 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93769 ⟨126371, by decide⟩ :=
  accepted_of_selected 12 93769 ⟨126371, by decide⟩ ⟨12, 1, 0, 126371, 93769, 1, 65536⟩
    (by decide) selected_cut_29785

theorem selected_cut_29786 : selected 9 ⟨751477, by decide⟩
    (prefixPartial 12 93770) = some ⟨12, 2, 0, 751477, 93770, 3009, 65536⟩ := by
  decide +kernel

theorem context_12_93770_751477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93770 ⟨751477, by decide⟩ :=
  accepted_of_selected 12 93770 ⟨751477, by decide⟩ ⟨12, 2, 0, 751477, 93770, 3009, 65536⟩
    (by decide) selected_cut_29786

theorem selected_cut_29787 : selected 9 ⟨751532, by decide⟩
    (prefixPartial 12 93771) = some ⟨12, 2, 0, 751532, 93771, 3433, 65536⟩ := by
  decide +kernel

theorem context_12_93771_751532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93771 ⟨751532, by decide⟩ :=
  accepted_of_selected 12 93771 ⟨751532, by decide⟩ ⟨12, 2, 0, 751532, 93771, 3433, 65536⟩
    (by decide) selected_cut_29787

theorem unmarked_context_11_23442_751533 : frontier 10 ⟨751533, by decide⟩
    (prefixCache 11 23442) (prefixPartial 11 23442) = false := by
  decide +kernel

theorem node_context_11_23442_751533 : EJMOriginalGlobalDAGData.nodes 10 ⟨751533, by decide⟩ =
    .split (coordinate 11) (![⟨751371, by decide⟩,⟨126371, by decide⟩,⟨751477, by decide⟩,⟨751532, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23442_751533 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23442 ⟨751533, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23442
    ⟨751533, by decide⟩ (by decide) (![⟨751371, by decide⟩,⟨126371, by decide⟩,⟨751477, by decide⟩,⟨751532, by decide⟩]) unmarked_context_11_23442_751533 node_context_11_23442_751533
  intro a
  fin_cases a
  · exact context_12_93768_751371
  · exact context_12_93769_126371
  · exact context_12_93770_751477
  · exact context_12_93771_751532

theorem selected_cut_29788 : selected 9 ⟨751581, by decide⟩
    (prefixPartial 12 93772) = some ⟨12, 2, 0, 751581, 93772, 3309, 65536⟩ := by
  decide +kernel

theorem context_12_93772_751581 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93772 ⟨751581, by decide⟩ :=
  accepted_of_selected 12 93772 ⟨751581, by decide⟩ ⟨12, 2, 0, 751581, 93772, 3309, 65536⟩
    (by decide) selected_cut_29788

theorem selected_cut_29789 : selected 9 ⟨751614, by decide⟩
    (prefixPartial 12 93773) = some ⟨12, 2, 0, 751614, 93773, 1917, 65536⟩ := by
  decide +kernel

theorem context_12_93773_751614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93773 ⟨751614, by decide⟩ :=
  accepted_of_selected 12 93773 ⟨751614, by decide⟩ ⟨12, 2, 0, 751614, 93773, 1917, 65536⟩
    (by decide) selected_cut_29789

theorem selected_cut_29790 : selected 9 ⟨751662, by decide⟩
    (prefixPartial 12 93774) = some ⟨12, 2, 0, 751662, 93774, 3001, 65536⟩ := by
  decide +kernel

theorem context_12_93774_751662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93774 ⟨751662, by decide⟩ :=
  accepted_of_selected 12 93774 ⟨751662, by decide⟩ ⟨12, 2, 0, 751662, 93774, 3001, 65536⟩
    (by decide) selected_cut_29790

theorem selected_cut_29791 : selected 9 ⟨751712, by decide⟩
    (prefixPartial 12 93775) = some ⟨12, 2, 0, 751712, 93775, 3549, 65536⟩ := by
  decide +kernel

theorem context_12_93775_751712 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93775 ⟨751712, by decide⟩ :=
  accepted_of_selected 12 93775 ⟨751712, by decide⟩ ⟨12, 2, 0, 751712, 93775, 3549, 65536⟩
    (by decide) selected_cut_29791

theorem unmarked_context_11_23443_751713 : frontier 10 ⟨751713, by decide⟩
    (prefixCache 11 23443) (prefixPartial 11 23443) = false := by
  decide +kernel

theorem node_context_11_23443_751713 : EJMOriginalGlobalDAGData.nodes 10 ⟨751713, by decide⟩ =
    .split (coordinate 11) (![⟨751581, by decide⟩,⟨751614, by decide⟩,⟨751662, by decide⟩,⟨751712, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23443_751713 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23443 ⟨751713, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23443
    ⟨751713, by decide⟩ (by decide) (![⟨751581, by decide⟩,⟨751614, by decide⟩,⟨751662, by decide⟩,⟨751712, by decide⟩]) unmarked_context_11_23443_751713 node_context_11_23443_751713
  intro a
  fin_cases a
  · exact context_12_93772_751581
  · exact context_12_93773_751614
  · exact context_12_93774_751662
  · exact context_12_93775_751712

theorem unmarked_context_10_5860_751714 : frontier 11 ⟨751714, by decide⟩
    (prefixCache 10 5860) (prefixPartial 10 5860) = false := by
  decide +kernel

theorem node_context_10_5860_751714 : EJMOriginalGlobalDAGData.nodes 11 ⟨751714, by decide⟩ =
    .split (coordinate 10) (![⟨751165, by decide⟩,⟨751323, by decide⟩,⟨751533, by decide⟩,⟨751713, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5860_751714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5860 ⟨751714, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5860
    ⟨751714, by decide⟩ (by decide) (![⟨751165, by decide⟩,⟨751323, by decide⟩,⟨751533, by decide⟩,⟨751713, by decide⟩]) unmarked_context_10_5860_751714 node_context_10_5860_751714
  intro a
  fin_cases a
  · exact context_11_23440_751165
  · exact context_11_23441_751323
  · exact context_11_23442_751533
  · exact context_11_23443_751713

theorem selected_cut_29792 : selected 9 ⟨751761, by decide⟩
    (prefixPartial 12 93776) = some ⟨12, 2, 0, 751761, 93776, 3629, 65536⟩ := by
  decide +kernel

theorem context_12_93776_751761 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93776 ⟨751761, by decide⟩ :=
  accepted_of_selected 12 93776 ⟨751761, by decide⟩ ⟨12, 2, 0, 751761, 93776, 3629, 65536⟩
    (by decide) selected_cut_29792

theorem selected_cut_29793 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93777) = some ⟨12, 1, 0, 642341, 93777, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93777_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93777 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93777 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93777, 1, 65536⟩
    (by decide) selected_cut_29793

theorem selected_cut_29794 : selected 9 ⟨751806, by decide⟩
    (prefixPartial 12 93778) = some ⟨12, 2, 0, 751806, 93778, 3321, 65536⟩ := by
  decide +kernel

theorem context_12_93778_751806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93778 ⟨751806, by decide⟩ :=
  accepted_of_selected 12 93778 ⟨751806, by decide⟩ ⟨12, 2, 0, 751806, 93778, 3321, 65536⟩
    (by decide) selected_cut_29794

theorem selected_cut_29795 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 375116) = some ⟨13, 1, 0, 3444, 375116, 1, 16384⟩ := by
  decide +kernel

theorem context_13_375116_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375116 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 375116 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 375116, 1, 16384⟩
    (by decide) selected_cut_29795

theorem selected_cut_29796 : selected 8 ⟨751831, by decide⟩
    (prefixPartial 13 375117) = some ⟨13, 2, 0, 751831, 375117, 1593, 16384⟩ := by
  decide +kernel

theorem context_13_375117_751831 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375117 ⟨751831, by decide⟩ :=
  accepted_of_selected 13 375117 ⟨751831, by decide⟩ ⟨13, 2, 0, 751831, 375117, 1593, 16384⟩
    (by decide) selected_cut_29796

theorem selected_cut_29797 : selected 8 ⟨751858, by decide⟩
    (prefixPartial 13 375118) = some ⟨13, 2, 0, 751858, 375118, 1697, 16384⟩ := by
  decide +kernel

theorem context_13_375118_751858 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375118 ⟨751858, by decide⟩ :=
  accepted_of_selected 13 375118 ⟨751858, by decide⟩ ⟨13, 2, 0, 751858, 375118, 1697, 16384⟩
    (by decide) selected_cut_29797

theorem selected_cut_29798 : selected 8 ⟨751871, by decide⟩
    (prefixPartial 13 375119) = some ⟨13, 2, 0, 751871, 375119, 941, 16384⟩ := by
  decide +kernel

theorem context_13_375119_751871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375119 ⟨751871, by decide⟩ :=
  accepted_of_selected 13 375119 ⟨751871, by decide⟩ ⟨13, 2, 0, 751871, 375119, 941, 16384⟩
    (by decide) selected_cut_29798

theorem unmarked_context_12_93779_751872 : frontier 9 ⟨751872, by decide⟩
    (prefixCache 12 93779) (prefixPartial 12 93779) = false := by
  decide +kernel

theorem node_context_12_93779_751872 : EJMOriginalGlobalDAGData.nodes 9 ⟨751872, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨751831, by decide⟩,⟨751858, by decide⟩,⟨751871, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93779_751872 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93779 ⟨751872, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93779
    ⟨751872, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨751831, by decide⟩,⟨751858, by decide⟩,⟨751871, by decide⟩]) unmarked_context_12_93779_751872 node_context_12_93779_751872
  intro a
  fin_cases a
  · exact context_13_375116_3444
  · exact context_13_375117_751831
  · exact context_13_375118_751858
  · exact context_13_375119_751871

theorem unmarked_context_11_23444_751873 : frontier 10 ⟨751873, by decide⟩
    (prefixCache 11 23444) (prefixPartial 11 23444) = false := by
  decide +kernel

theorem node_context_11_23444_751873 : EJMOriginalGlobalDAGData.nodes 10 ⟨751873, by decide⟩ =
    .split (coordinate 11) (![⟨751761, by decide⟩,⟨642341, by decide⟩,⟨751806, by decide⟩,⟨751872, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23444_751873 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23444 ⟨751873, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23444
    ⟨751873, by decide⟩ (by decide) (![⟨751761, by decide⟩,⟨642341, by decide⟩,⟨751806, by decide⟩,⟨751872, by decide⟩]) unmarked_context_11_23444_751873 node_context_11_23444_751873
  intro a
  fin_cases a
  · exact context_12_93776_751761
  · exact context_12_93777_642341
  · exact context_12_93778_751806
  · exact context_12_93779_751872

theorem selected_cut_29799 : selected 9 ⟨751921, by decide⟩
    (prefixPartial 12 93780) = some ⟨12, 2, 0, 751921, 93780, 3689, 65536⟩ := by
  decide +kernel

theorem context_12_93780_751921 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93780 ⟨751921, by decide⟩ :=
  accepted_of_selected 12 93780 ⟨751921, by decide⟩ ⟨12, 2, 0, 751921, 93780, 3689, 65536⟩
    (by decide) selected_cut_29799

theorem selected_cut_29800 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93781) = some ⟨12, 1, 0, 642341, 93781, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93781_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93781 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93781 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93781, 1, 65536⟩
    (by decide) selected_cut_29800

theorem selected_cut_29801 : selected 9 ⟨751968, by decide⟩
    (prefixPartial 12 93782) = some ⟨12, 2, 0, 751968, 93782, 3241, 65536⟩ := by
  decide +kernel

theorem context_12_93782_751968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93782 ⟨751968, by decide⟩ :=
  accepted_of_selected 12 93782 ⟨751968, by decide⟩ ⟨12, 2, 0, 751968, 93782, 3241, 65536⟩
    (by decide) selected_cut_29801

theorem selected_cut_29802 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 375132) = some ⟨13, 1, 0, 3444, 375132, 1, 16384⟩ := by
  decide +kernel

theorem context_13_375132_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375132 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 375132 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 375132, 1, 16384⟩
    (by decide) selected_cut_29802

theorem selected_cut_29803 : selected 8 ⟨751988, by decide⟩
    (prefixPartial 13 375133) = some ⟨13, 2, 0, 751988, 375133, 1329, 16384⟩ := by
  decide +kernel

theorem context_13_375133_751988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375133 ⟨751988, by decide⟩ :=
  accepted_of_selected 13 375133 ⟨751988, by decide⟩ ⟨13, 2, 0, 751988, 375133, 1329, 16384⟩
    (by decide) selected_cut_29803

theorem selected_cut_29804 : selected 8 ⟨752013, by decide⟩
    (prefixPartial 13 375134) = some ⟨13, 2, 0, 752013, 375134, 1877, 16384⟩ := by
  decide +kernel

theorem context_13_375134_752013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375134 ⟨752013, by decide⟩ :=
  accepted_of_selected 13 375134 ⟨752013, by decide⟩ ⟨13, 2, 0, 752013, 375134, 1877, 16384⟩
    (by decide) selected_cut_29804

theorem selected_cut_29805 : selected 8 ⟨752020, by decide⟩
    (prefixPartial 13 375135) = some ⟨13, 2, 0, 752020, 375135, 889, 16384⟩ := by
  decide +kernel

theorem context_13_375135_752020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375135 ⟨752020, by decide⟩ :=
  accepted_of_selected 13 375135 ⟨752020, by decide⟩ ⟨13, 2, 0, 752020, 375135, 889, 16384⟩
    (by decide) selected_cut_29805

theorem unmarked_context_12_93783_752021 : frontier 9 ⟨752021, by decide⟩
    (prefixCache 12 93783) (prefixPartial 12 93783) = false := by
  decide +kernel

theorem node_context_12_93783_752021 : EJMOriginalGlobalDAGData.nodes 9 ⟨752021, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨751988, by decide⟩,⟨752013, by decide⟩,⟨752020, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93783_752021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93783 ⟨752021, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93783
    ⟨752021, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨751988, by decide⟩,⟨752013, by decide⟩,⟨752020, by decide⟩]) unmarked_context_12_93783_752021 node_context_12_93783_752021
  intro a
  fin_cases a
  · exact context_13_375132_3444
  · exact context_13_375133_751988
  · exact context_13_375134_752013
  · exact context_13_375135_752020

theorem unmarked_context_11_23445_752022 : frontier 10 ⟨752022, by decide⟩
    (prefixCache 11 23445) (prefixPartial 11 23445) = false := by
  decide +kernel

theorem node_context_11_23445_752022 : EJMOriginalGlobalDAGData.nodes 10 ⟨752022, by decide⟩ =
    .split (coordinate 11) (![⟨751921, by decide⟩,⟨642341, by decide⟩,⟨751968, by decide⟩,⟨752021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23445_752022 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23445 ⟨752022, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23445
    ⟨752022, by decide⟩ (by decide) (![⟨751921, by decide⟩,⟨642341, by decide⟩,⟨751968, by decide⟩,⟨752021, by decide⟩]) unmarked_context_11_23445_752022 node_context_11_23445_752022
  intro a
  fin_cases a
  · exact context_12_93780_751921
  · exact context_12_93781_642341
  · exact context_12_93782_751968
  · exact context_12_93783_752021

theorem selected_cut_29806 : selected 9 ⟨752068, by decide⟩
    (prefixPartial 12 93784) = some ⟨12, 2, 0, 752068, 93784, 2901, 65536⟩ := by
  decide +kernel

theorem context_12_93784_752068 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93784 ⟨752068, by decide⟩ :=
  accepted_of_selected 12 93784 ⟨752068, by decide⟩ ⟨12, 2, 0, 752068, 93784, 2901, 65536⟩
    (by decide) selected_cut_29806

theorem selected_cut_29807 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93785) = some ⟨12, 1, 0, 642341, 93785, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93785_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93785 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93785 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93785, 1, 65536⟩
    (by decide) selected_cut_29807

theorem selected_cut_29808 : selected 9 ⟨290673, by decide⟩
    (prefixPartial 12 93786) = some ⟨12, 1, 0, 290673, 93786, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93786_290673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93786 ⟨290673, by decide⟩ :=
  accepted_of_selected 12 93786 ⟨290673, by decide⟩ ⟨12, 1, 0, 290673, 93786, 1, 65536⟩
    (by decide) selected_cut_29808

theorem selected_cut_29809 : selected 9 ⟨752114, by decide⟩
    (prefixPartial 12 93787) = some ⟨12, 2, 0, 752114, 93787, 3109, 65536⟩ := by
  decide +kernel

theorem context_12_93787_752114 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93787 ⟨752114, by decide⟩ :=
  accepted_of_selected 12 93787 ⟨752114, by decide⟩ ⟨12, 2, 0, 752114, 93787, 3109, 65536⟩
    (by decide) selected_cut_29809

theorem unmarked_context_11_23446_752115 : frontier 10 ⟨752115, by decide⟩
    (prefixCache 11 23446) (prefixPartial 11 23446) = false := by
  decide +kernel

theorem node_context_11_23446_752115 : EJMOriginalGlobalDAGData.nodes 10 ⟨752115, by decide⟩ =
    .split (coordinate 11) (![⟨752068, by decide⟩,⟨642341, by decide⟩,⟨290673, by decide⟩,⟨752114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23446_752115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23446 ⟨752115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23446
    ⟨752115, by decide⟩ (by decide) (![⟨752068, by decide⟩,⟨642341, by decide⟩,⟨290673, by decide⟩,⟨752114, by decide⟩]) unmarked_context_11_23446_752115 node_context_11_23446_752115
  intro a
  fin_cases a
  · exact context_12_93784_752068
  · exact context_12_93785_642341
  · exact context_12_93786_290673
  · exact context_12_93787_752114

theorem selected_cut_29810 : selected 9 ⟨752161, by decide⟩
    (prefixPartial 12 93788) = some ⟨12, 2, 0, 752161, 93788, 3005, 65536⟩ := by
  decide +kernel

theorem context_12_93788_752161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93788 ⟨752161, by decide⟩ :=
  accepted_of_selected 12 93788 ⟨752161, by decide⟩ ⟨12, 2, 0, 752161, 93788, 3005, 65536⟩
    (by decide) selected_cut_29810

theorem selected_cut_29811 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 93789) = some ⟨12, 1, 0, 642341, 93789, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93789_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93789 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 93789 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 93789, 1, 65536⟩
    (by decide) selected_cut_29811

theorem selected_cut_29812 : selected 9 ⟨752202, by decide⟩
    (prefixPartial 12 93790) = some ⟨12, 2, 0, 752202, 93790, 2713, 65536⟩ := by
  decide +kernel

theorem context_12_93790_752202 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93790 ⟨752202, by decide⟩ :=
  accepted_of_selected 12 93790 ⟨752202, by decide⟩ ⟨12, 2, 0, 752202, 93790, 2713, 65536⟩
    (by decide) selected_cut_29812

theorem selected_cut_29813 : selected 9 ⟨752250, by decide⟩
    (prefixPartial 12 93791) = some ⟨12, 2, 0, 752250, 93791, 3357, 65536⟩ := by
  decide +kernel

theorem context_12_93791_752250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93791 ⟨752250, by decide⟩ :=
  accepted_of_selected 12 93791 ⟨752250, by decide⟩ ⟨12, 2, 0, 752250, 93791, 3357, 65536⟩
    (by decide) selected_cut_29813

theorem unmarked_context_11_23447_752251 : frontier 10 ⟨752251, by decide⟩
    (prefixCache 11 23447) (prefixPartial 11 23447) = false := by
  decide +kernel

theorem node_context_11_23447_752251 : EJMOriginalGlobalDAGData.nodes 10 ⟨752251, by decide⟩ =
    .split (coordinate 11) (![⟨752161, by decide⟩,⟨642341, by decide⟩,⟨752202, by decide⟩,⟨752250, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23447_752251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23447 ⟨752251, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23447
    ⟨752251, by decide⟩ (by decide) (![⟨752161, by decide⟩,⟨642341, by decide⟩,⟨752202, by decide⟩,⟨752250, by decide⟩]) unmarked_context_11_23447_752251 node_context_11_23447_752251
  intro a
  fin_cases a
  · exact context_12_93788_752161
  · exact context_12_93789_642341
  · exact context_12_93790_752202
  · exact context_12_93791_752250

theorem unmarked_context_10_5861_752252 : frontier 11 ⟨752252, by decide⟩
    (prefixCache 10 5861) (prefixPartial 10 5861) = false := by
  decide +kernel

theorem node_context_10_5861_752252 : EJMOriginalGlobalDAGData.nodes 11 ⟨752252, by decide⟩ =
    .split (coordinate 10) (![⟨751873, by decide⟩,⟨752022, by decide⟩,⟨752115, by decide⟩,⟨752251, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5861_752252 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5861 ⟨752252, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5861
    ⟨752252, by decide⟩ (by decide) (![⟨751873, by decide⟩,⟨752022, by decide⟩,⟨752115, by decide⟩,⟨752251, by decide⟩]) unmarked_context_10_5861_752252 node_context_10_5861_752252
  intro a
  fin_cases a
  · exact context_11_23444_751873
  · exact context_11_23445_752022
  · exact context_11_23446_752115
  · exact context_11_23447_752251

theorem selected_cut_29814 : selected 9 ⟨752294, by decide⟩
    (prefixPartial 12 93792) = some ⟨12, 2, 0, 752294, 93792, 3029, 65536⟩ := by
  decide +kernel

theorem context_12_93792_752294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93792 ⟨752294, by decide⟩ :=
  accepted_of_selected 12 93792 ⟨752294, by decide⟩ ⟨12, 2, 0, 752294, 93792, 3029, 65536⟩
    (by decide) selected_cut_29814

theorem selected_cut_29815 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 375172) = some ⟨13, 1, 0, 3444, 375172, 1, 16384⟩ := by
  decide +kernel

theorem context_13_375172_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375172 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 375172 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 375172, 1, 16384⟩
    (by decide) selected_cut_29815

theorem selected_cut_29816 : selected 8 ⟨752340, by decide⟩
    (prefixPartial 13 375173) = some ⟨13, 2, 0, 752340, 375173, 1601, 16384⟩ := by
  decide +kernel

theorem context_13_375173_752340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375173 ⟨752340, by decide⟩ :=
  accepted_of_selected 13 375173 ⟨752340, by decide⟩ ⟨13, 2, 0, 752340, 375173, 1601, 16384⟩
    (by decide) selected_cut_29816

theorem selected_cut_29817 : selected 8 ⟨752409, by decide⟩
    (prefixPartial 13 375174) = some ⟨13, 2, 0, 752409, 375174, 2277, 16384⟩ := by
  decide +kernel

theorem context_13_375174_752409 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375174 ⟨752409, by decide⟩ :=
  accepted_of_selected 13 375174 ⟨752409, by decide⟩ ⟨13, 2, 0, 752409, 375174, 2277, 16384⟩
    (by decide) selected_cut_29817

theorem selected_cut_29818 : selected 8 ⟨752425, by decide⟩
    (prefixPartial 13 375175) = some ⟨13, 2, 0, 752425, 375175, 961, 16384⟩ := by
  decide +kernel

theorem context_13_375175_752425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 375175 ⟨752425, by decide⟩ :=
  accepted_of_selected 13 375175 ⟨752425, by decide⟩ ⟨13, 2, 0, 752425, 375175, 961, 16384⟩
    (by decide) selected_cut_29818

theorem unmarked_context_12_93793_752426 : frontier 9 ⟨752426, by decide⟩
    (prefixCache 12 93793) (prefixPartial 12 93793) = false := by
  decide +kernel

theorem node_context_12_93793_752426 : EJMOriginalGlobalDAGData.nodes 9 ⟨752426, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨752340, by decide⟩,⟨752409, by decide⟩,⟨752425, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_93793_752426 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93793 ⟨752426, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 93793
    ⟨752426, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨752340, by decide⟩,⟨752409, by decide⟩,⟨752425, by decide⟩]) unmarked_context_12_93793_752426 node_context_12_93793_752426
  intro a
  fin_cases a
  · exact context_13_375172_3444
  · exact context_13_375173_752340
  · exact context_13_375174_752409
  · exact context_13_375175_752425

theorem selected_cut_29819 : selected 9 ⟨752463, by decide⟩
    (prefixPartial 12 93794) = some ⟨12, 2, 0, 752463, 93794, 2769, 65536⟩ := by
  decide +kernel

theorem context_12_93794_752463 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93794 ⟨752463, by decide⟩ :=
  accepted_of_selected 12 93794 ⟨752463, by decide⟩ ⟨12, 2, 0, 752463, 93794, 2769, 65536⟩
    (by decide) selected_cut_29819

theorem selected_cut_29820 : selected 9 ⟨752509, by decide⟩
    (prefixPartial 12 93795) = some ⟨12, 2, 0, 752509, 93795, 3425, 65536⟩ := by
  decide +kernel

theorem context_12_93795_752509 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93795 ⟨752509, by decide⟩ :=
  accepted_of_selected 12 93795 ⟨752509, by decide⟩ ⟨12, 2, 0, 752509, 93795, 3425, 65536⟩
    (by decide) selected_cut_29820

theorem unmarked_context_11_23448_752510 : frontier 10 ⟨752510, by decide⟩
    (prefixCache 11 23448) (prefixPartial 11 23448) = false := by
  decide +kernel

theorem node_context_11_23448_752510 : EJMOriginalGlobalDAGData.nodes 10 ⟨752510, by decide⟩ =
    .split (coordinate 11) (![⟨752294, by decide⟩,⟨752426, by decide⟩,⟨752463, by decide⟩,⟨752509, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23448_752510 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23448 ⟨752510, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23448
    ⟨752510, by decide⟩ (by decide) (![⟨752294, by decide⟩,⟨752426, by decide⟩,⟨752463, by decide⟩,⟨752509, by decide⟩]) unmarked_context_11_23448_752510 node_context_11_23448_752510
  intro a
  fin_cases a
  · exact context_12_93792_752294
  · exact context_12_93793_752426
  · exact context_12_93794_752463
  · exact context_12_93795_752509

theorem selected_cut_29821 : selected 9 ⟨752558, by decide⟩
    (prefixPartial 12 93796) = some ⟨12, 2, 0, 752558, 93796, 3101, 65536⟩ := by
  decide +kernel

theorem context_12_93796_752558 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93796 ⟨752558, by decide⟩ :=
  accepted_of_selected 12 93796 ⟨752558, by decide⟩ ⟨12, 2, 0, 752558, 93796, 3101, 65536⟩
    (by decide) selected_cut_29821

theorem selected_cut_29822 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 93797) = some ⟨12, 1, 0, 642794, 93797, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93797_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93797 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 93797 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 93797, 1, 65536⟩
    (by decide) selected_cut_29822

theorem selected_cut_29823 : selected 9 ⟨752595, by decide⟩
    (prefixPartial 12 93798) = some ⟨12, 2, 0, 752595, 93798, 2689, 65536⟩ := by
  decide +kernel

theorem context_12_93798_752595 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93798 ⟨752595, by decide⟩ :=
  accepted_of_selected 12 93798 ⟨752595, by decide⟩ ⟨12, 2, 0, 752595, 93798, 2689, 65536⟩
    (by decide) selected_cut_29823

theorem selected_cut_29824 : selected 9 ⟨752638, by decide⟩
    (prefixPartial 12 93799) = some ⟨12, 2, 0, 752638, 93799, 3317, 65536⟩ := by
  decide +kernel

theorem context_12_93799_752638 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93799 ⟨752638, by decide⟩ :=
  accepted_of_selected 12 93799 ⟨752638, by decide⟩ ⟨12, 2, 0, 752638, 93799, 3317, 65536⟩
    (by decide) selected_cut_29824

theorem unmarked_context_11_23449_752639 : frontier 10 ⟨752639, by decide⟩
    (prefixCache 11 23449) (prefixPartial 11 23449) = false := by
  decide +kernel

theorem node_context_11_23449_752639 : EJMOriginalGlobalDAGData.nodes 10 ⟨752639, by decide⟩ =
    .split (coordinate 11) (![⟨752558, by decide⟩,⟨642794, by decide⟩,⟨752595, by decide⟩,⟨752638, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23449_752639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23449 ⟨752639, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23449
    ⟨752639, by decide⟩ (by decide) (![⟨752558, by decide⟩,⟨642794, by decide⟩,⟨752595, by decide⟩,⟨752638, by decide⟩]) unmarked_context_11_23449_752639 node_context_11_23449_752639
  intro a
  fin_cases a
  · exact context_12_93796_752558
  · exact context_12_93797_642794
  · exact context_12_93798_752595
  · exact context_12_93799_752638

theorem selected_cut_29825 : selected 9 ⟨752673, by decide⟩
    (prefixPartial 12 93800) = some ⟨12, 2, 0, 752673, 93800, 2501, 65536⟩ := by
  decide +kernel

theorem context_12_93800_752673 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93800 ⟨752673, by decide⟩ :=
  accepted_of_selected 12 93800 ⟨752673, by decide⟩ ⟨12, 2, 0, 752673, 93800, 2501, 65536⟩
    (by decide) selected_cut_29825

theorem selected_cut_29826 : selected 9 ⟨289098, by decide⟩
    (prefixPartial 12 93801) = some ⟨12, 1, 0, 289098, 93801, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93801_289098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93801 ⟨289098, by decide⟩ :=
  accepted_of_selected 12 93801 ⟨289098, by decide⟩ ⟨12, 1, 0, 289098, 93801, 1, 65536⟩
    (by decide) selected_cut_29826

theorem selected_cut_29827 : selected 9 ⟨445248, by decide⟩
    (prefixPartial 12 93802) = some ⟨12, 1, 0, 445248, 93802, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93802_445248 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93802 ⟨445248, by decide⟩ :=
  accepted_of_selected 12 93802 ⟨445248, by decide⟩ ⟨12, 1, 0, 445248, 93802, 1, 65536⟩
    (by decide) selected_cut_29827

theorem selected_cut_29828 : selected 9 ⟨752708, by decide⟩
    (prefixPartial 12 93803) = some ⟨12, 2, 0, 752708, 93803, 2585, 65536⟩ := by
  decide +kernel

theorem context_12_93803_752708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93803 ⟨752708, by decide⟩ :=
  accepted_of_selected 12 93803 ⟨752708, by decide⟩ ⟨12, 2, 0, 752708, 93803, 2585, 65536⟩
    (by decide) selected_cut_29828

theorem unmarked_context_11_23450_752709 : frontier 10 ⟨752709, by decide⟩
    (prefixCache 11 23450) (prefixPartial 11 23450) = false := by
  decide +kernel

theorem node_context_11_23450_752709 : EJMOriginalGlobalDAGData.nodes 10 ⟨752709, by decide⟩ =
    .split (coordinate 11) (![⟨752673, by decide⟩,⟨289098, by decide⟩,⟨445248, by decide⟩,⟨752708, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23450_752709 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23450 ⟨752709, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23450
    ⟨752709, by decide⟩ (by decide) (![⟨752673, by decide⟩,⟨289098, by decide⟩,⟨445248, by decide⟩,⟨752708, by decide⟩]) unmarked_context_11_23450_752709 node_context_11_23450_752709
  intro a
  fin_cases a
  · exact context_12_93800_752673
  · exact context_12_93801_289098
  · exact context_12_93802_445248
  · exact context_12_93803_752708

theorem selected_cut_29829 : selected 9 ⟨752746, by decide⟩
    (prefixPartial 12 93804) = some ⟨12, 2, 0, 752746, 93804, 2733, 65536⟩ := by
  decide +kernel

theorem context_12_93804_752746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93804 ⟨752746, by decide⟩ :=
  accepted_of_selected 12 93804 ⟨752746, by decide⟩ ⟨12, 2, 0, 752746, 93804, 2733, 65536⟩
    (by decide) selected_cut_29829

theorem selected_cut_29830 : selected 9 ⟨752824, by decide⟩
    (prefixPartial 12 93805) = some ⟨12, 2, 0, 752824, 93805, 4017, 65536⟩ := by
  decide +kernel

theorem context_12_93805_752824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93805 ⟨752824, by decide⟩ :=
  accepted_of_selected 12 93805 ⟨752824, by decide⟩ ⟨12, 2, 0, 752824, 93805, 4017, 65536⟩
    (by decide) selected_cut_29830

theorem selected_cut_29831 : selected 9 ⟨752855, by decide⟩
    (prefixPartial 12 93806) = some ⟨12, 2, 0, 752855, 93806, 2369, 65536⟩ := by
  decide +kernel

theorem context_12_93806_752855 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93806 ⟨752855, by decide⟩ :=
  accepted_of_selected 12 93806 ⟨752855, by decide⟩ ⟨12, 2, 0, 752855, 93806, 2369, 65536⟩
    (by decide) selected_cut_29831

theorem selected_cut_29832 : selected 9 ⟨752889, by decide⟩
    (prefixPartial 12 93807) = some ⟨12, 2, 0, 752889, 93807, 2809, 65536⟩ := by
  decide +kernel

theorem context_12_93807_752889 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93807 ⟨752889, by decide⟩ :=
  accepted_of_selected 12 93807 ⟨752889, by decide⟩ ⟨12, 2, 0, 752889, 93807, 2809, 65536⟩
    (by decide) selected_cut_29832

theorem unmarked_context_11_23451_752890 : frontier 10 ⟨752890, by decide⟩
    (prefixCache 11 23451) (prefixPartial 11 23451) = false := by
  decide +kernel

theorem node_context_11_23451_752890 : EJMOriginalGlobalDAGData.nodes 10 ⟨752890, by decide⟩ =
    .split (coordinate 11) (![⟨752746, by decide⟩,⟨752824, by decide⟩,⟨752855, by decide⟩,⟨752889, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23451_752890 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23451 ⟨752890, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23451
    ⟨752890, by decide⟩ (by decide) (![⟨752746, by decide⟩,⟨752824, by decide⟩,⟨752855, by decide⟩,⟨752889, by decide⟩]) unmarked_context_11_23451_752890 node_context_11_23451_752890
  intro a
  fin_cases a
  · exact context_12_93804_752746
  · exact context_12_93805_752824
  · exact context_12_93806_752855
  · exact context_12_93807_752889

theorem unmarked_context_10_5862_752891 : frontier 11 ⟨752891, by decide⟩
    (prefixCache 10 5862) (prefixPartial 10 5862) = false := by
  decide +kernel

theorem node_context_10_5862_752891 : EJMOriginalGlobalDAGData.nodes 11 ⟨752891, by decide⟩ =
    .split (coordinate 10) (![⟨752510, by decide⟩,⟨752639, by decide⟩,⟨752709, by decide⟩,⟨752890, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5862_752891 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5862 ⟨752891, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5862
    ⟨752891, by decide⟩ (by decide) (![⟨752510, by decide⟩,⟨752639, by decide⟩,⟨752709, by decide⟩,⟨752890, by decide⟩]) unmarked_context_10_5862_752891 node_context_10_5862_752891
  intro a
  fin_cases a
  · exact context_11_23448_752510
  · exact context_11_23449_752639
  · exact context_11_23450_752709
  · exact context_11_23451_752890

theorem selected_cut_29833 : selected 9 ⟨752926, by decide⟩
    (prefixPartial 12 93808) = some ⟨12, 2, 0, 752926, 93808, 2613, 65536⟩ := by
  decide +kernel

theorem context_12_93808_752926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93808 ⟨752926, by decide⟩ :=
  accepted_of_selected 12 93808 ⟨752926, by decide⟩ ⟨12, 2, 0, 752926, 93808, 2613, 65536⟩
    (by decide) selected_cut_29833

theorem selected_cut_29834 : selected 9 ⟨752986, by decide⟩
    (prefixPartial 12 93809) = some ⟨12, 2, 0, 752986, 93809, 3793, 65536⟩ := by
  decide +kernel

theorem context_12_93809_752986 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93809 ⟨752986, by decide⟩ :=
  accepted_of_selected 12 93809 ⟨752986, by decide⟩ ⟨12, 2, 0, 752986, 93809, 3793, 65536⟩
    (by decide) selected_cut_29834

theorem selected_cut_29835 : selected 9 ⟨753020, by decide⟩
    (prefixPartial 12 93810) = some ⟨12, 2, 0, 753020, 93810, 2289, 65536⟩ := by
  decide +kernel

theorem context_12_93810_753020 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93810 ⟨753020, by decide⟩ :=
  accepted_of_selected 12 93810 ⟨753020, by decide⟩ ⟨12, 2, 0, 753020, 93810, 2289, 65536⟩
    (by decide) selected_cut_29835

theorem selected_cut_29836 : selected 9 ⟨753054, by decide⟩
    (prefixPartial 12 93811) = some ⟨12, 2, 0, 753054, 93811, 2853, 65536⟩ := by
  decide +kernel

theorem context_12_93811_753054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93811 ⟨753054, by decide⟩ :=
  accepted_of_selected 12 93811 ⟨753054, by decide⟩ ⟨12, 2, 0, 753054, 93811, 2853, 65536⟩
    (by decide) selected_cut_29836

theorem unmarked_context_11_23452_753055 : frontier 10 ⟨753055, by decide⟩
    (prefixCache 11 23452) (prefixPartial 11 23452) = false := by
  decide +kernel

theorem node_context_11_23452_753055 : EJMOriginalGlobalDAGData.nodes 10 ⟨753055, by decide⟩ =
    .split (coordinate 11) (![⟨752926, by decide⟩,⟨752986, by decide⟩,⟨753020, by decide⟩,⟨753054, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23452_753055 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23452 ⟨753055, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23452
    ⟨753055, by decide⟩ (by decide) (![⟨752926, by decide⟩,⟨752986, by decide⟩,⟨753020, by decide⟩,⟨753054, by decide⟩]) unmarked_context_11_23452_753055 node_context_11_23452_753055
  intro a
  fin_cases a
  · exact context_12_93808_752926
  · exact context_12_93809_752986
  · exact context_12_93810_753020
  · exact context_12_93811_753054

theorem selected_cut_29837 : selected 9 ⟨753087, by decide⟩
    (prefixPartial 12 93812) = some ⟨12, 2, 0, 753087, 93812, 2373, 65536⟩ := by
  decide +kernel

theorem context_12_93812_753087 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93812 ⟨753087, by decide⟩ :=
  accepted_of_selected 12 93812 ⟨753087, by decide⟩ ⟨12, 2, 0, 753087, 93812, 2373, 65536⟩
    (by decide) selected_cut_29837

theorem selected_cut_29838 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 93813) = some ⟨12, 1, 0, 642794, 93813, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93813_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93813 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 93813 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 93813, 1, 65536⟩
    (by decide) selected_cut_29838

theorem selected_cut_29839 : selected 9 ⟨753118, by decide⟩
    (prefixPartial 12 93814) = some ⟨12, 2, 0, 753118, 93814, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_93814_753118 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93814 ⟨753118, by decide⟩ :=
  accepted_of_selected 12 93814 ⟨753118, by decide⟩ ⟨12, 2, 0, 753118, 93814, 2193, 65536⟩
    (by decide) selected_cut_29839

theorem selected_cut_29840 : selected 9 ⟨753153, by decide⟩
    (prefixPartial 12 93815) = some ⟨12, 2, 0, 753153, 93815, 2825, 65536⟩ := by
  decide +kernel

theorem context_12_93815_753153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93815 ⟨753153, by decide⟩ :=
  accepted_of_selected 12 93815 ⟨753153, by decide⟩ ⟨12, 2, 0, 753153, 93815, 2825, 65536⟩
    (by decide) selected_cut_29840

theorem unmarked_context_11_23453_753154 : frontier 10 ⟨753154, by decide⟩
    (prefixCache 11 23453) (prefixPartial 11 23453) = false := by
  decide +kernel

theorem node_context_11_23453_753154 : EJMOriginalGlobalDAGData.nodes 10 ⟨753154, by decide⟩ =
    .split (coordinate 11) (![⟨753087, by decide⟩,⟨642794, by decide⟩,⟨753118, by decide⟩,⟨753153, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23453_753154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23453 ⟨753154, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23453
    ⟨753154, by decide⟩ (by decide) (![⟨753087, by decide⟩,⟨642794, by decide⟩,⟨753118, by decide⟩,⟨753153, by decide⟩]) unmarked_context_11_23453_753154 node_context_11_23453_753154
  intro a
  fin_cases a
  · exact context_12_93812_753087
  · exact context_12_93813_642794
  · exact context_12_93814_753118
  · exact context_12_93815_753153

theorem selected_cut_29841 : selected 9 ⟨753186, by decide⟩
    (prefixPartial 12 93816) = some ⟨12, 2, 0, 753186, 93816, 2033, 65536⟩ := by
  decide +kernel

theorem context_12_93816_753186 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93816 ⟨753186, by decide⟩ :=
  accepted_of_selected 12 93816 ⟨753186, by decide⟩ ⟨12, 2, 0, 753186, 93816, 2033, 65536⟩
    (by decide) selected_cut_29841

theorem selected_cut_29842 : selected 9 ⟨753187, by decide⟩
    (prefixPartial 12 93817) = some ⟨12, 1, 0, 753187, 93817, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93817_753187 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93817 ⟨753187, by decide⟩ :=
  accepted_of_selected 12 93817 ⟨753187, by decide⟩ ⟨12, 1, 0, 753187, 93817, 1, 65536⟩
    (by decide) selected_cut_29842

theorem selected_cut_29843 : selected 9 ⟨419292, by decide⟩
    (prefixPartial 12 93818) = some ⟨12, 1, 0, 419292, 93818, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93818_419292 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93818 ⟨419292, by decide⟩ :=
  accepted_of_selected 12 93818 ⟨419292, by decide⟩ ⟨12, 1, 0, 419292, 93818, 1, 65536⟩
    (by decide) selected_cut_29843

theorem selected_cut_29844 : selected 9 ⟨753220, by decide⟩
    (prefixPartial 12 93819) = some ⟨12, 2, 0, 753220, 93819, 2237, 65536⟩ := by
  decide +kernel

theorem context_12_93819_753220 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93819 ⟨753220, by decide⟩ :=
  accepted_of_selected 12 93819 ⟨753220, by decide⟩ ⟨12, 2, 0, 753220, 93819, 2237, 65536⟩
    (by decide) selected_cut_29844

theorem unmarked_context_11_23454_753221 : frontier 10 ⟨753221, by decide⟩
    (prefixCache 11 23454) (prefixPartial 11 23454) = false := by
  decide +kernel

theorem node_context_11_23454_753221 : EJMOriginalGlobalDAGData.nodes 10 ⟨753221, by decide⟩ =
    .split (coordinate 11) (![⟨753186, by decide⟩,⟨753187, by decide⟩,⟨419292, by decide⟩,⟨753220, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23454_753221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23454 ⟨753221, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23454
    ⟨753221, by decide⟩ (by decide) (![⟨753186, by decide⟩,⟨753187, by decide⟩,⟨419292, by decide⟩,⟨753220, by decide⟩]) unmarked_context_11_23454_753221 node_context_11_23454_753221
  intro a
  fin_cases a
  · exact context_12_93816_753186
  · exact context_12_93817_753187
  · exact context_12_93818_419292
  · exact context_12_93819_753220

theorem selected_cut_29845 : selected 9 ⟨753266, by decide⟩
    (prefixPartial 12 93820) = some ⟨12, 2, 0, 753266, 93820, 2765, 65536⟩ := by
  decide +kernel

theorem context_12_93820_753266 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93820 ⟨753266, by decide⟩ :=
  accepted_of_selected 12 93820 ⟨753266, by decide⟩ ⟨12, 2, 0, 753266, 93820, 2765, 65536⟩
    (by decide) selected_cut_29845

theorem selected_cut_29846 : selected 9 ⟨753356, by decide⟩
    (prefixPartial 12 93821) = some ⟨12, 2, 0, 753356, 93821, 4077, 65536⟩ := by
  decide +kernel

theorem context_12_93821_753356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93821 ⟨753356, by decide⟩ :=
  accepted_of_selected 12 93821 ⟨753356, by decide⟩ ⟨12, 2, 0, 753356, 93821, 4077, 65536⟩
    (by decide) selected_cut_29846

theorem selected_cut_29847 : selected 9 ⟨753414, by decide⟩
    (prefixPartial 12 93822) = some ⟨12, 2, 0, 753414, 93822, 949, 65536⟩ := by
  decide +kernel

theorem context_12_93822_753414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93822 ⟨753414, by decide⟩ :=
  accepted_of_selected 12 93822 ⟨753414, by decide⟩ ⟨12, 2, 0, 753414, 93822, 949, 65536⟩
    (by decide) selected_cut_29847

theorem selected_cut_29848 : selected 9 ⟨607719, by decide⟩
    (prefixPartial 12 93823) = some ⟨12, 1, 0, 607719, 93823, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93823_607719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93823 ⟨607719, by decide⟩ :=
  accepted_of_selected 12 93823 ⟨607719, by decide⟩ ⟨12, 1, 0, 607719, 93823, 1, 65536⟩
    (by decide) selected_cut_29848

theorem unmarked_context_11_23455_753415 : frontier 10 ⟨753415, by decide⟩
    (prefixCache 11 23455) (prefixPartial 11 23455) = false := by
  decide +kernel

theorem node_context_11_23455_753415 : EJMOriginalGlobalDAGData.nodes 10 ⟨753415, by decide⟩ =
    .split (coordinate 11) (![⟨753266, by decide⟩,⟨753356, by decide⟩,⟨753414, by decide⟩,⟨607719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23455_753415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23455 ⟨753415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23455
    ⟨753415, by decide⟩ (by decide) (![⟨753266, by decide⟩,⟨753356, by decide⟩,⟨753414, by decide⟩,⟨607719, by decide⟩]) unmarked_context_11_23455_753415 node_context_11_23455_753415
  intro a
  fin_cases a
  · exact context_12_93820_753266
  · exact context_12_93821_753356
  · exact context_12_93822_753414
  · exact context_12_93823_607719

theorem unmarked_context_10_5863_753416 : frontier 11 ⟨753416, by decide⟩
    (prefixCache 10 5863) (prefixPartial 10 5863) = false := by
  decide +kernel

theorem node_context_10_5863_753416 : EJMOriginalGlobalDAGData.nodes 11 ⟨753416, by decide⟩ =
    .split (coordinate 10) (![⟨753055, by decide⟩,⟨753154, by decide⟩,⟨753221, by decide⟩,⟨753415, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_5863_753416 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 5863 ⟨753416, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 5863
    ⟨753416, by decide⟩ (by decide) (![⟨753055, by decide⟩,⟨753154, by decide⟩,⟨753221, by decide⟩,⟨753415, by decide⟩]) unmarked_context_10_5863_753416 node_context_10_5863_753416
  intro a
  fin_cases a
  · exact context_11_23452_753055
  · exact context_11_23453_753154
  · exact context_11_23454_753221
  · exact context_11_23455_753415

theorem unmarked_context_9_1465_753417 : frontier 12 ⟨753417, by decide⟩
    (prefixCache 9 1465) (prefixPartial 9 1465) = false := by
  decide +kernel

theorem node_context_9_1465_753417 : EJMOriginalGlobalDAGData.nodes 12 ⟨753417, by decide⟩ =
    .split (coordinate 9) (![⟨751714, by decide⟩,⟨752252, by decide⟩,⟨752891, by decide⟩,⟨753416, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_1465_753417 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 1465 ⟨753417, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 1465
    ⟨753417, by decide⟩ (by decide) (![⟨751714, by decide⟩,⟨752252, by decide⟩,⟨752891, by decide⟩,⟨753416, by decide⟩]) unmarked_context_9_1465_753417 node_context_9_1465_753417
  intro a
  fin_cases a
  · exact context_10_5860_751714
  · exact context_10_5861_752252
  · exact context_10_5862_752891
  · exact context_10_5863_753416

theorem selected_cut_29849 : selected 9 ⟨753446, by decide⟩
    (prefixPartial 12 93824) = some ⟨12, 2, 0, 753446, 93824, 2145, 65536⟩ := by
  decide +kernel

theorem context_12_93824_753446 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93824 ⟨753446, by decide⟩ :=
  accepted_of_selected 12 93824 ⟨753446, by decide⟩ ⟨12, 2, 0, 753446, 93824, 2145, 65536⟩
    (by decide) selected_cut_29849

theorem selected_cut_29850 : selected 9 ⟨753471, by decide⟩
    (prefixPartial 12 93825) = some ⟨12, 2, 0, 753471, 93825, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_93825_753471 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93825 ⟨753471, by decide⟩ :=
  accepted_of_selected 12 93825 ⟨753471, by decide⟩ ⟨12, 2, 0, 753471, 93825, 2105, 65536⟩
    (by decide) selected_cut_29850

theorem selected_cut_29851 : selected 9 ⟨753500, by decide⟩
    (prefixPartial 12 93826) = some ⟨12, 2, 0, 753500, 93826, 2105, 65536⟩ := by
  decide +kernel

theorem context_12_93826_753500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93826 ⟨753500, by decide⟩ :=
  accepted_of_selected 12 93826 ⟨753500, by decide⟩ ⟨12, 2, 0, 753500, 93826, 2105, 65536⟩
    (by decide) selected_cut_29851

theorem selected_cut_29852 : selected 9 ⟨753534, by decide⟩
    (prefixPartial 12 93827) = some ⟨12, 2, 0, 753534, 93827, 2397, 65536⟩ := by
  decide +kernel

theorem context_12_93827_753534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93827 ⟨753534, by decide⟩ :=
  accepted_of_selected 12 93827 ⟨753534, by decide⟩ ⟨12, 2, 0, 753534, 93827, 2397, 65536⟩
    (by decide) selected_cut_29852

theorem unmarked_context_11_23456_753535 : frontier 10 ⟨753535, by decide⟩
    (prefixCache 11 23456) (prefixPartial 11 23456) = false := by
  decide +kernel

theorem node_context_11_23456_753535 : EJMOriginalGlobalDAGData.nodes 10 ⟨753535, by decide⟩ =
    .split (coordinate 11) (![⟨753446, by decide⟩,⟨753471, by decide⟩,⟨753500, by decide⟩,⟨753534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23456_753535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23456 ⟨753535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23456
    ⟨753535, by decide⟩ (by decide) (![⟨753446, by decide⟩,⟨753471, by decide⟩,⟨753500, by decide⟩,⟨753534, by decide⟩]) unmarked_context_11_23456_753535 node_context_11_23456_753535
  intro a
  fin_cases a
  · exact context_12_93824_753446
  · exact context_12_93825_753471
  · exact context_12_93826_753500
  · exact context_12_93827_753534

theorem selected_cut_29853 : selected 9 ⟨753562, by decide⟩
    (prefixPartial 12 93828) = some ⟨12, 2, 0, 753562, 93828, 2213, 65536⟩ := by
  decide +kernel

theorem context_12_93828_753562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93828 ⟨753562, by decide⟩ :=
  accepted_of_selected 12 93828 ⟨753562, by decide⟩ ⟨12, 2, 0, 753562, 93828, 2213, 65536⟩
    (by decide) selected_cut_29853

theorem selected_cut_29854 : selected 9 ⟨753584, by decide⟩
    (prefixPartial 12 93829) = some ⟨12, 2, 0, 753584, 93829, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_93829_753584 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93829 ⟨753584, by decide⟩ :=
  accepted_of_selected 12 93829 ⟨753584, by decide⟩ ⟨12, 2, 0, 753584, 93829, 1985, 65536⟩
    (by decide) selected_cut_29854

theorem selected_cut_29855 : selected 9 ⟨753607, by decide⟩
    (prefixPartial 12 93830) = some ⟨12, 2, 0, 753607, 93830, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_93830_753607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93830 ⟨753607, by decide⟩ :=
  accepted_of_selected 12 93830 ⟨753607, by decide⟩ ⟨12, 2, 0, 753607, 93830, 2073, 65536⟩
    (by decide) selected_cut_29855

theorem selected_cut_29856 : selected 9 ⟨753636, by decide⟩
    (prefixPartial 12 93831) = some ⟨12, 2, 0, 753636, 93831, 2421, 65536⟩ := by
  decide +kernel

theorem context_12_93831_753636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93831 ⟨753636, by decide⟩ :=
  accepted_of_selected 12 93831 ⟨753636, by decide⟩ ⟨12, 2, 0, 753636, 93831, 2421, 65536⟩
    (by decide) selected_cut_29856

theorem unmarked_context_11_23457_753637 : frontier 10 ⟨753637, by decide⟩
    (prefixCache 11 23457) (prefixPartial 11 23457) = false := by
  decide +kernel

theorem node_context_11_23457_753637 : EJMOriginalGlobalDAGData.nodes 10 ⟨753637, by decide⟩ =
    .split (coordinate 11) (![⟨753562, by decide⟩,⟨753584, by decide⟩,⟨753607, by decide⟩,⟨753636, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_23457_753637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 23457 ⟨753637, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 23457
    ⟨753637, by decide⟩ (by decide) (![⟨753562, by decide⟩,⟨753584, by decide⟩,⟨753607, by decide⟩,⟨753636, by decide⟩]) unmarked_context_11_23457_753637 node_context_11_23457_753637
  intro a
  fin_cases a
  · exact context_12_93828_753562
  · exact context_12_93829_753584
  · exact context_12_93830_753607
  · exact context_12_93831_753636

theorem selected_cut_29857 : selected 9 ⟨753663, by decide⟩
    (prefixPartial 12 93832) = some ⟨12, 2, 0, 753663, 93832, 2225, 65536⟩ := by
  decide +kernel

theorem context_12_93832_753663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93832 ⟨753663, by decide⟩ :=
  accepted_of_selected 12 93832 ⟨753663, by decide⟩ ⟨12, 2, 0, 753663, 93832, 2225, 65536⟩
    (by decide) selected_cut_29857

theorem selected_cut_29858 : selected 9 ⟨753689, by decide⟩
    (prefixPartial 12 93833) = some ⟨12, 2, 0, 753689, 93833, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_93833_753689 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93833 ⟨753689, by decide⟩ :=
  accepted_of_selected 12 93833 ⟨753689, by decide⟩ ⟨12, 2, 0, 753689, 93833, 2201, 65536⟩
    (by decide) selected_cut_29858

theorem selected_cut_29859 : selected 9 ⟨448662, by decide⟩
    (prefixPartial 12 93834) = some ⟨12, 1, 0, 448662, 93834, 1, 65536⟩ := by
  decide +kernel

theorem context_12_93834_448662 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 93834 ⟨448662, by decide⟩ :=
  accepted_of_selected 12 93834 ⟨448662, by decide⟩ ⟨12, 1, 0, 448662, 93834, 1, 65536⟩
    (by decide) selected_cut_29859

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
