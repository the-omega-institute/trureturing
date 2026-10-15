/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover049
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_12_18747_153115 : frontier 9 ⟨153115, by decide⟩
    (prefixCache 12 18747) (prefixPartial 12 18747) = false := by
  decide +kernel

theorem node_context_12_18747_153115 : EJMOriginalGlobalDAGData.nodes 9 ⟨153115, by decide⟩ =
    .split (coordinate 12) (![⟨153036, by decide⟩,⟨153076, by decide⟩,⟨153107, by decide⟩,⟨153114, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18747_153115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18747 ⟨153115, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18747
    ⟨153115, by decide⟩ (by decide) (![⟨153036, by decide⟩,⟨153076, by decide⟩,⟨153107, by decide⟩,⟨153114, by decide⟩]) unmarked_context_12_18747_153115 node_context_12_18747_153115
  intro a
  fin_cases a
  · exact context_13_74988_153036
  · exact context_13_74989_153076
  · exact context_13_74990_153107
  · exact context_13_74991_153114

theorem unmarked_context_11_4686_153116 : frontier 10 ⟨153116, by decide⟩
    (prefixCache 11 4686) (prefixPartial 11 4686) = false := by
  decide +kernel

theorem node_context_11_4686_153116 : EJMOriginalGlobalDAGData.nodes 10 ⟨153116, by decide⟩ =
    .split (coordinate 11) (![⟨152883, by decide⟩,⟨152954, by decide⟩,⟨153029, by decide⟩,⟨153115, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4686_153116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4686 ⟨153116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4686
    ⟨153116, by decide⟩ (by decide) (![⟨152883, by decide⟩,⟨152954, by decide⟩,⟨153029, by decide⟩,⟨153115, by decide⟩]) unmarked_context_11_4686_153116 node_context_11_4686_153116
  intro a
  fin_cases a
  · exact context_12_18744_152883
  · exact context_12_18745_152954
  · exact context_12_18746_153029
  · exact context_12_18747_153115

theorem selected_cut_04804 : selected 8 ⟨153119, by decide⟩
    (prefixPartial 13 74992) = some ⟨13, 2, 0, 153119, 74992, 129, 16384⟩ := by
  decide +kernel

theorem context_13_74992_153119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74992 ⟨153119, by decide⟩ :=
  accepted_of_selected 13 74992 ⟨153119, by decide⟩ ⟨13, 2, 0, 153119, 74992, 129, 16384⟩
    (by decide) selected_cut_04804

theorem selected_cut_04805 : selected 8 ⟨153143, by decide⟩
    (prefixPartial 13 74993) = some ⟨13, 2, 0, 153143, 74993, 2877, 16384⟩ := by
  decide +kernel

theorem context_13_74993_153143 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74993 ⟨153143, by decide⟩ :=
  accepted_of_selected 13 74993 ⟨153143, by decide⟩ ⟨13, 2, 0, 153143, 74993, 2877, 16384⟩
    (by decide) selected_cut_04805

theorem selected_cut_04806 : selected 8 ⟨153164, by decide⟩
    (prefixPartial 13 74994) = some ⟨13, 2, 0, 153164, 74994, 1633, 16384⟩ := by
  decide +kernel

theorem context_13_74994_153164 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74994 ⟨153164, by decide⟩ :=
  accepted_of_selected 13 74994 ⟨153164, by decide⟩ ⟨13, 2, 0, 153164, 74994, 1633, 16384⟩
    (by decide) selected_cut_04806

theorem selected_cut_04807 : selected 8 ⟨153171, by decide⟩
    (prefixPartial 13 74995) = some ⟨13, 2, 0, 153171, 74995, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_74995_153171 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74995 ⟨153171, by decide⟩ :=
  accepted_of_selected 13 74995 ⟨153171, by decide⟩ ⟨13, 2, 0, 153171, 74995, 1021, 16384⟩
    (by decide) selected_cut_04807

theorem unmarked_context_12_18748_153172 : frontier 9 ⟨153172, by decide⟩
    (prefixCache 12 18748) (prefixPartial 12 18748) = false := by
  decide +kernel

theorem node_context_12_18748_153172 : EJMOriginalGlobalDAGData.nodes 9 ⟨153172, by decide⟩ =
    .split (coordinate 12) (![⟨153119, by decide⟩,⟨153143, by decide⟩,⟨153164, by decide⟩,⟨153171, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18748_153172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18748 ⟨153172, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18748
    ⟨153172, by decide⟩ (by decide) (![⟨153119, by decide⟩,⟨153143, by decide⟩,⟨153164, by decide⟩,⟨153171, by decide⟩]) unmarked_context_12_18748_153172 node_context_12_18748_153172
  intro a
  fin_cases a
  · exact context_13_74992_153119
  · exact context_13_74993_153143
  · exact context_13_74994_153164
  · exact context_13_74995_153171

theorem selected_cut_04808 : selected 8 ⟨153176, by decide⟩
    (prefixPartial 13 74996) = some ⟨13, 2, 0, 153176, 74996, 113, 16384⟩ := by
  decide +kernel

theorem context_13_74996_153176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74996 ⟨153176, by decide⟩ :=
  accepted_of_selected 13 74996 ⟨153176, by decide⟩ ⟨13, 2, 0, 153176, 74996, 113, 16384⟩
    (by decide) selected_cut_04808

theorem selected_cut_04809 : selected 8 ⟨153211, by decide⟩
    (prefixPartial 13 74997) = some ⟨13, 2, 0, 153211, 74997, 2285, 16384⟩ := by
  decide +kernel

theorem context_13_74997_153211 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74997 ⟨153211, by decide⟩ :=
  accepted_of_selected 13 74997 ⟨153211, by decide⟩ ⟨13, 2, 0, 153211, 74997, 2285, 16384⟩
    (by decide) selected_cut_04809

theorem selected_cut_04810 : selected 8 ⟨153233, by decide⟩
    (prefixPartial 13 74998) = some ⟨13, 2, 0, 153233, 74998, 1781, 16384⟩ := by
  decide +kernel

theorem context_13_74998_153233 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74998 ⟨153233, by decide⟩ :=
  accepted_of_selected 13 74998 ⟨153233, by decide⟩ ⟨13, 2, 0, 153233, 74998, 1781, 16384⟩
    (by decide) selected_cut_04810

theorem selected_cut_04811 : selected 8 ⟨153245, by decide⟩
    (prefixPartial 13 74999) = some ⟨13, 2, 0, 153245, 74999, 905, 16384⟩ := by
  decide +kernel

theorem context_13_74999_153245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 74999 ⟨153245, by decide⟩ :=
  accepted_of_selected 13 74999 ⟨153245, by decide⟩ ⟨13, 2, 0, 153245, 74999, 905, 16384⟩
    (by decide) selected_cut_04811

theorem unmarked_context_12_18749_153246 : frontier 9 ⟨153246, by decide⟩
    (prefixCache 12 18749) (prefixPartial 12 18749) = false := by
  decide +kernel

theorem node_context_12_18749_153246 : EJMOriginalGlobalDAGData.nodes 9 ⟨153246, by decide⟩ =
    .split (coordinate 12) (![⟨153176, by decide⟩,⟨153211, by decide⟩,⟨153233, by decide⟩,⟨153245, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18749_153246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18749 ⟨153246, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18749
    ⟨153246, by decide⟩ (by decide) (![⟨153176, by decide⟩,⟨153211, by decide⟩,⟨153233, by decide⟩,⟨153245, by decide⟩]) unmarked_context_12_18749_153246 node_context_12_18749_153246
  intro a
  fin_cases a
  · exact context_13_74996_153176
  · exact context_13_74997_153211
  · exact context_13_74998_153233
  · exact context_13_74999_153245

theorem selected_cut_04812 : selected 8 ⟨153250, by decide⟩
    (prefixPartial 13 75000) = some ⟨13, 2, 0, 153250, 75000, 101, 16384⟩ := by
  decide +kernel

theorem context_13_75000_153250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75000 ⟨153250, by decide⟩ :=
  accepted_of_selected 13 75000 ⟨153250, by decide⟩ ⟨13, 2, 0, 153250, 75000, 101, 16384⟩
    (by decide) selected_cut_04812

theorem selected_cut_04813 : selected 8 ⟨153279, by decide⟩
    (prefixPartial 13 75001) = some ⟨13, 2, 0, 153279, 75001, 2953, 16384⟩ := by
  decide +kernel

theorem context_13_75001_153279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75001 ⟨153279, by decide⟩ :=
  accepted_of_selected 13 75001 ⟨153279, by decide⟩ ⟨13, 2, 0, 153279, 75001, 2953, 16384⟩
    (by decide) selected_cut_04813

theorem selected_cut_04814 : selected 8 ⟨153301, by decide⟩
    (prefixPartial 13 75002) = some ⟨13, 2, 0, 153301, 75002, 1957, 16384⟩ := by
  decide +kernel

theorem context_13_75002_153301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75002 ⟨153301, by decide⟩ :=
  accepted_of_selected 13 75002 ⟨153301, by decide⟩ ⟨13, 2, 0, 153301, 75002, 1957, 16384⟩
    (by decide) selected_cut_04814

theorem selected_cut_04815 : selected 8 ⟨153308, by decide⟩
    (prefixPartial 13 75003) = some ⟨13, 2, 0, 153308, 75003, 1021, 16384⟩ := by
  decide +kernel

theorem context_13_75003_153308 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75003 ⟨153308, by decide⟩ :=
  accepted_of_selected 13 75003 ⟨153308, by decide⟩ ⟨13, 2, 0, 153308, 75003, 1021, 16384⟩
    (by decide) selected_cut_04815

theorem unmarked_context_12_18750_153309 : frontier 9 ⟨153309, by decide⟩
    (prefixCache 12 18750) (prefixPartial 12 18750) = false := by
  decide +kernel

theorem node_context_12_18750_153309 : EJMOriginalGlobalDAGData.nodes 9 ⟨153309, by decide⟩ =
    .split (coordinate 12) (![⟨153250, by decide⟩,⟨153279, by decide⟩,⟨153301, by decide⟩,⟨153308, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18750_153309 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18750 ⟨153309, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18750
    ⟨153309, by decide⟩ (by decide) (![⟨153250, by decide⟩,⟨153279, by decide⟩,⟨153301, by decide⟩,⟨153308, by decide⟩]) unmarked_context_12_18750_153309 node_context_12_18750_153309
  intro a
  fin_cases a
  · exact context_13_75000_153250
  · exact context_13_75001_153279
  · exact context_13_75002_153301
  · exact context_13_75003_153308

theorem selected_cut_04816 : selected 8 ⟨153313, by decide⟩
    (prefixPartial 13 75004) = some ⟨13, 2, 0, 153313, 75004, 65, 16384⟩ := by
  decide +kernel

theorem context_13_75004_153313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75004 ⟨153313, by decide⟩ :=
  accepted_of_selected 13 75004 ⟨153313, by decide⟩ ⟨13, 2, 0, 153313, 75004, 65, 16384⟩
    (by decide) selected_cut_04816

theorem selected_cut_04817 : selected 8 ⟨153343, by decide⟩
    (prefixPartial 13 75005) = some ⟨13, 2, 0, 153343, 75005, 2613, 16384⟩ := by
  decide +kernel

theorem context_13_75005_153343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75005 ⟨153343, by decide⟩ :=
  accepted_of_selected 13 75005 ⟨153343, by decide⟩ ⟨13, 2, 0, 153343, 75005, 2613, 16384⟩
    (by decide) selected_cut_04817

theorem selected_cut_04818 : selected 8 ⟨153366, by decide⟩
    (prefixPartial 13 75006) = some ⟨13, 2, 0, 153366, 75006, 1737, 16384⟩ := by
  decide +kernel

theorem context_13_75006_153366 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75006 ⟨153366, by decide⟩ :=
  accepted_of_selected 13 75006 ⟨153366, by decide⟩ ⟨13, 2, 0, 153366, 75006, 1737, 16384⟩
    (by decide) selected_cut_04818

theorem selected_cut_04819 : selected 8 ⟨153373, by decide⟩
    (prefixPartial 13 75007) = some ⟨13, 2, 0, 153373, 75007, 873, 16384⟩ := by
  decide +kernel

theorem context_13_75007_153373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75007 ⟨153373, by decide⟩ :=
  accepted_of_selected 13 75007 ⟨153373, by decide⟩ ⟨13, 2, 0, 153373, 75007, 873, 16384⟩
    (by decide) selected_cut_04819

theorem unmarked_context_12_18751_153374 : frontier 9 ⟨153374, by decide⟩
    (prefixCache 12 18751) (prefixPartial 12 18751) = false := by
  decide +kernel

theorem node_context_12_18751_153374 : EJMOriginalGlobalDAGData.nodes 9 ⟨153374, by decide⟩ =
    .split (coordinate 12) (![⟨153313, by decide⟩,⟨153343, by decide⟩,⟨153366, by decide⟩,⟨153373, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18751_153374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18751 ⟨153374, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18751
    ⟨153374, by decide⟩ (by decide) (![⟨153313, by decide⟩,⟨153343, by decide⟩,⟨153366, by decide⟩,⟨153373, by decide⟩]) unmarked_context_12_18751_153374 node_context_12_18751_153374
  intro a
  fin_cases a
  · exact context_13_75004_153313
  · exact context_13_75005_153343
  · exact context_13_75006_153366
  · exact context_13_75007_153373

theorem unmarked_context_11_4687_153375 : frontier 10 ⟨153375, by decide⟩
    (prefixCache 11 4687) (prefixPartial 11 4687) = false := by
  decide +kernel

theorem node_context_11_4687_153375 : EJMOriginalGlobalDAGData.nodes 10 ⟨153375, by decide⟩ =
    .split (coordinate 11) (![⟨153172, by decide⟩,⟨153246, by decide⟩,⟨153309, by decide⟩,⟨153374, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4687_153375 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4687 ⟨153375, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4687
    ⟨153375, by decide⟩ (by decide) (![⟨153172, by decide⟩,⟨153246, by decide⟩,⟨153309, by decide⟩,⟨153374, by decide⟩]) unmarked_context_11_4687_153375 node_context_11_4687_153375
  intro a
  fin_cases a
  · exact context_12_18748_153172
  · exact context_12_18749_153246
  · exact context_12_18750_153309
  · exact context_12_18751_153374

theorem unmarked_context_10_1171_153376 : frontier 11 ⟨153376, by decide⟩
    (prefixCache 10 1171) (prefixPartial 10 1171) = false := by
  decide +kernel

theorem node_context_10_1171_153376 : EJMOriginalGlobalDAGData.nodes 11 ⟨153376, by decide⟩ =
    .split (coordinate 10) (![⟨152544, by decide⟩,⟨152817, by decide⟩,⟨153116, by decide⟩,⟨153375, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1171_153376 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1171 ⟨153376, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1171
    ⟨153376, by decide⟩ (by decide) (![⟨152544, by decide⟩,⟨152817, by decide⟩,⟨153116, by decide⟩,⟨153375, by decide⟩]) unmarked_context_10_1171_153376 node_context_10_1171_153376
  intro a
  fin_cases a
  · exact context_11_4684_152544
  · exact context_11_4685_152817
  · exact context_11_4686_153116
  · exact context_11_4687_153375

theorem unmarked_context_9_292_153377 : frontier 12 ⟨153377, by decide⟩
    (prefixCache 9 292) (prefixPartial 9 292) = false := by
  decide +kernel

theorem node_context_9_292_153377 : EJMOriginalGlobalDAGData.nodes 12 ⟨153377, by decide⟩ =
    .split (coordinate 9) (![⟨149399, by decide⟩,⟨150857, by decide⟩,⟨152232, by decide⟩,⟨153376, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_292_153377 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 292 ⟨153377, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 292
    ⟨153377, by decide⟩ (by decide) (![⟨149399, by decide⟩,⟨150857, by decide⟩,⟨152232, by decide⟩,⟨153376, by decide⟩]) unmarked_context_9_292_153377 node_context_9_292_153377
  intro a
  fin_cases a
  · exact context_10_1168_149399
  · exact context_10_1169_150857
  · exact context_10_1170_152232
  · exact context_10_1171_153376

theorem selected_cut_04820 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75008) = some ⟨13, 1, 0, 3444, 75008, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75008_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75008 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75008 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75008, 1, 16384⟩
    (by decide) selected_cut_04820

theorem selected_cut_04821 : selected 8 ⟨153400, by decide⟩
    (prefixPartial 13 75009) = some ⟨13, 2, 0, 153400, 75009, 2925, 16384⟩ := by
  decide +kernel

theorem context_13_75009_153400 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75009 ⟨153400, by decide⟩ :=
  accepted_of_selected 13 75009 ⟨153400, by decide⟩ ⟨13, 2, 0, 153400, 75009, 2925, 16384⟩
    (by decide) selected_cut_04821

theorem selected_cut_04822 : selected 8 ⟨153424, by decide⟩
    (prefixPartial 13 75010) = some ⟨13, 2, 0, 153424, 75010, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_75010_153424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75010 ⟨153424, by decide⟩ :=
  accepted_of_selected 13 75010 ⟨153424, by decide⟩ ⟨13, 2, 0, 153424, 75010, 1873, 16384⟩
    (by decide) selected_cut_04822

theorem selected_cut_04823 : selected 8 ⟨153433, by decide⟩
    (prefixPartial 13 75011) = some ⟨13, 2, 0, 153433, 75011, 973, 16384⟩ := by
  decide +kernel

theorem context_13_75011_153433 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75011 ⟨153433, by decide⟩ :=
  accepted_of_selected 13 75011 ⟨153433, by decide⟩ ⟨13, 2, 0, 153433, 75011, 973, 16384⟩
    (by decide) selected_cut_04823

theorem unmarked_context_12_18752_153434 : frontier 9 ⟨153434, by decide⟩
    (prefixCache 12 18752) (prefixPartial 12 18752) = false := by
  decide +kernel

theorem node_context_12_18752_153434 : EJMOriginalGlobalDAGData.nodes 9 ⟨153434, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153400, by decide⟩,⟨153424, by decide⟩,⟨153433, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18752_153434 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18752 ⟨153434, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18752
    ⟨153434, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153400, by decide⟩,⟨153424, by decide⟩,⟨153433, by decide⟩]) unmarked_context_12_18752_153434 node_context_12_18752_153434
  intro a
  fin_cases a
  · exact context_13_75008_3444
  · exact context_13_75009_153400
  · exact context_13_75010_153424
  · exact context_13_75011_153433

theorem selected_cut_04824 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75012) = some ⟨13, 1, 0, 3444, 75012, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75012_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75012 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75012 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75012, 1, 16384⟩
    (by decide) selected_cut_04824

theorem selected_cut_04825 : selected 8 ⟨153466, by decide⟩
    (prefixPartial 13 75013) = some ⟨13, 2, 0, 153466, 75013, 2765, 16384⟩ := by
  decide +kernel

theorem context_13_75013_153466 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75013 ⟨153466, by decide⟩ :=
  accepted_of_selected 13 75013 ⟨153466, by decide⟩ ⟨13, 2, 0, 153466, 75013, 2765, 16384⟩
    (by decide) selected_cut_04825

theorem selected_cut_04826 : selected 8 ⟨153490, by decide⟩
    (prefixPartial 13 75014) = some ⟨13, 2, 0, 153490, 75014, 2173, 16384⟩ := by
  decide +kernel

theorem context_13_75014_153490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75014 ⟨153490, by decide⟩ :=
  accepted_of_selected 13 75014 ⟨153490, by decide⟩ ⟨13, 2, 0, 153490, 75014, 2173, 16384⟩
    (by decide) selected_cut_04826

theorem selected_cut_04827 : selected 8 ⟨153500, by decide⟩
    (prefixPartial 13 75015) = some ⟨13, 2, 0, 153500, 75015, 1129, 16384⟩ := by
  decide +kernel

theorem context_13_75015_153500 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75015 ⟨153500, by decide⟩ :=
  accepted_of_selected 13 75015 ⟨153500, by decide⟩ ⟨13, 2, 0, 153500, 75015, 1129, 16384⟩
    (by decide) selected_cut_04827

theorem unmarked_context_12_18753_153501 : frontier 9 ⟨153501, by decide⟩
    (prefixCache 12 18753) (prefixPartial 12 18753) = false := by
  decide +kernel

theorem node_context_12_18753_153501 : EJMOriginalGlobalDAGData.nodes 9 ⟨153501, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153466, by decide⟩,⟨153490, by decide⟩,⟨153500, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18753_153501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18753 ⟨153501, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18753
    ⟨153501, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153466, by decide⟩,⟨153490, by decide⟩,⟨153500, by decide⟩]) unmarked_context_12_18753_153501 node_context_12_18753_153501
  intro a
  fin_cases a
  · exact context_13_75012_3444
  · exact context_13_75013_153466
  · exact context_13_75014_153490
  · exact context_13_75015_153500

theorem selected_cut_04828 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75016) = some ⟨13, 1, 0, 3444, 75016, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75016_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75016 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75016 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75016, 1, 16384⟩
    (by decide) selected_cut_04828

theorem selected_cut_04829 : selected 8 ⟨153526, by decide⟩
    (prefixPartial 13 75017) = some ⟨13, 2, 0, 153526, 75017, 2197, 16384⟩ := by
  decide +kernel

theorem context_13_75017_153526 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75017 ⟨153526, by decide⟩ :=
  accepted_of_selected 13 75017 ⟨153526, by decide⟩ ⟨13, 2, 0, 153526, 75017, 2197, 16384⟩
    (by decide) selected_cut_04829

theorem selected_cut_04830 : selected 8 ⟨153545, by decide⟩
    (prefixPartial 13 75018) = some ⟨13, 2, 0, 153545, 75018, 1873, 16384⟩ := by
  decide +kernel

theorem context_13_75018_153545 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75018 ⟨153545, by decide⟩ :=
  accepted_of_selected 13 75018 ⟨153545, by decide⟩ ⟨13, 2, 0, 153545, 75018, 1873, 16384⟩
    (by decide) selected_cut_04830

theorem selected_cut_04831 : selected 8 ⟨153556, by decide⟩
    (prefixPartial 13 75019) = some ⟨13, 2, 0, 153556, 75019, 989, 16384⟩ := by
  decide +kernel

theorem context_13_75019_153556 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75019 ⟨153556, by decide⟩ :=
  accepted_of_selected 13 75019 ⟨153556, by decide⟩ ⟨13, 2, 0, 153556, 75019, 989, 16384⟩
    (by decide) selected_cut_04831

theorem unmarked_context_12_18754_153557 : frontier 9 ⟨153557, by decide⟩
    (prefixCache 12 18754) (prefixPartial 12 18754) = false := by
  decide +kernel

theorem node_context_12_18754_153557 : EJMOriginalGlobalDAGData.nodes 9 ⟨153557, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153526, by decide⟩,⟨153545, by decide⟩,⟨153556, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18754_153557 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18754 ⟨153557, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18754
    ⟨153557, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153526, by decide⟩,⟨153545, by decide⟩,⟨153556, by decide⟩]) unmarked_context_12_18754_153557 node_context_12_18754_153557
  intro a
  fin_cases a
  · exact context_13_75016_3444
  · exact context_13_75017_153526
  · exact context_13_75018_153545
  · exact context_13_75019_153556

theorem selected_cut_04832 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75020) = some ⟨13, 1, 0, 3444, 75020, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75020_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75020 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75020 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75020, 1, 16384⟩
    (by decide) selected_cut_04832

theorem selected_cut_04833 : selected 8 ⟨153587, by decide⟩
    (prefixPartial 13 75021) = some ⟨13, 2, 0, 153587, 75021, 2297, 16384⟩ := by
  decide +kernel

theorem context_13_75021_153587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75021 ⟨153587, by decide⟩ :=
  accepted_of_selected 13 75021 ⟨153587, by decide⟩ ⟨13, 2, 0, 153587, 75021, 2297, 16384⟩
    (by decide) selected_cut_04833

theorem selected_cut_04834 : selected 8 ⟨153616, by decide⟩
    (prefixPartial 13 75022) = some ⟨13, 2, 0, 153616, 75022, 2037, 16384⟩ := by
  decide +kernel

theorem context_13_75022_153616 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75022 ⟨153616, by decide⟩ :=
  accepted_of_selected 13 75022 ⟨153616, by decide⟩ ⟨13, 2, 0, 153616, 75022, 2037, 16384⟩
    (by decide) selected_cut_04834

theorem selected_cut_04835 : selected 8 ⟨153629, by decide⟩
    (prefixPartial 13 75023) = some ⟨13, 2, 0, 153629, 75023, 889, 16384⟩ := by
  decide +kernel

theorem context_13_75023_153629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75023 ⟨153629, by decide⟩ :=
  accepted_of_selected 13 75023 ⟨153629, by decide⟩ ⟨13, 2, 0, 153629, 75023, 889, 16384⟩
    (by decide) selected_cut_04835

theorem unmarked_context_12_18755_153630 : frontier 9 ⟨153630, by decide⟩
    (prefixCache 12 18755) (prefixPartial 12 18755) = false := by
  decide +kernel

theorem node_context_12_18755_153630 : EJMOriginalGlobalDAGData.nodes 9 ⟨153630, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153587, by decide⟩,⟨153616, by decide⟩,⟨153629, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18755_153630 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18755 ⟨153630, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18755
    ⟨153630, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153587, by decide⟩,⟨153616, by decide⟩,⟨153629, by decide⟩]) unmarked_context_12_18755_153630 node_context_12_18755_153630
  intro a
  fin_cases a
  · exact context_13_75020_3444
  · exact context_13_75021_153587
  · exact context_13_75022_153616
  · exact context_13_75023_153629

theorem unmarked_context_11_4688_153631 : frontier 10 ⟨153631, by decide⟩
    (prefixCache 11 4688) (prefixPartial 11 4688) = false := by
  decide +kernel

theorem node_context_11_4688_153631 : EJMOriginalGlobalDAGData.nodes 10 ⟨153631, by decide⟩ =
    .split (coordinate 11) (![⟨153434, by decide⟩,⟨153501, by decide⟩,⟨153557, by decide⟩,⟨153630, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4688_153631 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4688 ⟨153631, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4688
    ⟨153631, by decide⟩ (by decide) (![⟨153434, by decide⟩,⟨153501, by decide⟩,⟨153557, by decide⟩,⟨153630, by decide⟩]) unmarked_context_11_4688_153631 node_context_11_4688_153631
  intro a
  fin_cases a
  · exact context_12_18752_153434
  · exact context_12_18753_153501
  · exact context_12_18754_153557
  · exact context_12_18755_153630

theorem selected_cut_04836 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75024) = some ⟨13, 1, 0, 3444, 75024, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75024_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75024 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75024 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75024, 1, 16384⟩
    (by decide) selected_cut_04836

theorem selected_cut_04837 : selected 8 ⟨153656, by decide⟩
    (prefixPartial 13 75025) = some ⟨13, 2, 0, 153656, 75025, 2081, 16384⟩ := by
  decide +kernel

theorem context_13_75025_153656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75025 ⟨153656, by decide⟩ :=
  accepted_of_selected 13 75025 ⟨153656, by decide⟩ ⟨13, 2, 0, 153656, 75025, 2081, 16384⟩
    (by decide) selected_cut_04837

theorem selected_cut_04838 : selected 8 ⟨153677, by decide⟩
    (prefixPartial 13 75026) = some ⟨13, 2, 0, 153677, 75026, 1729, 16384⟩ := by
  decide +kernel

theorem context_13_75026_153677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75026 ⟨153677, by decide⟩ :=
  accepted_of_selected 13 75026 ⟨153677, by decide⟩ ⟨13, 2, 0, 153677, 75026, 1729, 16384⟩
    (by decide) selected_cut_04838

theorem selected_cut_04839 : selected 8 ⟨153692, by decide⟩
    (prefixPartial 13 75027) = some ⟨13, 2, 0, 153692, 75027, 1013, 16384⟩ := by
  decide +kernel

theorem context_13_75027_153692 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75027 ⟨153692, by decide⟩ :=
  accepted_of_selected 13 75027 ⟨153692, by decide⟩ ⟨13, 2, 0, 153692, 75027, 1013, 16384⟩
    (by decide) selected_cut_04839

theorem unmarked_context_12_18756_153693 : frontier 9 ⟨153693, by decide⟩
    (prefixCache 12 18756) (prefixPartial 12 18756) = false := by
  decide +kernel

theorem node_context_12_18756_153693 : EJMOriginalGlobalDAGData.nodes 9 ⟨153693, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153656, by decide⟩,⟨153677, by decide⟩,⟨153692, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18756_153693 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18756 ⟨153693, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18756
    ⟨153693, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153656, by decide⟩,⟨153677, by decide⟩,⟨153692, by decide⟩]) unmarked_context_12_18756_153693 node_context_12_18756_153693
  intro a
  fin_cases a
  · exact context_13_75024_3444
  · exact context_13_75025_153656
  · exact context_13_75026_153677
  · exact context_13_75027_153692

theorem selected_cut_04840 : selected 9 ⟨126884, by decide⟩
    (prefixPartial 12 18757) = some ⟨12, 1, 0, 126884, 18757, 1, 65536⟩ := by
  decide +kernel

theorem context_12_18757_126884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18757 ⟨126884, by decide⟩ :=
  accepted_of_selected 12 18757 ⟨126884, by decide⟩ ⟨12, 1, 0, 126884, 18757, 1, 65536⟩
    (by decide) selected_cut_04840

theorem selected_cut_04841 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75032) = some ⟨13, 1, 0, 3444, 75032, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75032_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75032 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75032 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75032, 1, 16384⟩
    (by decide) selected_cut_04841

theorem selected_cut_04842 : selected 8 ⟨153723, by decide⟩
    (prefixPartial 13 75033) = some ⟨13, 2, 0, 153723, 75033, 2181, 16384⟩ := by
  decide +kernel

theorem context_13_75033_153723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75033 ⟨153723, by decide⟩ :=
  accepted_of_selected 13 75033 ⟨153723, by decide⟩ ⟨13, 2, 0, 153723, 75033, 2181, 16384⟩
    (by decide) selected_cut_04842

theorem selected_cut_04843 : selected 8 ⟨153746, by decide⟩
    (prefixPartial 13 75034) = some ⟨13, 2, 0, 153746, 75034, 1785, 16384⟩ := by
  decide +kernel

theorem context_13_75034_153746 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75034 ⟨153746, by decide⟩ :=
  accepted_of_selected 13 75034 ⟨153746, by decide⟩ ⟨13, 2, 0, 153746, 75034, 1785, 16384⟩
    (by decide) selected_cut_04843

theorem selected_cut_04844 : selected 8 ⟨153758, by decide⟩
    (prefixPartial 13 75035) = some ⟨13, 2, 0, 153758, 75035, 989, 16384⟩ := by
  decide +kernel

theorem context_13_75035_153758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75035 ⟨153758, by decide⟩ :=
  accepted_of_selected 13 75035 ⟨153758, by decide⟩ ⟨13, 2, 0, 153758, 75035, 989, 16384⟩
    (by decide) selected_cut_04844

theorem unmarked_context_12_18758_153759 : frontier 9 ⟨153759, by decide⟩
    (prefixCache 12 18758) (prefixPartial 12 18758) = false := by
  decide +kernel

theorem node_context_12_18758_153759 : EJMOriginalGlobalDAGData.nodes 9 ⟨153759, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153723, by decide⟩,⟨153746, by decide⟩,⟨153758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18758_153759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18758 ⟨153759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18758
    ⟨153759, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153723, by decide⟩,⟨153746, by decide⟩,⟨153758, by decide⟩]) unmarked_context_12_18758_153759 node_context_12_18758_153759
  intro a
  fin_cases a
  · exact context_13_75032_3444
  · exact context_13_75033_153723
  · exact context_13_75034_153746
  · exact context_13_75035_153758

theorem selected_cut_04845 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75036) = some ⟨13, 1, 0, 3444, 75036, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75036_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75036 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75036 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75036, 1, 16384⟩
    (by decide) selected_cut_04845

theorem selected_cut_04846 : selected 8 ⟨153790, by decide⟩
    (prefixPartial 13 75037) = some ⟨13, 2, 0, 153790, 75037, 2329, 16384⟩ := by
  decide +kernel

theorem context_13_75037_153790 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75037 ⟨153790, by decide⟩ :=
  accepted_of_selected 13 75037 ⟨153790, by decide⟩ ⟨13, 2, 0, 153790, 75037, 2329, 16384⟩
    (by decide) selected_cut_04846

theorem selected_cut_04847 : selected 8 ⟨153812, by decide⟩
    (prefixPartial 13 75038) = some ⟨13, 2, 0, 153812, 75038, 1905, 16384⟩ := by
  decide +kernel

theorem context_13_75038_153812 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75038 ⟨153812, by decide⟩ :=
  accepted_of_selected 13 75038 ⟨153812, by decide⟩ ⟨13, 2, 0, 153812, 75038, 1905, 16384⟩
    (by decide) selected_cut_04847

theorem selected_cut_04848 : selected 8 ⟨153823, by decide⟩
    (prefixPartial 13 75039) = some ⟨13, 2, 0, 153823, 75039, 949, 16384⟩ := by
  decide +kernel

theorem context_13_75039_153823 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75039 ⟨153823, by decide⟩ :=
  accepted_of_selected 13 75039 ⟨153823, by decide⟩ ⟨13, 2, 0, 153823, 75039, 949, 16384⟩
    (by decide) selected_cut_04848

theorem unmarked_context_12_18759_153824 : frontier 9 ⟨153824, by decide⟩
    (prefixCache 12 18759) (prefixPartial 12 18759) = false := by
  decide +kernel

theorem node_context_12_18759_153824 : EJMOriginalGlobalDAGData.nodes 9 ⟨153824, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153790, by decide⟩,⟨153812, by decide⟩,⟨153823, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18759_153824 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18759 ⟨153824, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18759
    ⟨153824, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153790, by decide⟩,⟨153812, by decide⟩,⟨153823, by decide⟩]) unmarked_context_12_18759_153824 node_context_12_18759_153824
  intro a
  fin_cases a
  · exact context_13_75036_3444
  · exact context_13_75037_153790
  · exact context_13_75038_153812
  · exact context_13_75039_153823

theorem unmarked_context_11_4689_153825 : frontier 10 ⟨153825, by decide⟩
    (prefixCache 11 4689) (prefixPartial 11 4689) = false := by
  decide +kernel

theorem node_context_11_4689_153825 : EJMOriginalGlobalDAGData.nodes 10 ⟨153825, by decide⟩ =
    .split (coordinate 11) (![⟨153693, by decide⟩,⟨126884, by decide⟩,⟨153759, by decide⟩,⟨153824, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4689_153825 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4689 ⟨153825, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4689
    ⟨153825, by decide⟩ (by decide) (![⟨153693, by decide⟩,⟨126884, by decide⟩,⟨153759, by decide⟩,⟨153824, by decide⟩]) unmarked_context_11_4689_153825 node_context_11_4689_153825
  intro a
  fin_cases a
  · exact context_12_18756_153693
  · exact context_12_18757_126884
  · exact context_12_18758_153759
  · exact context_12_18759_153824

theorem selected_cut_04849 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75040) = some ⟨13, 1, 0, 3444, 75040, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75040_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75040 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75040 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75040, 1, 16384⟩
    (by decide) selected_cut_04849

theorem selected_cut_04850 : selected 8 ⟨153850, by decide⟩
    (prefixPartial 13 75041) = some ⟨13, 2, 0, 153850, 75041, 2313, 16384⟩ := by
  decide +kernel

theorem context_13_75041_153850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75041 ⟨153850, by decide⟩ :=
  accepted_of_selected 13 75041 ⟨153850, by decide⟩ ⟨13, 2, 0, 153850, 75041, 2313, 16384⟩
    (by decide) selected_cut_04850

theorem selected_cut_04851 : selected 8 ⟨153868, by decide⟩
    (prefixPartial 13 75042) = some ⟨13, 2, 0, 153868, 75042, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_75042_153868 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75042 ⟨153868, by decide⟩ :=
  accepted_of_selected 13 75042 ⟨153868, by decide⟩ ⟨13, 2, 0, 153868, 75042, 1889, 16384⟩
    (by decide) selected_cut_04851

theorem selected_cut_04852 : selected 8 ⟨153878, by decide⟩
    (prefixPartial 13 75043) = some ⟨13, 2, 0, 153878, 75043, 961, 16384⟩ := by
  decide +kernel

theorem context_13_75043_153878 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75043 ⟨153878, by decide⟩ :=
  accepted_of_selected 13 75043 ⟨153878, by decide⟩ ⟨13, 2, 0, 153878, 75043, 961, 16384⟩
    (by decide) selected_cut_04852

theorem unmarked_context_12_18760_153879 : frontier 9 ⟨153879, by decide⟩
    (prefixCache 12 18760) (prefixPartial 12 18760) = false := by
  decide +kernel

theorem node_context_12_18760_153879 : EJMOriginalGlobalDAGData.nodes 9 ⟨153879, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153850, by decide⟩,⟨153868, by decide⟩,⟨153878, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18760_153879 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18760 ⟨153879, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18760
    ⟨153879, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153850, by decide⟩,⟨153868, by decide⟩,⟨153878, by decide⟩]) unmarked_context_12_18760_153879 node_context_12_18760_153879
  intro a
  fin_cases a
  · exact context_13_75040_3444
  · exact context_13_75041_153850
  · exact context_13_75042_153868
  · exact context_13_75043_153878

theorem selected_cut_04853 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75044) = some ⟨13, 1, 0, 3444, 75044, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75044_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75044 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75044 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75044, 1, 16384⟩
    (by decide) selected_cut_04853

theorem selected_cut_04854 : selected 8 ⟨153908, by decide⟩
    (prefixPartial 13 75045) = some ⟨13, 2, 0, 153908, 75045, 2689, 16384⟩ := by
  decide +kernel

theorem context_13_75045_153908 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75045 ⟨153908, by decide⟩ :=
  accepted_of_selected 13 75045 ⟨153908, by decide⟩ ⟨13, 2, 0, 153908, 75045, 2689, 16384⟩
    (by decide) selected_cut_04854

theorem selected_cut_04855 : selected 8 ⟨153933, by decide⟩
    (prefixPartial 13 75046) = some ⟨13, 2, 0, 153933, 75046, 2421, 16384⟩ := by
  decide +kernel

theorem context_13_75046_153933 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75046 ⟨153933, by decide⟩ :=
  accepted_of_selected 13 75046 ⟨153933, by decide⟩ ⟨13, 2, 0, 153933, 75046, 2421, 16384⟩
    (by decide) selected_cut_04855

theorem selected_cut_04856 : selected 8 ⟨153940, by decide⟩
    (prefixPartial 13 75047) = some ⟨13, 2, 0, 153940, 75047, 1201, 16384⟩ := by
  decide +kernel

theorem context_13_75047_153940 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75047 ⟨153940, by decide⟩ :=
  accepted_of_selected 13 75047 ⟨153940, by decide⟩ ⟨13, 2, 0, 153940, 75047, 1201, 16384⟩
    (by decide) selected_cut_04856

theorem unmarked_context_12_18761_153941 : frontier 9 ⟨153941, by decide⟩
    (prefixCache 12 18761) (prefixPartial 12 18761) = false := by
  decide +kernel

theorem node_context_12_18761_153941 : EJMOriginalGlobalDAGData.nodes 9 ⟨153941, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153908, by decide⟩,⟨153933, by decide⟩,⟨153940, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18761_153941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18761 ⟨153941, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18761
    ⟨153941, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153908, by decide⟩,⟨153933, by decide⟩,⟨153940, by decide⟩]) unmarked_context_12_18761_153941 node_context_12_18761_153941
  intro a
  fin_cases a
  · exact context_13_75044_3444
  · exact context_13_75045_153908
  · exact context_13_75046_153933
  · exact context_13_75047_153940

theorem selected_cut_04857 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75048) = some ⟨13, 1, 0, 3444, 75048, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75048_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75048 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75048 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75048, 1, 16384⟩
    (by decide) selected_cut_04857

theorem selected_cut_04858 : selected 8 ⟨153963, by decide⟩
    (prefixPartial 13 75049) = some ⟨13, 2, 0, 153963, 75049, 1825, 16384⟩ := by
  decide +kernel

theorem context_13_75049_153963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75049 ⟨153963, by decide⟩ :=
  accepted_of_selected 13 75049 ⟨153963, by decide⟩ ⟨13, 2, 0, 153963, 75049, 1825, 16384⟩
    (by decide) selected_cut_04858

theorem selected_cut_04859 : selected 8 ⟨153984, by decide⟩
    (prefixPartial 13 75050) = some ⟨13, 2, 0, 153984, 75050, 1917, 16384⟩ := by
  decide +kernel

theorem context_13_75050_153984 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75050 ⟨153984, by decide⟩ :=
  accepted_of_selected 13 75050 ⟨153984, by decide⟩ ⟨13, 2, 0, 153984, 75050, 1917, 16384⟩
    (by decide) selected_cut_04859

theorem selected_cut_04860 : selected 8 ⟨153992, by decide⟩
    (prefixPartial 13 75051) = some ⟨13, 2, 0, 153992, 75051, 953, 16384⟩ := by
  decide +kernel

theorem context_13_75051_153992 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75051 ⟨153992, by decide⟩ :=
  accepted_of_selected 13 75051 ⟨153992, by decide⟩ ⟨13, 2, 0, 153992, 75051, 953, 16384⟩
    (by decide) selected_cut_04860

theorem unmarked_context_12_18762_153993 : frontier 9 ⟨153993, by decide⟩
    (prefixCache 12 18762) (prefixPartial 12 18762) = false := by
  decide +kernel

theorem node_context_12_18762_153993 : EJMOriginalGlobalDAGData.nodes 9 ⟨153993, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨153963, by decide⟩,⟨153984, by decide⟩,⟨153992, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18762_153993 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18762 ⟨153993, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18762
    ⟨153993, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨153963, by decide⟩,⟨153984, by decide⟩,⟨153992, by decide⟩]) unmarked_context_12_18762_153993 node_context_12_18762_153993
  intro a
  fin_cases a
  · exact context_13_75048_3444
  · exact context_13_75049_153963
  · exact context_13_75050_153984
  · exact context_13_75051_153992

theorem selected_cut_04861 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75052) = some ⟨13, 1, 0, 3444, 75052, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75052_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75052 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75052 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75052, 1, 16384⟩
    (by decide) selected_cut_04861

theorem selected_cut_04862 : selected 8 ⟨154018, by decide⟩
    (prefixPartial 13 75053) = some ⟨13, 2, 0, 154018, 75053, 2305, 16384⟩ := by
  decide +kernel

theorem context_13_75053_154018 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75053 ⟨154018, by decide⟩ :=
  accepted_of_selected 13 75053 ⟨154018, by decide⟩ ⟨13, 2, 0, 154018, 75053, 2305, 16384⟩
    (by decide) selected_cut_04862

theorem selected_cut_04863 : selected 8 ⟨154039, by decide⟩
    (prefixPartial 13 75054) = some ⟨13, 2, 0, 154039, 75054, 2201, 16384⟩ := by
  decide +kernel

theorem context_13_75054_154039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75054 ⟨154039, by decide⟩ :=
  accepted_of_selected 13 75054 ⟨154039, by decide⟩ ⟨13, 2, 0, 154039, 75054, 2201, 16384⟩
    (by decide) selected_cut_04863

theorem selected_cut_04864 : selected 8 ⟨154050, by decide⟩
    (prefixPartial 13 75055) = some ⟨13, 2, 0, 154050, 75055, 1041, 16384⟩ := by
  decide +kernel

theorem context_13_75055_154050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75055 ⟨154050, by decide⟩ :=
  accepted_of_selected 13 75055 ⟨154050, by decide⟩ ⟨13, 2, 0, 154050, 75055, 1041, 16384⟩
    (by decide) selected_cut_04864

theorem unmarked_context_12_18763_154051 : frontier 9 ⟨154051, by decide⟩
    (prefixCache 12 18763) (prefixPartial 12 18763) = false := by
  decide +kernel

theorem node_context_12_18763_154051 : EJMOriginalGlobalDAGData.nodes 9 ⟨154051, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154018, by decide⟩,⟨154039, by decide⟩,⟨154050, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18763_154051 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18763 ⟨154051, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18763
    ⟨154051, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154018, by decide⟩,⟨154039, by decide⟩,⟨154050, by decide⟩]) unmarked_context_12_18763_154051 node_context_12_18763_154051
  intro a
  fin_cases a
  · exact context_13_75052_3444
  · exact context_13_75053_154018
  · exact context_13_75054_154039
  · exact context_13_75055_154050

theorem unmarked_context_11_4690_154052 : frontier 10 ⟨154052, by decide⟩
    (prefixCache 11 4690) (prefixPartial 11 4690) = false := by
  decide +kernel

theorem node_context_11_4690_154052 : EJMOriginalGlobalDAGData.nodes 10 ⟨154052, by decide⟩ =
    .split (coordinate 11) (![⟨153879, by decide⟩,⟨153941, by decide⟩,⟨153993, by decide⟩,⟨154051, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4690_154052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4690 ⟨154052, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4690
    ⟨154052, by decide⟩ (by decide) (![⟨153879, by decide⟩,⟨153941, by decide⟩,⟨153993, by decide⟩,⟨154051, by decide⟩]) unmarked_context_11_4690_154052 node_context_11_4690_154052
  intro a
  fin_cases a
  · exact context_12_18760_153879
  · exact context_12_18761_153941
  · exact context_12_18762_153993
  · exact context_12_18763_154051

theorem selected_cut_04865 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75056) = some ⟨13, 1, 0, 3444, 75056, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75056_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75056 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75056 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75056, 1, 16384⟩
    (by decide) selected_cut_04865

theorem selected_cut_04866 : selected 8 ⟨154070, by decide⟩
    (prefixPartial 13 75057) = some ⟨13, 2, 0, 154070, 75057, 2189, 16384⟩ := by
  decide +kernel

theorem context_13_75057_154070 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75057 ⟨154070, by decide⟩ :=
  accepted_of_selected 13 75057 ⟨154070, by decide⟩ ⟨13, 2, 0, 154070, 75057, 2189, 16384⟩
    (by decide) selected_cut_04866

theorem selected_cut_04867 : selected 8 ⟨154091, by decide⟩
    (prefixPartial 13 75058) = some ⟨13, 2, 0, 154091, 75058, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_75058_154091 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75058 ⟨154091, by decide⟩ :=
  accepted_of_selected 13 75058 ⟨154091, by decide⟩ ⟨13, 2, 0, 154091, 75058, 1889, 16384⟩
    (by decide) selected_cut_04867

theorem selected_cut_04868 : selected 8 ⟨154100, by decide⟩
    (prefixPartial 13 75059) = some ⟨13, 2, 0, 154100, 75059, 1137, 16384⟩ := by
  decide +kernel

theorem context_13_75059_154100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75059 ⟨154100, by decide⟩ :=
  accepted_of_selected 13 75059 ⟨154100, by decide⟩ ⟨13, 2, 0, 154100, 75059, 1137, 16384⟩
    (by decide) selected_cut_04868

theorem unmarked_context_12_18764_154101 : frontier 9 ⟨154101, by decide⟩
    (prefixCache 12 18764) (prefixPartial 12 18764) = false := by
  decide +kernel

theorem node_context_12_18764_154101 : EJMOriginalGlobalDAGData.nodes 9 ⟨154101, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154070, by decide⟩,⟨154091, by decide⟩,⟨154100, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18764_154101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18764 ⟨154101, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18764
    ⟨154101, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154070, by decide⟩,⟨154091, by decide⟩,⟨154100, by decide⟩]) unmarked_context_12_18764_154101 node_context_12_18764_154101
  intro a
  fin_cases a
  · exact context_13_75056_3444
  · exact context_13_75057_154070
  · exact context_13_75058_154091
  · exact context_13_75059_154100

theorem selected_cut_04869 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75060) = some ⟨13, 1, 0, 3444, 75060, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75060_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75060 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75060 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75060, 1, 16384⟩
    (by decide) selected_cut_04869

theorem selected_cut_04870 : selected 8 ⟨154131, by decide⟩
    (prefixPartial 13 75061) = some ⟨13, 2, 0, 154131, 75061, 2501, 16384⟩ := by
  decide +kernel

theorem context_13_75061_154131 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75061 ⟨154131, by decide⟩ :=
  accepted_of_selected 13 75061 ⟨154131, by decide⟩ ⟨13, 2, 0, 154131, 75061, 2501, 16384⟩
    (by decide) selected_cut_04870

theorem selected_cut_04871 : selected 8 ⟨154161, by decide⟩
    (prefixPartial 13 75062) = some ⟨13, 2, 0, 154161, 75062, 2469, 16384⟩ := by
  decide +kernel

theorem context_13_75062_154161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75062 ⟨154161, by decide⟩ :=
  accepted_of_selected 13 75062 ⟨154161, by decide⟩ ⟨13, 2, 0, 154161, 75062, 2469, 16384⟩
    (by decide) selected_cut_04871

theorem selected_cut_04872 : selected 8 ⟨154182, by decide⟩
    (prefixPartial 13 75063) = some ⟨13, 2, 0, 154182, 75063, 1333, 16384⟩ := by
  decide +kernel

theorem context_13_75063_154182 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75063 ⟨154182, by decide⟩ :=
  accepted_of_selected 13 75063 ⟨154182, by decide⟩ ⟨13, 2, 0, 154182, 75063, 1333, 16384⟩
    (by decide) selected_cut_04872

theorem unmarked_context_12_18765_154183 : frontier 9 ⟨154183, by decide⟩
    (prefixCache 12 18765) (prefixPartial 12 18765) = false := by
  decide +kernel

theorem node_context_12_18765_154183 : EJMOriginalGlobalDAGData.nodes 9 ⟨154183, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154131, by decide⟩,⟨154161, by decide⟩,⟨154182, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18765_154183 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18765 ⟨154183, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18765
    ⟨154183, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154131, by decide⟩,⟨154161, by decide⟩,⟨154182, by decide⟩]) unmarked_context_12_18765_154183 node_context_12_18765_154183
  intro a
  fin_cases a
  · exact context_13_75060_3444
  · exact context_13_75061_154131
  · exact context_13_75062_154161
  · exact context_13_75063_154182

theorem selected_cut_04873 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75064) = some ⟨13, 1, 0, 3444, 75064, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75064_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75064 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75064 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75064, 1, 16384⟩
    (by decide) selected_cut_04873

theorem selected_cut_04874 : selected 8 ⟨154206, by decide⟩
    (prefixPartial 13 75065) = some ⟨13, 2, 0, 154206, 75065, 2025, 16384⟩ := by
  decide +kernel

theorem context_13_75065_154206 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75065 ⟨154206, by decide⟩ :=
  accepted_of_selected 13 75065 ⟨154206, by decide⟩ ⟨13, 2, 0, 154206, 75065, 2025, 16384⟩
    (by decide) selected_cut_04874

theorem selected_cut_04875 : selected 8 ⟨154227, by decide⟩
    (prefixPartial 13 75066) = some ⟨13, 2, 0, 154227, 75066, 2121, 16384⟩ := by
  decide +kernel

theorem context_13_75066_154227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75066 ⟨154227, by decide⟩ :=
  accepted_of_selected 13 75066 ⟨154227, by decide⟩ ⟨13, 2, 0, 154227, 75066, 2121, 16384⟩
    (by decide) selected_cut_04875

theorem selected_cut_04876 : selected 8 ⟨154235, by decide⟩
    (prefixPartial 13 75067) = some ⟨13, 2, 0, 154235, 75067, 1185, 16384⟩ := by
  decide +kernel

theorem context_13_75067_154235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75067 ⟨154235, by decide⟩ :=
  accepted_of_selected 13 75067 ⟨154235, by decide⟩ ⟨13, 2, 0, 154235, 75067, 1185, 16384⟩
    (by decide) selected_cut_04876

theorem unmarked_context_12_18766_154236 : frontier 9 ⟨154236, by decide⟩
    (prefixCache 12 18766) (prefixPartial 12 18766) = false := by
  decide +kernel

theorem node_context_12_18766_154236 : EJMOriginalGlobalDAGData.nodes 9 ⟨154236, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154206, by decide⟩,⟨154227, by decide⟩,⟨154235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18766_154236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18766 ⟨154236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18766
    ⟨154236, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154206, by decide⟩,⟨154227, by decide⟩,⟨154235, by decide⟩]) unmarked_context_12_18766_154236 node_context_12_18766_154236
  intro a
  fin_cases a
  · exact context_13_75064_3444
  · exact context_13_75065_154206
  · exact context_13_75066_154227
  · exact context_13_75067_154235

theorem selected_cut_04877 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75068) = some ⟨13, 1, 0, 3444, 75068, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75068_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75068 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75068 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75068, 1, 16384⟩
    (by decide) selected_cut_04877

theorem selected_cut_04878 : selected 8 ⟨154256, by decide⟩
    (prefixPartial 13 75069) = some ⟨13, 2, 0, 154256, 75069, 1889, 16384⟩ := by
  decide +kernel

theorem context_13_75069_154256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75069 ⟨154256, by decide⟩ :=
  accepted_of_selected 13 75069 ⟨154256, by decide⟩ ⟨13, 2, 0, 154256, 75069, 1889, 16384⟩
    (by decide) selected_cut_04878

theorem selected_cut_04879 : selected 8 ⟨154276, by decide⟩
    (prefixPartial 13 75070) = some ⟨13, 2, 0, 154276, 75070, 2029, 16384⟩ := by
  decide +kernel

theorem context_13_75070_154276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75070 ⟨154276, by decide⟩ :=
  accepted_of_selected 13 75070 ⟨154276, by decide⟩ ⟨13, 2, 0, 154276, 75070, 2029, 16384⟩
    (by decide) selected_cut_04879

theorem selected_cut_04880 : selected 8 ⟨154283, by decide⟩
    (prefixPartial 13 75071) = some ⟨13, 2, 0, 154283, 75071, 1101, 16384⟩ := by
  decide +kernel

theorem context_13_75071_154283 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75071 ⟨154283, by decide⟩ :=
  accepted_of_selected 13 75071 ⟨154283, by decide⟩ ⟨13, 2, 0, 154283, 75071, 1101, 16384⟩
    (by decide) selected_cut_04880

theorem unmarked_context_12_18767_154284 : frontier 9 ⟨154284, by decide⟩
    (prefixCache 12 18767) (prefixPartial 12 18767) = false := by
  decide +kernel

theorem node_context_12_18767_154284 : EJMOriginalGlobalDAGData.nodes 9 ⟨154284, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154256, by decide⟩,⟨154276, by decide⟩,⟨154283, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18767_154284 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18767 ⟨154284, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18767
    ⟨154284, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154256, by decide⟩,⟨154276, by decide⟩,⟨154283, by decide⟩]) unmarked_context_12_18767_154284 node_context_12_18767_154284
  intro a
  fin_cases a
  · exact context_13_75068_3444
  · exact context_13_75069_154256
  · exact context_13_75070_154276
  · exact context_13_75071_154283

theorem unmarked_context_11_4691_154285 : frontier 10 ⟨154285, by decide⟩
    (prefixCache 11 4691) (prefixPartial 11 4691) = false := by
  decide +kernel

theorem node_context_11_4691_154285 : EJMOriginalGlobalDAGData.nodes 10 ⟨154285, by decide⟩ =
    .split (coordinate 11) (![⟨154101, by decide⟩,⟨154183, by decide⟩,⟨154236, by decide⟩,⟨154284, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4691_154285 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4691 ⟨154285, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4691
    ⟨154285, by decide⟩ (by decide) (![⟨154101, by decide⟩,⟨154183, by decide⟩,⟨154236, by decide⟩,⟨154284, by decide⟩]) unmarked_context_11_4691_154285 node_context_11_4691_154285
  intro a
  fin_cases a
  · exact context_12_18764_154101
  · exact context_12_18765_154183
  · exact context_12_18766_154236
  · exact context_12_18767_154284

theorem unmarked_context_10_1172_154286 : frontier 11 ⟨154286, by decide⟩
    (prefixCache 10 1172) (prefixPartial 10 1172) = false := by
  decide +kernel

theorem node_context_10_1172_154286 : EJMOriginalGlobalDAGData.nodes 11 ⟨154286, by decide⟩ =
    .split (coordinate 10) (![⟨153631, by decide⟩,⟨153825, by decide⟩,⟨154052, by decide⟩,⟨154285, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_1172_154286 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 1172 ⟨154286, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 1172
    ⟨154286, by decide⟩ (by decide) (![⟨153631, by decide⟩,⟨153825, by decide⟩,⟨154052, by decide⟩,⟨154285, by decide⟩]) unmarked_context_10_1172_154286 node_context_10_1172_154286
  intro a
  fin_cases a
  · exact context_11_4688_153631
  · exact context_11_4689_153825
  · exact context_11_4690_154052
  · exact context_11_4691_154285

theorem selected_cut_04881 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75072) = some ⟨13, 1, 0, 3444, 75072, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75072_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75072 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75072 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75072, 1, 16384⟩
    (by decide) selected_cut_04881

theorem selected_cut_04882 : selected 8 ⟨154305, by decide⟩
    (prefixPartial 13 75073) = some ⟨13, 2, 0, 154305, 75073, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_75073_154305 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75073 ⟨154305, by decide⟩ :=
  accepted_of_selected 13 75073 ⟨154305, by decide⟩ ⟨13, 2, 0, 154305, 75073, 1973, 16384⟩
    (by decide) selected_cut_04882

theorem selected_cut_04883 : selected 8 ⟨154329, by decide⟩
    (prefixPartial 13 75074) = some ⟨13, 2, 0, 154329, 75074, 1709, 16384⟩ := by
  decide +kernel

theorem context_13_75074_154329 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75074 ⟨154329, by decide⟩ :=
  accepted_of_selected 13 75074 ⟨154329, by decide⟩ ⟨13, 2, 0, 154329, 75074, 1709, 16384⟩
    (by decide) selected_cut_04883

theorem selected_cut_04884 : selected 8 ⟨154337, by decide⟩
    (prefixPartial 13 75075) = some ⟨13, 2, 0, 154337, 75075, 1009, 16384⟩ := by
  decide +kernel

theorem context_13_75075_154337 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75075 ⟨154337, by decide⟩ :=
  accepted_of_selected 13 75075 ⟨154337, by decide⟩ ⟨13, 2, 0, 154337, 75075, 1009, 16384⟩
    (by decide) selected_cut_04884

theorem unmarked_context_12_18768_154338 : frontier 9 ⟨154338, by decide⟩
    (prefixCache 12 18768) (prefixPartial 12 18768) = false := by
  decide +kernel

theorem node_context_12_18768_154338 : EJMOriginalGlobalDAGData.nodes 9 ⟨154338, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154305, by decide⟩,⟨154329, by decide⟩,⟨154337, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18768_154338 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18768 ⟨154338, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18768
    ⟨154338, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154305, by decide⟩,⟨154329, by decide⟩,⟨154337, by decide⟩]) unmarked_context_12_18768_154338 node_context_12_18768_154338
  intro a
  fin_cases a
  · exact context_13_75072_3444
  · exact context_13_75073_154305
  · exact context_13_75074_154329
  · exact context_13_75075_154337

theorem selected_cut_04885 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75076) = some ⟨13, 1, 0, 3444, 75076, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75076_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75076 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75076 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75076, 1, 16384⟩
    (by decide) selected_cut_04885

theorem selected_cut_04886 : selected 8 ⟨154365, by decide⟩
    (prefixPartial 13 75077) = some ⟨13, 2, 0, 154365, 75077, 1853, 16384⟩ := by
  decide +kernel

theorem context_13_75077_154365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75077 ⟨154365, by decide⟩ :=
  accepted_of_selected 13 75077 ⟨154365, by decide⟩ ⟨13, 2, 0, 154365, 75077, 1853, 16384⟩
    (by decide) selected_cut_04886

theorem selected_cut_04887 : selected 8 ⟨154392, by decide⟩
    (prefixPartial 13 75078) = some ⟨13, 2, 0, 154392, 75078, 2129, 16384⟩ := by
  decide +kernel

theorem context_13_75078_154392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75078 ⟨154392, by decide⟩ :=
  accepted_of_selected 13 75078 ⟨154392, by decide⟩ ⟨13, 2, 0, 154392, 75078, 2129, 16384⟩
    (by decide) selected_cut_04887

theorem selected_cut_04888 : selected 8 ⟨154405, by decide⟩
    (prefixPartial 13 75079) = some ⟨13, 2, 0, 154405, 75079, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_75079_154405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75079 ⟨154405, by decide⟩ :=
  accepted_of_selected 13 75079 ⟨154405, by decide⟩ ⟨13, 2, 0, 154405, 75079, 1113, 16384⟩
    (by decide) selected_cut_04888

theorem unmarked_context_12_18769_154406 : frontier 9 ⟨154406, by decide⟩
    (prefixCache 12 18769) (prefixPartial 12 18769) = false := by
  decide +kernel

theorem node_context_12_18769_154406 : EJMOriginalGlobalDAGData.nodes 9 ⟨154406, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154365, by decide⟩,⟨154392, by decide⟩,⟨154405, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18769_154406 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18769 ⟨154406, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18769
    ⟨154406, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154365, by decide⟩,⟨154392, by decide⟩,⟨154405, by decide⟩]) unmarked_context_12_18769_154406 node_context_12_18769_154406
  intro a
  fin_cases a
  · exact context_13_75076_3444
  · exact context_13_75077_154365
  · exact context_13_75078_154392
  · exact context_13_75079_154405

theorem selected_cut_04889 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75080) = some ⟨13, 1, 0, 3444, 75080, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75080_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75080 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75080 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75080, 1, 16384⟩
    (by decide) selected_cut_04889

theorem selected_cut_04890 : selected 8 ⟨154431, by decide⟩
    (prefixPartial 13 75081) = some ⟨13, 2, 0, 154431, 75081, 1705, 16384⟩ := by
  decide +kernel

theorem context_13_75081_154431 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75081 ⟨154431, by decide⟩ :=
  accepted_of_selected 13 75081 ⟨154431, by decide⟩ ⟨13, 2, 0, 154431, 75081, 1705, 16384⟩
    (by decide) selected_cut_04890

theorem selected_cut_04891 : selected 8 ⟨154458, by decide⟩
    (prefixPartial 13 75082) = some ⟨13, 2, 0, 154458, 75082, 1973, 16384⟩ := by
  decide +kernel

theorem context_13_75082_154458 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75082 ⟨154458, by decide⟩ :=
  accepted_of_selected 13 75082 ⟨154458, by decide⟩ ⟨13, 2, 0, 154458, 75082, 1973, 16384⟩
    (by decide) selected_cut_04891

theorem selected_cut_04892 : selected 8 ⟨154474, by decide⟩
    (prefixPartial 13 75083) = some ⟨13, 2, 0, 154474, 75083, 1113, 16384⟩ := by
  decide +kernel

theorem context_13_75083_154474 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75083 ⟨154474, by decide⟩ :=
  accepted_of_selected 13 75083 ⟨154474, by decide⟩ ⟨13, 2, 0, 154474, 75083, 1113, 16384⟩
    (by decide) selected_cut_04892

theorem unmarked_context_12_18770_154475 : frontier 9 ⟨154475, by decide⟩
    (prefixCache 12 18770) (prefixPartial 12 18770) = false := by
  decide +kernel

theorem node_context_12_18770_154475 : EJMOriginalGlobalDAGData.nodes 9 ⟨154475, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154431, by decide⟩,⟨154458, by decide⟩,⟨154474, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18770_154475 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18770 ⟨154475, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18770
    ⟨154475, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154431, by decide⟩,⟨154458, by decide⟩,⟨154474, by decide⟩]) unmarked_context_12_18770_154475 node_context_12_18770_154475
  intro a
  fin_cases a
  · exact context_13_75080_3444
  · exact context_13_75081_154431
  · exact context_13_75082_154458
  · exact context_13_75083_154474

theorem selected_cut_04893 : selected 8 ⟨3444, by decide⟩
    (prefixPartial 13 75084) = some ⟨13, 1, 0, 3444, 75084, 1, 16384⟩ := by
  decide +kernel

theorem context_13_75084_3444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75084 ⟨3444, by decide⟩ :=
  accepted_of_selected 13 75084 ⟨3444, by decide⟩ ⟨13, 1, 0, 3444, 75084, 1, 16384⟩
    (by decide) selected_cut_04893

theorem selected_cut_04894 : selected 8 ⟨154498, by decide⟩
    (prefixPartial 13 75085) = some ⟨13, 2, 0, 154498, 75085, 1725, 16384⟩ := by
  decide +kernel

theorem context_13_75085_154498 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75085 ⟨154498, by decide⟩ :=
  accepted_of_selected 13 75085 ⟨154498, by decide⟩ ⟨13, 2, 0, 154498, 75085, 1725, 16384⟩
    (by decide) selected_cut_04894

theorem selected_cut_04895 : selected 8 ⟨154524, by decide⟩
    (prefixPartial 13 75086) = some ⟨13, 2, 0, 154524, 75086, 2097, 16384⟩ := by
  decide +kernel

theorem context_13_75086_154524 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75086 ⟨154524, by decide⟩ :=
  accepted_of_selected 13 75086 ⟨154524, by decide⟩ ⟨13, 2, 0, 154524, 75086, 2097, 16384⟩
    (by decide) selected_cut_04895

theorem selected_cut_04896 : selected 8 ⟨154534, by decide⟩
    (prefixPartial 13 75087) = some ⟨13, 2, 0, 154534, 75087, 981, 16384⟩ := by
  decide +kernel

theorem context_13_75087_154534 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 13 75087 ⟨154534, by decide⟩ :=
  accepted_of_selected 13 75087 ⟨154534, by decide⟩ ⟨13, 2, 0, 154534, 75087, 981, 16384⟩
    (by decide) selected_cut_04896

theorem unmarked_context_12_18771_154535 : frontier 9 ⟨154535, by decide⟩
    (prefixCache 12 18771) (prefixPartial 12 18771) = false := by
  decide +kernel

theorem node_context_12_18771_154535 : EJMOriginalGlobalDAGData.nodes 9 ⟨154535, by decide⟩ =
    .split (coordinate 12) (![⟨3444, by decide⟩,⟨154498, by decide⟩,⟨154524, by decide⟩,⟨154534, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_12_18771_154535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18771 ⟨154535, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 12 18771
    ⟨154535, by decide⟩ (by decide) (![⟨3444, by decide⟩,⟨154498, by decide⟩,⟨154524, by decide⟩,⟨154534, by decide⟩]) unmarked_context_12_18771_154535 node_context_12_18771_154535
  intro a
  fin_cases a
  · exact context_13_75084_3444
  · exact context_13_75085_154498
  · exact context_13_75086_154524
  · exact context_13_75087_154534

theorem unmarked_context_11_4692_154536 : frontier 10 ⟨154536, by decide⟩
    (prefixCache 11 4692) (prefixPartial 11 4692) = false := by
  decide +kernel

theorem node_context_11_4692_154536 : EJMOriginalGlobalDAGData.nodes 10 ⟨154536, by decide⟩ =
    .split (coordinate 11) (![⟨154338, by decide⟩,⟨154406, by decide⟩,⟨154475, by decide⟩,⟨154535, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_4692_154536 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 4692 ⟨154536, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 4692
    ⟨154536, by decide⟩ (by decide) (![⟨154338, by decide⟩,⟨154406, by decide⟩,⟨154475, by decide⟩,⟨154535, by decide⟩]) unmarked_context_11_4692_154536 node_context_11_4692_154536
  intro a
  fin_cases a
  · exact context_12_18768_154338
  · exact context_12_18769_154406
  · exact context_12_18770_154475
  · exact context_12_18771_154535

theorem selected_cut_04897 : selected 9 ⟨154580, by decide⟩
    (prefixPartial 12 18772) = some ⟨12, 2, 0, 154580, 18772, 3621, 65536⟩ := by
  decide +kernel

theorem context_12_18772_154580 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 18772 ⟨154580, by decide⟩ :=
  accepted_of_selected 12 18772 ⟨154580, by decide⟩ ⟨12, 2, 0, 154580, 18772, 3621, 65536⟩
    (by decide) selected_cut_04897

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
