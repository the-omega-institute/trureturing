/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover510
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_10_25346_1384765 : frontier 11 ⟨1384765, by decide⟩
    (prefixCache 10 25346) (prefixPartial 10 25346) = false := by
  decide +kernel

theorem node_context_10_25346_1384765 : EJMOriginalGlobalDAGData.nodes 11 ⟨1384765, by decide⟩ =
    .split (coordinate 10) (![⟨1384641, by decide⟩,⟨1384702, by decide⟩,⟨479708, by decide⟩,⟨1384764, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25346_1384765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25346 ⟨1384765, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25346
    ⟨1384765, by decide⟩ (by decide) (![⟨1384641, by decide⟩,⟨1384702, by decide⟩,⟨479708, by decide⟩,⟨1384764, by decide⟩]) unmarked_context_10_25346_1384765 node_context_10_25346_1384765
  intro a
  fin_cases a
  · exact context_11_101384_1384641
  · exact context_11_101385_1384702
  · exact context_11_101386_479708
  · exact context_11_101387_1384764

theorem selected_cut_49059 : selected 10 ⟨1384871, by decide⟩
    (prefixPartial 11 101388) = some ⟨11, 2, 0, 1384871, 101388, 3357, 262144⟩ := by
  decide +kernel

theorem context_11_101388_1384871 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101388 ⟨1384871, by decide⟩ :=
  accepted_of_selected 11 101388 ⟨1384871, by decide⟩ ⟨11, 2, 0, 1384871, 101388, 3357, 262144⟩
    (by decide) selected_cut_49059

theorem selected_cut_49060 : selected 10 ⟨1384944, by decide⟩
    (prefixPartial 11 101389) = some ⟨11, 2, 0, 1384944, 101389, 2361, 262144⟩ := by
  decide +kernel

theorem context_11_101389_1384944 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101389 ⟨1384944, by decide⟩ :=
  accepted_of_selected 11 101389 ⟨1384944, by decide⟩ ⟨11, 2, 0, 1384944, 101389, 2361, 262144⟩
    (by decide) selected_cut_49060

theorem selected_cut_49061 : selected 10 ⟨1384994, by decide⟩
    (prefixPartial 11 101390) = some ⟨11, 2, 0, 1384994, 101390, 2165, 262144⟩ := by
  decide +kernel

theorem context_11_101390_1384994 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101390 ⟨1384994, by decide⟩ :=
  accepted_of_selected 11 101390 ⟨1384994, by decide⟩ ⟨11, 2, 0, 1384994, 101390, 2165, 262144⟩
    (by decide) selected_cut_49061

theorem selected_cut_49062 : selected 10 ⟨612961, by decide⟩
    (prefixPartial 11 101391) = some ⟨11, 1, 0, 612961, 101391, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101391_612961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101391 ⟨612961, by decide⟩ :=
  accepted_of_selected 11 101391 ⟨612961, by decide⟩ ⟨11, 1, 0, 612961, 101391, 1, 262144⟩
    (by decide) selected_cut_49062

theorem unmarked_context_10_25347_1384995 : frontier 11 ⟨1384995, by decide⟩
    (prefixCache 10 25347) (prefixPartial 10 25347) = false := by
  decide +kernel

theorem node_context_10_25347_1384995 : EJMOriginalGlobalDAGData.nodes 11 ⟨1384995, by decide⟩ =
    .split (coordinate 10) (![⟨1384871, by decide⟩,⟨1384944, by decide⟩,⟨1384994, by decide⟩,⟨612961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25347_1384995 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25347 ⟨1384995, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25347
    ⟨1384995, by decide⟩ (by decide) (![⟨1384871, by decide⟩,⟨1384944, by decide⟩,⟨1384994, by decide⟩,⟨612961, by decide⟩]) unmarked_context_10_25347_1384995 node_context_10_25347_1384995
  intro a
  fin_cases a
  · exact context_11_101388_1384871
  · exact context_11_101389_1384944
  · exact context_11_101390_1384994
  · exact context_11_101391_612961

theorem unmarked_context_9_6336_1384996 : frontier 12 ⟨1384996, by decide⟩
    (prefixCache 9 6336) (prefixPartial 9 6336) = false := by
  decide +kernel

theorem node_context_9_6336_1384996 : EJMOriginalGlobalDAGData.nodes 12 ⟨1384996, by decide⟩ =
    .split (coordinate 9) (![⟨1384295, by decide⟩,⟨1384552, by decide⟩,⟨1384765, by decide⟩,⟨1384995, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6336_1384996 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6336 ⟨1384996, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6336
    ⟨1384996, by decide⟩ (by decide) (![⟨1384295, by decide⟩,⟨1384552, by decide⟩,⟨1384765, by decide⟩,⟨1384995, by decide⟩]) unmarked_context_9_6336_1384996 node_context_9_6336_1384996
  intro a
  fin_cases a
  · exact context_10_25344_1384295
  · exact context_10_25345_1384552
  · exact context_10_25346_1384765
  · exact context_10_25347_1384995

theorem selected_cut_49063 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 25348) = some ⟨10, 1, 0, 793297, 25348, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25348_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25348 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 25348 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 25348, 1, 1048576⟩
    (by decide) selected_cut_49063

theorem selected_cut_49064 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25349) = some ⟨10, 1, 0, 893098, 25349, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25349_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25349 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25349 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25349, 1, 1048576⟩
    (by decide) selected_cut_49064

theorem selected_cut_49065 : selected 10 ⟨1385074, by decide⟩
    (prefixPartial 11 101400) = some ⟨11, 2, 0, 1385074, 101400, 2021, 262144⟩ := by
  decide +kernel

theorem context_11_101400_1385074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101400 ⟨1385074, by decide⟩ :=
  accepted_of_selected 11 101400 ⟨1385074, by decide⟩ ⟨11, 2, 0, 1385074, 101400, 2021, 262144⟩
    (by decide) selected_cut_49065

theorem selected_cut_49066 : selected 10 ⟨1385151, by decide⟩
    (prefixPartial 11 101401) = some ⟨11, 2, 0, 1385151, 101401, 2873, 262144⟩ := by
  decide +kernel

theorem context_11_101401_1385151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101401 ⟨1385151, by decide⟩ :=
  accepted_of_selected 11 101401 ⟨1385151, by decide⟩ ⟨11, 2, 0, 1385151, 101401, 2873, 262144⟩
    (by decide) selected_cut_49066

theorem selected_cut_49067 : selected 10 ⟨1385179, by decide⟩
    (prefixPartial 11 101402) = some ⟨11, 2, 0, 1385179, 101402, 937, 262144⟩ := by
  decide +kernel

theorem context_11_101402_1385179 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101402 ⟨1385179, by decide⟩ :=
  accepted_of_selected 11 101402 ⟨1385179, by decide⟩ ⟨11, 2, 0, 1385179, 101402, 937, 262144⟩
    (by decide) selected_cut_49067

theorem selected_cut_49068 : selected 10 ⟨1385257, by decide⟩
    (prefixPartial 11 101403) = some ⟨11, 2, 0, 1385257, 101403, 3273, 262144⟩ := by
  decide +kernel

theorem context_11_101403_1385257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101403 ⟨1385257, by decide⟩ :=
  accepted_of_selected 11 101403 ⟨1385257, by decide⟩ ⟨11, 2, 0, 1385257, 101403, 3273, 262144⟩
    (by decide) selected_cut_49068

theorem unmarked_context_10_25350_1385258 : frontier 11 ⟨1385258, by decide⟩
    (prefixCache 10 25350) (prefixPartial 10 25350) = false := by
  decide +kernel

theorem node_context_10_25350_1385258 : EJMOriginalGlobalDAGData.nodes 11 ⟨1385258, by decide⟩ =
    .split (coordinate 10) (![⟨1385074, by decide⟩,⟨1385151, by decide⟩,⟨1385179, by decide⟩,⟨1385257, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25350_1385258 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25350 ⟨1385258, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25350
    ⟨1385258, by decide⟩ (by decide) (![⟨1385074, by decide⟩,⟨1385151, by decide⟩,⟨1385179, by decide⟩,⟨1385257, by decide⟩]) unmarked_context_10_25350_1385258 node_context_10_25350_1385258
  intro a
  fin_cases a
  · exact context_11_101400_1385074
  · exact context_11_101401_1385151
  · exact context_11_101402_1385179
  · exact context_11_101403_1385257

theorem selected_cut_49069 : selected 10 ⟨1385301, by decide⟩
    (prefixPartial 11 101404) = some ⟨11, 2, 0, 1385301, 101404, 1313, 262144⟩ := by
  decide +kernel

theorem context_11_101404_1385301 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101404 ⟨1385301, by decide⟩ :=
  accepted_of_selected 11 101404 ⟨1385301, by decide⟩ ⟨11, 2, 0, 1385301, 101404, 1313, 262144⟩
    (by decide) selected_cut_49069

theorem selected_cut_49070 : selected 10 ⟨1385340, by decide⟩
    (prefixPartial 11 101405) = some ⟨11, 2, 0, 1385340, 101405, 1837, 262144⟩ := by
  decide +kernel

theorem context_11_101405_1385340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101405 ⟨1385340, by decide⟩ :=
  accepted_of_selected 11 101405 ⟨1385340, by decide⟩ ⟨11, 2, 0, 1385340, 101405, 1837, 262144⟩
    (by decide) selected_cut_49070

theorem selected_cut_49071 : selected 10 ⟨1385411, by decide⟩
    (prefixPartial 11 101406) = some ⟨11, 2, 0, 1385411, 101406, 2149, 262144⟩ := by
  decide +kernel

theorem context_11_101406_1385411 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101406 ⟨1385411, by decide⟩ :=
  accepted_of_selected 11 101406 ⟨1385411, by decide⟩ ⟨11, 2, 0, 1385411, 101406, 2149, 262144⟩
    (by decide) selected_cut_49071

theorem selected_cut_49072 : selected 10 ⟨1385422, by decide⟩
    (prefixPartial 11 101407) = some ⟨11, 2, 0, 1385422, 101407, 429, 262144⟩ := by
  decide +kernel

theorem context_11_101407_1385422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101407 ⟨1385422, by decide⟩ :=
  accepted_of_selected 11 101407 ⟨1385422, by decide⟩ ⟨11, 2, 0, 1385422, 101407, 429, 262144⟩
    (by decide) selected_cut_49072

theorem unmarked_context_10_25351_1385423 : frontier 11 ⟨1385423, by decide⟩
    (prefixCache 10 25351) (prefixPartial 10 25351) = false := by
  decide +kernel

theorem node_context_10_25351_1385423 : EJMOriginalGlobalDAGData.nodes 11 ⟨1385423, by decide⟩ =
    .split (coordinate 10) (![⟨1385301, by decide⟩,⟨1385340, by decide⟩,⟨1385411, by decide⟩,⟨1385422, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25351_1385423 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25351 ⟨1385423, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25351
    ⟨1385423, by decide⟩ (by decide) (![⟨1385301, by decide⟩,⟨1385340, by decide⟩,⟨1385411, by decide⟩,⟨1385422, by decide⟩]) unmarked_context_10_25351_1385423 node_context_10_25351_1385423
  intro a
  fin_cases a
  · exact context_11_101404_1385301
  · exact context_11_101405_1385340
  · exact context_11_101406_1385411
  · exact context_11_101407_1385422

theorem unmarked_context_9_6337_1385424 : frontier 12 ⟨1385424, by decide⟩
    (prefixCache 9 6337) (prefixPartial 9 6337) = false := by
  decide +kernel

theorem node_context_9_6337_1385424 : EJMOriginalGlobalDAGData.nodes 12 ⟨1385424, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1385258, by decide⟩,⟨1385423, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6337_1385424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6337 ⟨1385424, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6337
    ⟨1385424, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1385258, by decide⟩,⟨1385423, by decide⟩]) unmarked_context_9_6337_1385424 node_context_9_6337_1385424
  intro a
  fin_cases a
  · exact context_10_25348_793297
  · exact context_10_25349_893098
  · exact context_10_25350_1385258
  · exact context_10_25351_1385423

theorem selected_cut_49073 : selected 12 ⟨1385540, by decide⟩
    (prefixPartial 9 6338) = some ⟨9, 2, 0, 1385540, 6338, 2353, 4194304⟩ := by
  decide +kernel

theorem context_9_6338_1385540 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6338 ⟨1385540, by decide⟩ :=
  accepted_of_selected 9 6338 ⟨1385540, by decide⟩ ⟨9, 2, 0, 1385540, 6338, 2353, 4194304⟩
    (by decide) selected_cut_49073

theorem selected_cut_49074 : selected 12 ⟨1385582, by decide⟩
    (prefixPartial 9 6339) = some ⟨9, 2, 0, 1385582, 6339, 501, 4194304⟩ := by
  decide +kernel

theorem context_9_6339_1385582 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6339 ⟨1385582, by decide⟩ :=
  accepted_of_selected 9 6339 ⟨1385582, by decide⟩ ⟨9, 2, 0, 1385582, 6339, 501, 4194304⟩
    (by decide) selected_cut_49074

theorem unmarked_context_8_1584_1385583 : frontier 13 ⟨1385583, by decide⟩
    (prefixCache 8 1584) (prefixPartial 8 1584) = false := by
  decide +kernel

theorem node_context_8_1584_1385583 : EJMOriginalGlobalDAGData.nodes 13 ⟨1385583, by decide⟩ =
    .split (coordinate 8) (![⟨1384996, by decide⟩,⟨1385424, by decide⟩,⟨1385540, by decide⟩,⟨1385582, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1584_1385583 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1584 ⟨1385583, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1584
    ⟨1385583, by decide⟩ (by decide) (![⟨1384996, by decide⟩,⟨1385424, by decide⟩,⟨1385540, by decide⟩,⟨1385582, by decide⟩]) unmarked_context_8_1584_1385583 node_context_8_1584_1385583
  intro a
  fin_cases a
  · exact context_9_6336_1384996
  · exact context_9_6337_1385424
  · exact context_9_6338_1385540
  · exact context_9_6339_1385582

theorem selected_cut_49075 : selected 11 ⟨1385663, by decide⟩
    (prefixPartial 10 25360) = some ⟨10, 2, 0, 1385663, 25360, 1489, 1048576⟩ := by
  decide +kernel

theorem context_10_25360_1385663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25360 ⟨1385663, by decide⟩ :=
  accepted_of_selected 10 25360 ⟨1385663, by decide⟩ ⟨10, 2, 0, 1385663, 25360, 1489, 1048576⟩
    (by decide) selected_cut_49075

theorem selected_cut_49076 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405776) = some ⟨12, 1, 0, 1108174, 405776, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405776_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405776 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405776 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405776, 1, 65536⟩
    (by decide) selected_cut_49076

theorem selected_cut_49077 : selected 9 ⟨1385706, by decide⟩
    (prefixPartial 12 405777) = some ⟨12, 2, 0, 1385706, 405777, 1581, 65536⟩ := by
  decide +kernel

theorem context_12_405777_1385706 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405777 ⟨1385706, by decide⟩ :=
  accepted_of_selected 12 405777 ⟨1385706, by decide⟩ ⟨12, 2, 0, 1385706, 405777, 1581, 65536⟩
    (by decide) selected_cut_49077

theorem selected_cut_49078 : selected 9 ⟨1385745, by decide⟩
    (prefixPartial 12 405778) = some ⟨12, 2, 0, 1385745, 405778, 1821, 65536⟩ := by
  decide +kernel

theorem context_12_405778_1385745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405778 ⟨1385745, by decide⟩ :=
  accepted_of_selected 12 405778 ⟨1385745, by decide⟩ ⟨12, 2, 0, 1385745, 405778, 1821, 65536⟩
    (by decide) selected_cut_49078

theorem selected_cut_49079 : selected 9 ⟨1385779, by decide⟩
    (prefixPartial 12 405779) = some ⟨12, 2, 0, 1385779, 405779, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_405779_1385779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405779 ⟨1385779, by decide⟩ :=
  accepted_of_selected 12 405779 ⟨1385779, by decide⟩ ⟨12, 2, 0, 1385779, 405779, 1561, 65536⟩
    (by decide) selected_cut_49079

theorem unmarked_context_11_101444_1385780 : frontier 10 ⟨1385780, by decide⟩
    (prefixCache 11 101444) (prefixPartial 11 101444) = false := by
  decide +kernel

theorem node_context_11_101444_1385780 : EJMOriginalGlobalDAGData.nodes 10 ⟨1385780, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1385706, by decide⟩,⟨1385745, by decide⟩,⟨1385779, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101444_1385780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101444 ⟨1385780, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101444
    ⟨1385780, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1385706, by decide⟩,⟨1385745, by decide⟩,⟨1385779, by decide⟩]) unmarked_context_11_101444_1385780 node_context_11_101444_1385780
  intro a
  fin_cases a
  · exact context_12_405776_1108174
  · exact context_12_405777_1385706
  · exact context_12_405778_1385745
  · exact context_12_405779_1385779

theorem selected_cut_49080 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 101445) = some ⟨11, 1, 0, 451541, 101445, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101445_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101445 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 101445 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 101445, 1, 262144⟩
    (by decide) selected_cut_49080

theorem selected_cut_49081 : selected 10 ⟨1385848, by decide⟩
    (prefixPartial 11 101446) = some ⟨11, 2, 0, 1385848, 101446, 2789, 262144⟩ := by
  decide +kernel

theorem context_11_101446_1385848 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101446 ⟨1385848, by decide⟩ :=
  accepted_of_selected 11 101446 ⟨1385848, by decide⟩ ⟨11, 2, 0, 1385848, 101446, 2789, 262144⟩
    (by decide) selected_cut_49081

theorem selected_cut_49082 : selected 10 ⟨1385926, by decide⟩
    (prefixPartial 11 101447) = some ⟨11, 2, 0, 1385926, 101447, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_101447_1385926 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101447 ⟨1385926, by decide⟩ :=
  accepted_of_selected 11 101447 ⟨1385926, by decide⟩ ⟨11, 2, 0, 1385926, 101447, 3233, 262144⟩
    (by decide) selected_cut_49082

theorem unmarked_context_10_25361_1385927 : frontier 11 ⟨1385927, by decide⟩
    (prefixCache 10 25361) (prefixPartial 10 25361) = false := by
  decide +kernel

theorem node_context_10_25361_1385927 : EJMOriginalGlobalDAGData.nodes 11 ⟨1385927, by decide⟩ =
    .split (coordinate 10) (![⟨1385780, by decide⟩,⟨451541, by decide⟩,⟨1385848, by decide⟩,⟨1385926, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25361_1385927 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25361 ⟨1385927, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25361
    ⟨1385927, by decide⟩ (by decide) (![⟨1385780, by decide⟩,⟨451541, by decide⟩,⟨1385848, by decide⟩,⟨1385926, by decide⟩]) unmarked_context_10_25361_1385927 node_context_10_25361_1385927
  intro a
  fin_cases a
  · exact context_11_101444_1385780
  · exact context_11_101445_451541
  · exact context_11_101446_1385848
  · exact context_11_101447_1385926

theorem selected_cut_49083 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405792) = some ⟨12, 1, 0, 1108174, 405792, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405792_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405792 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405792 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405792, 1, 65536⟩
    (by decide) selected_cut_49083

theorem selected_cut_49084 : selected 9 ⟨1385963, by decide⟩
    (prefixPartial 12 405793) = some ⟨12, 2, 0, 1385963, 405793, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_405793_1385963 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405793 ⟨1385963, by decide⟩ :=
  accepted_of_selected 12 405793 ⟨1385963, by decide⟩ ⟨12, 2, 0, 1385963, 405793, 1477, 65536⟩
    (by decide) selected_cut_49084

theorem selected_cut_49085 : selected 9 ⟨1386010, by decide⟩
    (prefixPartial 12 405794) = some ⟨12, 2, 0, 1386010, 405794, 1653, 65536⟩ := by
  decide +kernel

theorem context_12_405794_1386010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405794 ⟨1386010, by decide⟩ :=
  accepted_of_selected 12 405794 ⟨1386010, by decide⟩ ⟨12, 2, 0, 1386010, 405794, 1653, 65536⟩
    (by decide) selected_cut_49085

theorem selected_cut_49086 : selected 9 ⟨1386033, by decide⟩
    (prefixPartial 12 405795) = some ⟨12, 2, 0, 1386033, 405795, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_405795_1386033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405795 ⟨1386033, by decide⟩ :=
  accepted_of_selected 12 405795 ⟨1386033, by decide⟩ ⟨12, 2, 0, 1386033, 405795, 1369, 65536⟩
    (by decide) selected_cut_49086

theorem unmarked_context_11_101448_1386034 : frontier 10 ⟨1386034, by decide⟩
    (prefixCache 11 101448) (prefixPartial 11 101448) = false := by
  decide +kernel

theorem node_context_11_101448_1386034 : EJMOriginalGlobalDAGData.nodes 10 ⟨1386034, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1385963, by decide⟩,⟨1386010, by decide⟩,⟨1386033, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101448_1386034 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101448 ⟨1386034, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101448
    ⟨1386034, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1385963, by decide⟩,⟨1386010, by decide⟩,⟨1386033, by decide⟩]) unmarked_context_11_101448_1386034 node_context_11_101448_1386034
  intro a
  fin_cases a
  · exact context_12_405792_1108174
  · exact context_12_405793_1385963
  · exact context_12_405794_1386010
  · exact context_12_405795_1386033

theorem selected_cut_49087 : selected 10 ⟨1386101, by decide⟩
    (prefixPartial 11 101449) = some ⟨11, 2, 0, 1386101, 101449, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_101449_1386101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101449 ⟨1386101, by decide⟩ :=
  accepted_of_selected 11 101449 ⟨1386101, by decide⟩ ⟨11, 2, 0, 1386101, 101449, 2857, 262144⟩
    (by decide) selected_cut_49087

theorem selected_cut_49088 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 101450) = some ⟨11, 1, 0, 479708, 101450, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101450_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101450 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 101450 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 101450, 1, 262144⟩
    (by decide) selected_cut_49088

theorem selected_cut_49089 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 405804) = some ⟨12, 1, 0, 1108174, 405804, 1, 65536⟩ := by
  decide +kernel

theorem context_12_405804_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405804 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 405804 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 405804, 1, 65536⟩
    (by decide) selected_cut_49089

theorem selected_cut_49090 : selected 9 ⟨1386133, by decide⟩
    (prefixPartial 12 405805) = some ⟨12, 2, 0, 1386133, 405805, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_405805_1386133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405805 ⟨1386133, by decide⟩ :=
  accepted_of_selected 12 405805 ⟨1386133, by decide⟩ ⟨12, 2, 0, 1386133, 405805, 1385, 65536⟩
    (by decide) selected_cut_49090

theorem selected_cut_49091 : selected 9 ⟨1386172, by decide⟩
    (prefixPartial 12 405806) = some ⟨12, 2, 0, 1386172, 405806, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_405806_1386172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405806 ⟨1386172, by decide⟩ :=
  accepted_of_selected 12 405806 ⟨1386172, by decide⟩ ⟨12, 2, 0, 1386172, 405806, 1561, 65536⟩
    (by decide) selected_cut_49091

theorem selected_cut_49092 : selected 9 ⟨1386197, by decide⟩
    (prefixPartial 12 405807) = some ⟨12, 2, 0, 1386197, 405807, 1293, 65536⟩ := by
  decide +kernel

theorem context_12_405807_1386197 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 405807 ⟨1386197, by decide⟩ :=
  accepted_of_selected 12 405807 ⟨1386197, by decide⟩ ⟨12, 2, 0, 1386197, 405807, 1293, 65536⟩
    (by decide) selected_cut_49092

theorem unmarked_context_11_101451_1386198 : frontier 10 ⟨1386198, by decide⟩
    (prefixCache 11 101451) (prefixPartial 11 101451) = false := by
  decide +kernel

theorem node_context_11_101451_1386198 : EJMOriginalGlobalDAGData.nodes 10 ⟨1386198, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1386133, by decide⟩,⟨1386172, by decide⟩,⟨1386197, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101451_1386198 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101451 ⟨1386198, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101451
    ⟨1386198, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1386133, by decide⟩,⟨1386172, by decide⟩,⟨1386197, by decide⟩]) unmarked_context_11_101451_1386198 node_context_11_101451_1386198
  intro a
  fin_cases a
  · exact context_12_405804_1108174
  · exact context_12_405805_1386133
  · exact context_12_405806_1386172
  · exact context_12_405807_1386197

theorem unmarked_context_10_25362_1386199 : frontier 11 ⟨1386199, by decide⟩
    (prefixCache 10 25362) (prefixPartial 10 25362) = false := by
  decide +kernel

theorem node_context_10_25362_1386199 : EJMOriginalGlobalDAGData.nodes 11 ⟨1386199, by decide⟩ =
    .split (coordinate 10) (![⟨1386034, by decide⟩,⟨1386101, by decide⟩,⟨479708, by decide⟩,⟨1386198, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25362_1386199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25362 ⟨1386199, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25362
    ⟨1386199, by decide⟩ (by decide) (![⟨1386034, by decide⟩,⟨1386101, by decide⟩,⟨479708, by decide⟩,⟨1386198, by decide⟩]) unmarked_context_10_25362_1386199 node_context_10_25362_1386199
  intro a
  fin_cases a
  · exact context_11_101448_1386034
  · exact context_11_101449_1386101
  · exact context_11_101450_479708
  · exact context_11_101451_1386198

theorem selected_cut_49093 : selected 10 ⟨1386313, by decide⟩
    (prefixPartial 11 101452) = some ⟨11, 2, 0, 1386313, 101452, 3425, 262144⟩ := by
  decide +kernel

theorem context_11_101452_1386313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101452 ⟨1386313, by decide⟩ :=
  accepted_of_selected 11 101452 ⟨1386313, by decide⟩ ⟨11, 2, 0, 1386313, 101452, 3425, 262144⟩
    (by decide) selected_cut_49093

theorem selected_cut_49094 : selected 10 ⟨1386374, by decide⟩
    (prefixPartial 11 101453) = some ⟨11, 2, 0, 1386374, 101453, 2237, 262144⟩ := by
  decide +kernel

theorem context_11_101453_1386374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101453 ⟨1386374, by decide⟩ :=
  accepted_of_selected 11 101453 ⟨1386374, by decide⟩ ⟨11, 2, 0, 1386374, 101453, 2237, 262144⟩
    (by decide) selected_cut_49094

theorem selected_cut_49095 : selected 10 ⟨1386443, by decide⟩
    (prefixPartial 11 101454) = some ⟨11, 2, 0, 1386443, 101454, 2893, 262144⟩ := by
  decide +kernel

theorem context_11_101454_1386443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101454 ⟨1386443, by decide⟩ :=
  accepted_of_selected 11 101454 ⟨1386443, by decide⟩ ⟨11, 2, 0, 1386443, 101454, 2893, 262144⟩
    (by decide) selected_cut_49095

theorem selected_cut_49096 : selected 10 ⟨612961, by decide⟩
    (prefixPartial 11 101455) = some ⟨11, 1, 0, 612961, 101455, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101455_612961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101455 ⟨612961, by decide⟩ :=
  accepted_of_selected 11 101455 ⟨612961, by decide⟩ ⟨11, 1, 0, 612961, 101455, 1, 262144⟩
    (by decide) selected_cut_49096

theorem unmarked_context_10_25363_1386444 : frontier 11 ⟨1386444, by decide⟩
    (prefixCache 10 25363) (prefixPartial 10 25363) = false := by
  decide +kernel

theorem node_context_10_25363_1386444 : EJMOriginalGlobalDAGData.nodes 11 ⟨1386444, by decide⟩ =
    .split (coordinate 10) (![⟨1386313, by decide⟩,⟨1386374, by decide⟩,⟨1386443, by decide⟩,⟨612961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25363_1386444 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25363 ⟨1386444, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25363
    ⟨1386444, by decide⟩ (by decide) (![⟨1386313, by decide⟩,⟨1386374, by decide⟩,⟨1386443, by decide⟩,⟨612961, by decide⟩]) unmarked_context_10_25363_1386444 node_context_10_25363_1386444
  intro a
  fin_cases a
  · exact context_11_101452_1386313
  · exact context_11_101453_1386374
  · exact context_11_101454_1386443
  · exact context_11_101455_612961

theorem unmarked_context_9_6340_1386445 : frontier 12 ⟨1386445, by decide⟩
    (prefixCache 9 6340) (prefixPartial 9 6340) = false := by
  decide +kernel

theorem node_context_9_6340_1386445 : EJMOriginalGlobalDAGData.nodes 12 ⟨1386445, by decide⟩ =
    .split (coordinate 9) (![⟨1385663, by decide⟩,⟨1385927, by decide⟩,⟨1386199, by decide⟩,⟨1386444, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6340_1386445 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6340 ⟨1386445, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6340
    ⟨1386445, by decide⟩ (by decide) (![⟨1385663, by decide⟩,⟨1385927, by decide⟩,⟨1386199, by decide⟩,⟨1386444, by decide⟩]) unmarked_context_9_6340_1386445 node_context_9_6340_1386445
  intro a
  fin_cases a
  · exact context_10_25360_1385663
  · exact context_10_25361_1385927
  · exact context_10_25362_1386199
  · exact context_10_25363_1386444

theorem selected_cut_49097 : selected 11 ⟨793297, by decide⟩
    (prefixPartial 10 25364) = some ⟨10, 1, 0, 793297, 25364, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25364_793297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25364 ⟨793297, by decide⟩ :=
  accepted_of_selected 10 25364 ⟨793297, by decide⟩ ⟨10, 1, 0, 793297, 25364, 1, 1048576⟩
    (by decide) selected_cut_49097

theorem selected_cut_49098 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25365) = some ⟨10, 1, 0, 893098, 25365, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25365_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25365 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25365 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25365, 1, 1048576⟩
    (by decide) selected_cut_49098

theorem selected_cut_49099 : selected 10 ⟨1386507, by decide⟩
    (prefixPartial 11 101464) = some ⟨11, 2, 0, 1386507, 101464, 1873, 262144⟩ := by
  decide +kernel

theorem context_11_101464_1386507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101464 ⟨1386507, by decide⟩ :=
  accepted_of_selected 11 101464 ⟨1386507, by decide⟩ ⟨11, 2, 0, 1386507, 101464, 1873, 262144⟩
    (by decide) selected_cut_49099

theorem selected_cut_49100 : selected 10 ⟨1386590, by decide⟩
    (prefixPartial 11 101465) = some ⟨11, 2, 0, 1386590, 101465, 2485, 262144⟩ := by
  decide +kernel

theorem context_11_101465_1386590 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101465 ⟨1386590, by decide⟩ :=
  accepted_of_selected 11 101465 ⟨1386590, by decide⟩ ⟨11, 2, 0, 1386590, 101465, 2485, 262144⟩
    (by decide) selected_cut_49100

theorem selected_cut_49101 : selected 10 ⟨1386621, by decide⟩
    (prefixPartial 11 101466) = some ⟨11, 2, 0, 1386621, 101466, 881, 262144⟩ := by
  decide +kernel

theorem context_11_101466_1386621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101466 ⟨1386621, by decide⟩ :=
  accepted_of_selected 11 101466 ⟨1386621, by decide⟩ ⟨11, 2, 0, 1386621, 101466, 881, 262144⟩
    (by decide) selected_cut_49101

theorem selected_cut_49102 : selected 10 ⟨1386696, by decide⟩
    (prefixPartial 11 101467) = some ⟨11, 2, 0, 1386696, 101467, 1909, 262144⟩ := by
  decide +kernel

theorem context_11_101467_1386696 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101467 ⟨1386696, by decide⟩ :=
  accepted_of_selected 11 101467 ⟨1386696, by decide⟩ ⟨11, 2, 0, 1386696, 101467, 1909, 262144⟩
    (by decide) selected_cut_49102

theorem unmarked_context_10_25366_1386697 : frontier 11 ⟨1386697, by decide⟩
    (prefixCache 10 25366) (prefixPartial 10 25366) = false := by
  decide +kernel

theorem node_context_10_25366_1386697 : EJMOriginalGlobalDAGData.nodes 11 ⟨1386697, by decide⟩ =
    .split (coordinate 10) (![⟨1386507, by decide⟩,⟨1386590, by decide⟩,⟨1386621, by decide⟩,⟨1386696, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25366_1386697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25366 ⟨1386697, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25366
    ⟨1386697, by decide⟩ (by decide) (![⟨1386507, by decide⟩,⟨1386590, by decide⟩,⟨1386621, by decide⟩,⟨1386696, by decide⟩]) unmarked_context_10_25366_1386697 node_context_10_25366_1386697
  intro a
  fin_cases a
  · exact context_11_101464_1386507
  · exact context_11_101465_1386590
  · exact context_11_101466_1386621
  · exact context_11_101467_1386696

theorem selected_cut_49103 : selected 10 ⟨1386733, by decide⟩
    (prefixPartial 11 101468) = some ⟨11, 2, 0, 1386733, 101468, 1189, 262144⟩ := by
  decide +kernel

theorem context_11_101468_1386733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101468 ⟨1386733, by decide⟩ :=
  accepted_of_selected 11 101468 ⟨1386733, by decide⟩ ⟨11, 2, 0, 1386733, 101468, 1189, 262144⟩
    (by decide) selected_cut_49103

theorem selected_cut_49104 : selected 10 ⟨1386791, by decide⟩
    (prefixPartial 11 101469) = some ⟨11, 2, 0, 1386791, 101469, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_101469_1386791 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101469 ⟨1386791, by decide⟩ :=
  accepted_of_selected 11 101469 ⟨1386791, by decide⟩ ⟨11, 2, 0, 1386791, 101469, 1717, 262144⟩
    (by decide) selected_cut_49104

theorem selected_cut_49105 : selected 10 ⟨1386836, by decide⟩
    (prefixPartial 11 101470) = some ⟨11, 2, 0, 1386836, 101470, 1213, 262144⟩ := by
  decide +kernel

theorem context_11_101470_1386836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101470 ⟨1386836, by decide⟩ :=
  accepted_of_selected 11 101470 ⟨1386836, by decide⟩ ⟨11, 2, 0, 1386836, 101470, 1213, 262144⟩
    (by decide) selected_cut_49105

theorem selected_cut_49106 : selected 10 ⟨1386850, by decide⟩
    (prefixPartial 11 101471) = some ⟨11, 2, 0, 1386850, 101471, 453, 262144⟩ := by
  decide +kernel

theorem context_11_101471_1386850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101471 ⟨1386850, by decide⟩ :=
  accepted_of_selected 11 101471 ⟨1386850, by decide⟩ ⟨11, 2, 0, 1386850, 101471, 453, 262144⟩
    (by decide) selected_cut_49106

theorem unmarked_context_10_25367_1386851 : frontier 11 ⟨1386851, by decide⟩
    (prefixCache 10 25367) (prefixPartial 10 25367) = false := by
  decide +kernel

theorem node_context_10_25367_1386851 : EJMOriginalGlobalDAGData.nodes 11 ⟨1386851, by decide⟩ =
    .split (coordinate 10) (![⟨1386733, by decide⟩,⟨1386791, by decide⟩,⟨1386836, by decide⟩,⟨1386850, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25367_1386851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25367 ⟨1386851, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25367
    ⟨1386851, by decide⟩ (by decide) (![⟨1386733, by decide⟩,⟨1386791, by decide⟩,⟨1386836, by decide⟩,⟨1386850, by decide⟩]) unmarked_context_10_25367_1386851 node_context_10_25367_1386851
  intro a
  fin_cases a
  · exact context_11_101468_1386733
  · exact context_11_101469_1386791
  · exact context_11_101470_1386836
  · exact context_11_101471_1386850

theorem unmarked_context_9_6341_1386852 : frontier 12 ⟨1386852, by decide⟩
    (prefixCache 9 6341) (prefixPartial 9 6341) = false := by
  decide +kernel

theorem node_context_9_6341_1386852 : EJMOriginalGlobalDAGData.nodes 12 ⟨1386852, by decide⟩ =
    .split (coordinate 9) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1386697, by decide⟩,⟨1386851, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6341_1386852 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6341 ⟨1386852, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6341
    ⟨1386852, by decide⟩ (by decide) (![⟨793297, by decide⟩,⟨893098, by decide⟩,⟨1386697, by decide⟩,⟨1386851, by decide⟩]) unmarked_context_9_6341_1386852 node_context_9_6341_1386852
  intro a
  fin_cases a
  · exact context_10_25364_793297
  · exact context_10_25365_893098
  · exact context_10_25366_1386697
  · exact context_10_25367_1386851

theorem selected_cut_49107 : selected 12 ⟨1386941, by decide⟩
    (prefixPartial 9 6342) = some ⟨9, 2, 0, 1386941, 6342, 2069, 4194304⟩ := by
  decide +kernel

theorem context_9_6342_1386941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6342 ⟨1386941, by decide⟩ :=
  accepted_of_selected 9 6342 ⟨1386941, by decide⟩ ⟨9, 2, 0, 1386941, 6342, 2069, 4194304⟩
    (by decide) selected_cut_49107

theorem selected_cut_49108 : selected 12 ⟨1386968, by decide⟩
    (prefixPartial 9 6343) = some ⟨9, 2, 0, 1386968, 6343, 473, 4194304⟩ := by
  decide +kernel

theorem context_9_6343_1386968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6343 ⟨1386968, by decide⟩ :=
  accepted_of_selected 9 6343 ⟨1386968, by decide⟩ ⟨9, 2, 0, 1386968, 6343, 473, 4194304⟩
    (by decide) selected_cut_49108

theorem unmarked_context_8_1585_1386969 : frontier 13 ⟨1386969, by decide⟩
    (prefixCache 8 1585) (prefixPartial 8 1585) = false := by
  decide +kernel

theorem node_context_8_1585_1386969 : EJMOriginalGlobalDAGData.nodes 13 ⟨1386969, by decide⟩ =
    .split (coordinate 8) (![⟨1386445, by decide⟩,⟨1386852, by decide⟩,⟨1386941, by decide⟩,⟨1386968, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1585_1386969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1585 ⟨1386969, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1585
    ⟨1386969, by decide⟩ (by decide) (![⟨1386445, by decide⟩,⟨1386852, by decide⟩,⟨1386941, by decide⟩,⟨1386968, by decide⟩]) unmarked_context_8_1585_1386969 node_context_8_1585_1386969
  intro a
  fin_cases a
  · exact context_9_6340_1386445
  · exact context_9_6341_1386852
  · exact context_9_6342_1386941
  · exact context_9_6343_1386968

theorem selected_cut_49109 : selected 11 ⟨1387098, by decide⟩
    (prefixPartial 10 25376) = some ⟨10, 2, 0, 1387098, 25376, 3297, 1048576⟩ := by
  decide +kernel

theorem context_10_25376_1387098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25376 ⟨1387098, by decide⟩ :=
  accepted_of_selected 10 25376 ⟨1387098, by decide⟩ ⟨10, 2, 0, 1387098, 25376, 3297, 1048576⟩
    (by decide) selected_cut_49109

theorem selected_cut_49110 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406032) = some ⟨12, 1, 0, 1108174, 406032, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406032_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406032 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406032 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406032, 1, 65536⟩
    (by decide) selected_cut_49110

theorem selected_cut_49111 : selected 9 ⟨1387151, by decide⟩
    (prefixPartial 12 406033) = some ⟨12, 2, 0, 1387151, 406033, 1985, 65536⟩ := by
  decide +kernel

theorem context_12_406033_1387151 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406033 ⟨1387151, by decide⟩ :=
  accepted_of_selected 12 406033 ⟨1387151, by decide⟩ ⟨12, 2, 0, 1387151, 406033, 1985, 65536⟩
    (by decide) selected_cut_49111

theorem selected_cut_49112 : selected 9 ⟨1387204, by decide⟩
    (prefixPartial 12 406034) = some ⟨12, 2, 0, 1387204, 406034, 2057, 65536⟩ := by
  decide +kernel

theorem context_12_406034_1387204 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406034 ⟨1387204, by decide⟩ :=
  accepted_of_selected 12 406034 ⟨1387204, by decide⟩ ⟨12, 2, 0, 1387204, 406034, 2057, 65536⟩
    (by decide) selected_cut_49112

theorem selected_cut_49113 : selected 9 ⟨1387244, by decide⟩
    (prefixPartial 12 406035) = some ⟨12, 2, 0, 1387244, 406035, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_406035_1387244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406035 ⟨1387244, by decide⟩ :=
  accepted_of_selected 12 406035 ⟨1387244, by decide⟩ ⟨12, 2, 0, 1387244, 406035, 1765, 65536⟩
    (by decide) selected_cut_49113

theorem unmarked_context_11_101508_1387245 : frontier 10 ⟨1387245, by decide⟩
    (prefixCache 11 101508) (prefixPartial 11 101508) = false := by
  decide +kernel

theorem node_context_11_101508_1387245 : EJMOriginalGlobalDAGData.nodes 10 ⟨1387245, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1387151, by decide⟩,⟨1387204, by decide⟩,⟨1387244, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101508_1387245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101508 ⟨1387245, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101508
    ⟨1387245, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1387151, by decide⟩,⟨1387204, by decide⟩,⟨1387244, by decide⟩]) unmarked_context_11_101508_1387245 node_context_11_101508_1387245
  intro a
  fin_cases a
  · exact context_12_406032_1108174
  · exact context_12_406033_1387151
  · exact context_12_406034_1387204
  · exact context_12_406035_1387244

theorem selected_cut_49114 : selected 10 ⟨451541, by decide⟩
    (prefixPartial 11 101509) = some ⟨11, 1, 0, 451541, 101509, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101509_451541 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101509 ⟨451541, by decide⟩ :=
  accepted_of_selected 11 101509 ⟨451541, by decide⟩ ⟨11, 1, 0, 451541, 101509, 1, 262144⟩
    (by decide) selected_cut_49114

theorem selected_cut_49115 : selected 10 ⟨1387319, by decide⟩
    (prefixPartial 11 101510) = some ⟨11, 2, 0, 1387319, 101510, 3169, 262144⟩ := by
  decide +kernel

theorem context_11_101510_1387319 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101510 ⟨1387319, by decide⟩ :=
  accepted_of_selected 11 101510 ⟨1387319, by decide⟩ ⟨11, 2, 0, 1387319, 101510, 3169, 262144⟩
    (by decide) selected_cut_49115

theorem selected_cut_49116 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406044) = some ⟨12, 1, 0, 1108174, 406044, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406044_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406044 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406044 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406044, 1, 65536⟩
    (by decide) selected_cut_49116

theorem selected_cut_49117 : selected 9 ⟨1387365, by decide⟩
    (prefixPartial 12 406045) = some ⟨12, 2, 0, 1387365, 406045, 1913, 65536⟩ := by
  decide +kernel

theorem context_12_406045_1387365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406045 ⟨1387365, by decide⟩ :=
  accepted_of_selected 12 406045 ⟨1387365, by decide⟩ ⟨12, 2, 0, 1387365, 406045, 1913, 65536⟩
    (by decide) selected_cut_49117

theorem selected_cut_49118 : selected 9 ⟨1387424, by decide⟩
    (prefixPartial 12 406046) = some ⟨12, 2, 0, 1387424, 406046, 2193, 65536⟩ := by
  decide +kernel

theorem context_12_406046_1387424 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406046 ⟨1387424, by decide⟩ :=
  accepted_of_selected 12 406046 ⟨1387424, by decide⟩ ⟨12, 2, 0, 1387424, 406046, 2193, 65536⟩
    (by decide) selected_cut_49118

theorem selected_cut_49119 : selected 9 ⟨1387459, by decide⟩
    (prefixPartial 12 406047) = some ⟨12, 2, 0, 1387459, 406047, 1617, 65536⟩ := by
  decide +kernel

theorem context_12_406047_1387459 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406047 ⟨1387459, by decide⟩ :=
  accepted_of_selected 12 406047 ⟨1387459, by decide⟩ ⟨12, 2, 0, 1387459, 406047, 1617, 65536⟩
    (by decide) selected_cut_49119

theorem unmarked_context_11_101511_1387460 : frontier 10 ⟨1387460, by decide⟩
    (prefixCache 11 101511) (prefixPartial 11 101511) = false := by
  decide +kernel

theorem node_context_11_101511_1387460 : EJMOriginalGlobalDAGData.nodes 10 ⟨1387460, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1387365, by decide⟩,⟨1387424, by decide⟩,⟨1387459, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101511_1387460 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101511 ⟨1387460, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101511
    ⟨1387460, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1387365, by decide⟩,⟨1387424, by decide⟩,⟨1387459, by decide⟩]) unmarked_context_11_101511_1387460 node_context_11_101511_1387460
  intro a
  fin_cases a
  · exact context_12_406044_1108174
  · exact context_12_406045_1387365
  · exact context_12_406046_1387424
  · exact context_12_406047_1387459

theorem unmarked_context_10_25377_1387461 : frontier 11 ⟨1387461, by decide⟩
    (prefixCache 10 25377) (prefixPartial 10 25377) = false := by
  decide +kernel

theorem node_context_10_25377_1387461 : EJMOriginalGlobalDAGData.nodes 11 ⟨1387461, by decide⟩ =
    .split (coordinate 10) (![⟨1387245, by decide⟩,⟨451541, by decide⟩,⟨1387319, by decide⟩,⟨1387460, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25377_1387461 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25377 ⟨1387461, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25377
    ⟨1387461, by decide⟩ (by decide) (![⟨1387245, by decide⟩,⟨451541, by decide⟩,⟨1387319, by decide⟩,⟨1387460, by decide⟩]) unmarked_context_10_25377_1387461 node_context_10_25377_1387461
  intro a
  fin_cases a
  · exact context_11_101508_1387245
  · exact context_11_101509_451541
  · exact context_11_101510_1387319
  · exact context_11_101511_1387460

theorem selected_cut_49120 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406048) = some ⟨12, 1, 0, 1108174, 406048, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406048_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406048 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406048 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406048, 1, 65536⟩
    (by decide) selected_cut_49120

theorem selected_cut_49121 : selected 9 ⟨1387494, by decide⟩
    (prefixPartial 12 406049) = some ⟨12, 2, 0, 1387494, 406049, 1809, 65536⟩ := by
  decide +kernel

theorem context_12_406049_1387494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406049 ⟨1387494, by decide⟩ :=
  accepted_of_selected 12 406049 ⟨1387494, by decide⟩ ⟨12, 2, 0, 1387494, 406049, 1809, 65536⟩
    (by decide) selected_cut_49121

theorem selected_cut_49122 : selected 9 ⟨1387535, by decide⟩
    (prefixPartial 12 406050) = some ⟨12, 2, 0, 1387535, 406050, 1813, 65536⟩ := by
  decide +kernel

theorem context_12_406050_1387535 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406050 ⟨1387535, by decide⟩ :=
  accepted_of_selected 12 406050 ⟨1387535, by decide⟩ ⟨12, 2, 0, 1387535, 406050, 1813, 65536⟩
    (by decide) selected_cut_49122

theorem selected_cut_49123 : selected 9 ⟨1387563, by decide⟩
    (prefixPartial 12 406051) = some ⟨12, 2, 0, 1387563, 406051, 1533, 65536⟩ := by
  decide +kernel

theorem context_12_406051_1387563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406051 ⟨1387563, by decide⟩ :=
  accepted_of_selected 12 406051 ⟨1387563, by decide⟩ ⟨12, 2, 0, 1387563, 406051, 1533, 65536⟩
    (by decide) selected_cut_49123

theorem unmarked_context_11_101512_1387564 : frontier 10 ⟨1387564, by decide⟩
    (prefixCache 11 101512) (prefixPartial 11 101512) = false := by
  decide +kernel

theorem node_context_11_101512_1387564 : EJMOriginalGlobalDAGData.nodes 10 ⟨1387564, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1387494, by decide⟩,⟨1387535, by decide⟩,⟨1387563, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101512_1387564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101512 ⟨1387564, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101512
    ⟨1387564, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1387494, by decide⟩,⟨1387535, by decide⟩,⟨1387563, by decide⟩]) unmarked_context_11_101512_1387564 node_context_11_101512_1387564
  intro a
  fin_cases a
  · exact context_12_406048_1108174
  · exact context_12_406049_1387494
  · exact context_12_406050_1387535
  · exact context_12_406051_1387563

theorem selected_cut_49124 : selected 10 ⟨1387639, by decide⟩
    (prefixPartial 11 101513) = some ⟨11, 2, 0, 1387639, 101513, 3205, 262144⟩ := by
  decide +kernel

theorem context_11_101513_1387639 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101513 ⟨1387639, by decide⟩ :=
  accepted_of_selected 11 101513 ⟨1387639, by decide⟩ ⟨11, 2, 0, 1387639, 101513, 3205, 262144⟩
    (by decide) selected_cut_49124

theorem selected_cut_49125 : selected 10 ⟨479708, by decide⟩
    (prefixPartial 11 101514) = some ⟨11, 1, 0, 479708, 101514, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101514_479708 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101514 ⟨479708, by decide⟩ :=
  accepted_of_selected 11 101514 ⟨479708, by decide⟩ ⟨11, 1, 0, 479708, 101514, 1, 262144⟩
    (by decide) selected_cut_49125

theorem selected_cut_49126 : selected 10 ⟨1387723, by decide⟩
    (prefixPartial 11 101515) = some ⟨11, 2, 0, 1387723, 101515, 3493, 262144⟩ := by
  decide +kernel

theorem context_11_101515_1387723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101515 ⟨1387723, by decide⟩ :=
  accepted_of_selected 11 101515 ⟨1387723, by decide⟩ ⟨11, 2, 0, 1387723, 101515, 3493, 262144⟩
    (by decide) selected_cut_49126

theorem unmarked_context_10_25378_1387724 : frontier 11 ⟨1387724, by decide⟩
    (prefixCache 10 25378) (prefixPartial 10 25378) = false := by
  decide +kernel

theorem node_context_10_25378_1387724 : EJMOriginalGlobalDAGData.nodes 11 ⟨1387724, by decide⟩ =
    .split (coordinate 10) (![⟨1387564, by decide⟩,⟨1387639, by decide⟩,⟨479708, by decide⟩,⟨1387723, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25378_1387724 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25378 ⟨1387724, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25378
    ⟨1387724, by decide⟩ (by decide) (![⟨1387564, by decide⟩,⟨1387639, by decide⟩,⟨479708, by decide⟩,⟨1387723, by decide⟩]) unmarked_context_10_25378_1387724 node_context_10_25378_1387724
  intro a
  fin_cases a
  · exact context_11_101512_1387564
  · exact context_11_101513_1387639
  · exact context_11_101514_479708
  · exact context_11_101515_1387723

theorem selected_cut_49127 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 406064) = some ⟨12, 1, 0, 1108174, 406064, 1, 65536⟩ := by
  decide +kernel

theorem context_12_406064_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406064 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 406064 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 406064, 1, 65536⟩
    (by decide) selected_cut_49127

theorem selected_cut_49128 : selected 9 ⟨1387748, by decide⟩
    (prefixPartial 12 406065) = some ⟨12, 2, 0, 1387748, 406065, 1417, 65536⟩ := by
  decide +kernel

theorem context_12_406065_1387748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406065 ⟨1387748, by decide⟩ :=
  accepted_of_selected 12 406065 ⟨1387748, by decide⟩ ⟨12, 2, 0, 1387748, 406065, 1417, 65536⟩
    (by decide) selected_cut_49128

theorem selected_cut_49129 : selected 9 ⟨1387779, by decide⟩
    (prefixPartial 12 406066) = some ⟨12, 2, 0, 1387779, 406066, 1385, 65536⟩ := by
  decide +kernel

theorem context_12_406066_1387779 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406066 ⟨1387779, by decide⟩ :=
  accepted_of_selected 12 406066 ⟨1387779, by decide⟩ ⟨12, 2, 0, 1387779, 406066, 1385, 65536⟩
    (by decide) selected_cut_49129

theorem selected_cut_49130 : selected 9 ⟨1387807, by decide⟩
    (prefixPartial 12 406067) = some ⟨12, 2, 0, 1387807, 406067, 1301, 65536⟩ := by
  decide +kernel

theorem context_12_406067_1387807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 406067 ⟨1387807, by decide⟩ :=
  accepted_of_selected 12 406067 ⟨1387807, by decide⟩ ⟨12, 2, 0, 1387807, 406067, 1301, 65536⟩
    (by decide) selected_cut_49130

theorem unmarked_context_11_101516_1387808 : frontier 10 ⟨1387808, by decide⟩
    (prefixCache 11 101516) (prefixPartial 11 101516) = false := by
  decide +kernel

theorem node_context_11_101516_1387808 : EJMOriginalGlobalDAGData.nodes 10 ⟨1387808, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1387748, by decide⟩,⟨1387779, by decide⟩,⟨1387807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101516_1387808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101516 ⟨1387808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101516
    ⟨1387808, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1387748, by decide⟩,⟨1387779, by decide⟩,⟨1387807, by decide⟩]) unmarked_context_11_101516_1387808 node_context_11_101516_1387808
  intro a
  fin_cases a
  · exact context_12_406064_1108174
  · exact context_12_406065_1387748
  · exact context_12_406066_1387779
  · exact context_12_406067_1387807

theorem selected_cut_49131 : selected 10 ⟨1387888, by decide⟩
    (prefixPartial 11 101517) = some ⟨11, 2, 0, 1387888, 101517, 3817, 262144⟩ := by
  decide +kernel

theorem context_11_101517_1387888 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101517 ⟨1387888, by decide⟩ :=
  accepted_of_selected 11 101517 ⟨1387888, by decide⟩ ⟨11, 2, 0, 1387888, 101517, 3817, 262144⟩
    (by decide) selected_cut_49131

theorem selected_cut_49132 : selected 10 ⟨1387935, by decide⟩
    (prefixPartial 11 101518) = some ⟨11, 2, 0, 1387935, 101518, 2245, 262144⟩ := by
  decide +kernel

theorem context_11_101518_1387935 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101518 ⟨1387935, by decide⟩ :=
  accepted_of_selected 11 101518 ⟨1387935, by decide⟩ ⟨11, 2, 0, 1387935, 101518, 2245, 262144⟩
    (by decide) selected_cut_49132

theorem selected_cut_49133 : selected 10 ⟨612961, by decide⟩
    (prefixPartial 11 101519) = some ⟨11, 1, 0, 612961, 101519, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101519_612961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101519 ⟨612961, by decide⟩ :=
  accepted_of_selected 11 101519 ⟨612961, by decide⟩ ⟨11, 1, 0, 612961, 101519, 1, 262144⟩
    (by decide) selected_cut_49133

theorem unmarked_context_10_25379_1387936 : frontier 11 ⟨1387936, by decide⟩
    (prefixCache 10 25379) (prefixPartial 10 25379) = false := by
  decide +kernel

theorem node_context_10_25379_1387936 : EJMOriginalGlobalDAGData.nodes 11 ⟨1387936, by decide⟩ =
    .split (coordinate 10) (![⟨1387808, by decide⟩,⟨1387888, by decide⟩,⟨1387935, by decide⟩,⟨612961, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25379_1387936 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25379 ⟨1387936, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25379
    ⟨1387936, by decide⟩ (by decide) (![⟨1387808, by decide⟩,⟨1387888, by decide⟩,⟨1387935, by decide⟩,⟨612961, by decide⟩]) unmarked_context_10_25379_1387936 node_context_10_25379_1387936
  intro a
  fin_cases a
  · exact context_11_101516_1387808
  · exact context_11_101517_1387888
  · exact context_11_101518_1387935
  · exact context_11_101519_612961

theorem unmarked_context_9_6344_1387937 : frontier 12 ⟨1387937, by decide⟩
    (prefixCache 9 6344) (prefixPartial 9 6344) = false := by
  decide +kernel

theorem node_context_9_6344_1387937 : EJMOriginalGlobalDAGData.nodes 12 ⟨1387937, by decide⟩ =
    .split (coordinate 9) (![⟨1387098, by decide⟩,⟨1387461, by decide⟩,⟨1387724, by decide⟩,⟨1387936, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6344_1387937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6344 ⟨1387937, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6344
    ⟨1387937, by decide⟩ (by decide) (![⟨1387098, by decide⟩,⟨1387461, by decide⟩,⟨1387724, by decide⟩,⟨1387936, by decide⟩]) unmarked_context_9_6344_1387937 node_context_9_6344_1387937
  intro a
  fin_cases a
  · exact context_10_25376_1387098
  · exact context_10_25377_1387461
  · exact context_10_25378_1387724
  · exact context_10_25379_1387936

theorem selected_cut_49134 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 101520) = some ⟨11, 1, 0, 907917, 101520, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101520_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101520 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 101520 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 101520, 1, 262144⟩
    (by decide) selected_cut_49134

theorem selected_cut_49135 : selected 10 ⟨1388008, by decide⟩
    (prefixPartial 11 101521) = some ⟨11, 2, 0, 1388008, 101521, 3633, 262144⟩ := by
  decide +kernel

theorem context_11_101521_1388008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101521 ⟨1388008, by decide⟩ :=
  accepted_of_selected 11 101521 ⟨1388008, by decide⟩ ⟨11, 2, 0, 1388008, 101521, 3633, 262144⟩
    (by decide) selected_cut_49135

theorem selected_cut_49136 : selected 10 ⟨1388050, by decide⟩
    (prefixPartial 11 101522) = some ⟨11, 2, 0, 1388050, 101522, 2197, 262144⟩ := by
  decide +kernel

theorem context_11_101522_1388050 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101522 ⟨1388050, by decide⟩ :=
  accepted_of_selected 11 101522 ⟨1388050, by decide⟩ ⟨11, 2, 0, 1388050, 101522, 2197, 262144⟩
    (by decide) selected_cut_49136

theorem selected_cut_49137 : selected 10 ⟨1388135, by decide⟩
    (prefixPartial 11 101523) = some ⟨11, 2, 0, 1388135, 101523, 3625, 262144⟩ := by
  decide +kernel

theorem context_11_101523_1388135 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101523 ⟨1388135, by decide⟩ :=
  accepted_of_selected 11 101523 ⟨1388135, by decide⟩ ⟨11, 2, 0, 1388135, 101523, 3625, 262144⟩
    (by decide) selected_cut_49137

theorem unmarked_context_10_25380_1388136 : frontier 11 ⟨1388136, by decide⟩
    (prefixCache 10 25380) (prefixPartial 10 25380) = false := by
  decide +kernel

theorem node_context_10_25380_1388136 : EJMOriginalGlobalDAGData.nodes 11 ⟨1388136, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1388008, by decide⟩,⟨1388050, by decide⟩,⟨1388135, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25380_1388136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25380 ⟨1388136, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25380
    ⟨1388136, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1388008, by decide⟩,⟨1388050, by decide⟩,⟨1388135, by decide⟩]) unmarked_context_10_25380_1388136 node_context_10_25380_1388136
  intro a
  fin_cases a
  · exact context_11_101520_907917
  · exact context_11_101521_1388008
  · exact context_11_101522_1388050
  · exact context_11_101523_1388135

theorem selected_cut_49138 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25381) = some ⟨10, 1, 0, 893098, 25381, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25381_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25381 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25381 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25381, 1, 1048576⟩
    (by decide) selected_cut_49138

theorem selected_cut_49139 : selected 10 ⟨1388173, by decide⟩
    (prefixPartial 11 101528) = some ⟨11, 2, 0, 1388173, 101528, 2129, 262144⟩ := by
  decide +kernel

theorem context_11_101528_1388173 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101528 ⟨1388173, by decide⟩ :=
  accepted_of_selected 11 101528 ⟨1388173, by decide⟩ ⟨11, 2, 0, 1388173, 101528, 2129, 262144⟩
    (by decide) selected_cut_49139

theorem selected_cut_49140 : selected 10 ⟨1388236, by decide⟩
    (prefixPartial 11 101529) = some ⟨11, 2, 0, 1388236, 101529, 3301, 262144⟩ := by
  decide +kernel

theorem context_11_101529_1388236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101529 ⟨1388236, by decide⟩ :=
  accepted_of_selected 11 101529 ⟨1388236, by decide⟩ ⟨11, 2, 0, 1388236, 101529, 3301, 262144⟩
    (by decide) selected_cut_49140

theorem selected_cut_49141 : selected 10 ⟨1388256, by decide⟩
    (prefixPartial 11 101530) = some ⟨11, 2, 0, 1388256, 101530, 1025, 262144⟩ := by
  decide +kernel

theorem context_11_101530_1388256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101530 ⟨1388256, by decide⟩ :=
  accepted_of_selected 11 101530 ⟨1388256, by decide⟩ ⟨11, 2, 0, 1388256, 101530, 1025, 262144⟩
    (by decide) selected_cut_49141

theorem selected_cut_49142 : selected 10 ⟨1388325, by decide⟩
    (prefixPartial 11 101531) = some ⟨11, 2, 0, 1388325, 101531, 3125, 262144⟩ := by
  decide +kernel

theorem context_11_101531_1388325 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101531 ⟨1388325, by decide⟩ :=
  accepted_of_selected 11 101531 ⟨1388325, by decide⟩ ⟨11, 2, 0, 1388325, 101531, 3125, 262144⟩
    (by decide) selected_cut_49142

theorem unmarked_context_10_25382_1388326 : frontier 11 ⟨1388326, by decide⟩
    (prefixCache 10 25382) (prefixPartial 10 25382) = false := by
  decide +kernel

theorem node_context_10_25382_1388326 : EJMOriginalGlobalDAGData.nodes 11 ⟨1388326, by decide⟩ =
    .split (coordinate 10) (![⟨1388173, by decide⟩,⟨1388236, by decide⟩,⟨1388256, by decide⟩,⟨1388325, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25382_1388326 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25382 ⟨1388326, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25382
    ⟨1388326, by decide⟩ (by decide) (![⟨1388173, by decide⟩,⟨1388236, by decide⟩,⟨1388256, by decide⟩,⟨1388325, by decide⟩]) unmarked_context_10_25382_1388326 node_context_10_25382_1388326
  intro a
  fin_cases a
  · exact context_11_101528_1388173
  · exact context_11_101529_1388236
  · exact context_11_101530_1388256
  · exact context_11_101531_1388325

theorem selected_cut_49143 : selected 10 ⟨1388379, by decide⟩
    (prefixPartial 11 101532) = some ⟨11, 2, 0, 1388379, 101532, 2029, 262144⟩ := by
  decide +kernel

theorem context_11_101532_1388379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101532 ⟨1388379, by decide⟩ :=
  accepted_of_selected 11 101532 ⟨1388379, by decide⟩ ⟨11, 2, 0, 1388379, 101532, 2029, 262144⟩
    (by decide) selected_cut_49143

theorem selected_cut_49144 : selected 10 ⟨1388425, by decide⟩
    (prefixPartial 11 101533) = some ⟨11, 2, 0, 1388425, 101533, 2489, 262144⟩ := by
  decide +kernel

theorem context_11_101533_1388425 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101533 ⟨1388425, by decide⟩ :=
  accepted_of_selected 11 101533 ⟨1388425, by decide⟩ ⟨11, 2, 0, 1388425, 101533, 2489, 262144⟩
    (by decide) selected_cut_49144

theorem selected_cut_49145 : selected 10 ⟨1388472, by decide⟩
    (prefixPartial 11 101534) = some ⟨11, 2, 0, 1388472, 101534, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_101534_1388472 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101534 ⟨1388472, by decide⟩ :=
  accepted_of_selected 11 101534 ⟨1388472, by decide⟩ ⟨11, 2, 0, 1388472, 101534, 2113, 262144⟩
    (by decide) selected_cut_49145

theorem selected_cut_49146 : selected 10 ⟨1388492, by decide⟩
    (prefixPartial 11 101535) = some ⟨11, 2, 0, 1388492, 101535, 781, 262144⟩ := by
  decide +kernel

theorem context_11_101535_1388492 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101535 ⟨1388492, by decide⟩ :=
  accepted_of_selected 11 101535 ⟨1388492, by decide⟩ ⟨11, 2, 0, 1388492, 101535, 781, 262144⟩
    (by decide) selected_cut_49146

theorem unmarked_context_10_25383_1388493 : frontier 11 ⟨1388493, by decide⟩
    (prefixCache 10 25383) (prefixPartial 10 25383) = false := by
  decide +kernel

theorem node_context_10_25383_1388493 : EJMOriginalGlobalDAGData.nodes 11 ⟨1388493, by decide⟩ =
    .split (coordinate 10) (![⟨1388379, by decide⟩,⟨1388425, by decide⟩,⟨1388472, by decide⟩,⟨1388492, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25383_1388493 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25383 ⟨1388493, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25383
    ⟨1388493, by decide⟩ (by decide) (![⟨1388379, by decide⟩,⟨1388425, by decide⟩,⟨1388472, by decide⟩,⟨1388492, by decide⟩]) unmarked_context_10_25383_1388493 node_context_10_25383_1388493
  intro a
  fin_cases a
  · exact context_11_101532_1388379
  · exact context_11_101533_1388425
  · exact context_11_101534_1388472
  · exact context_11_101535_1388492

theorem unmarked_context_9_6345_1388494 : frontier 12 ⟨1388494, by decide⟩
    (prefixCache 9 6345) (prefixPartial 9 6345) = false := by
  decide +kernel

theorem node_context_9_6345_1388494 : EJMOriginalGlobalDAGData.nodes 12 ⟨1388494, by decide⟩ =
    .split (coordinate 9) (![⟨1388136, by decide⟩,⟨893098, by decide⟩,⟨1388326, by decide⟩,⟨1388493, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6345_1388494 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6345 ⟨1388494, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6345
    ⟨1388494, by decide⟩ (by decide) (![⟨1388136, by decide⟩,⟨893098, by decide⟩,⟨1388326, by decide⟩,⟨1388493, by decide⟩]) unmarked_context_9_6345_1388494 node_context_9_6345_1388494
  intro a
  fin_cases a
  · exact context_10_25380_1388136
  · exact context_10_25381_893098
  · exact context_10_25382_1388326
  · exact context_10_25383_1388493

theorem selected_cut_49147 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 101536) = some ⟨11, 1, 0, 907917, 101536, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101536_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101536 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 101536 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 101536, 1, 262144⟩
    (by decide) selected_cut_49147

theorem selected_cut_49148 : selected 10 ⟨1388531, by decide⟩
    (prefixPartial 11 101537) = some ⟨11, 2, 0, 1388531, 101537, 1461, 262144⟩ := by
  decide +kernel

theorem context_11_101537_1388531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101537 ⟨1388531, by decide⟩ :=
  accepted_of_selected 11 101537 ⟨1388531, by decide⟩ ⟨11, 2, 0, 1388531, 101537, 1461, 262144⟩
    (by decide) selected_cut_49148

theorem selected_cut_49149 : selected 10 ⟨1388560, by decide⟩
    (prefixPartial 11 101538) = some ⟨11, 2, 0, 1388560, 101538, 1877, 262144⟩ := by
  decide +kernel

theorem context_11_101538_1388560 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101538 ⟨1388560, by decide⟩ :=
  accepted_of_selected 11 101538 ⟨1388560, by decide⟩ ⟨11, 2, 0, 1388560, 101538, 1877, 262144⟩
    (by decide) selected_cut_49149

theorem selected_cut_49150 : selected 10 ⟨1388600, by decide⟩
    (prefixPartial 11 101539) = some ⟨11, 2, 0, 1388600, 101539, 1469, 262144⟩ := by
  decide +kernel

theorem context_11_101539_1388600 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101539 ⟨1388600, by decide⟩ :=
  accepted_of_selected 11 101539 ⟨1388600, by decide⟩ ⟨11, 2, 0, 1388600, 101539, 1469, 262144⟩
    (by decide) selected_cut_49150

theorem unmarked_context_10_25384_1388601 : frontier 11 ⟨1388601, by decide⟩
    (prefixCache 10 25384) (prefixPartial 10 25384) = false := by
  decide +kernel

theorem node_context_10_25384_1388601 : EJMOriginalGlobalDAGData.nodes 11 ⟨1388601, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1388531, by decide⟩,⟨1388560, by decide⟩,⟨1388600, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25384_1388601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25384 ⟨1388601, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25384
    ⟨1388601, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1388531, by decide⟩,⟨1388560, by decide⟩,⟨1388600, by decide⟩]) unmarked_context_10_25384_1388601 node_context_10_25384_1388601
  intro a
  fin_cases a
  · exact context_11_101536_907917
  · exact context_11_101537_1388531
  · exact context_11_101538_1388560
  · exact context_11_101539_1388600

theorem selected_cut_49151 : selected 10 ⟨1388636, by decide⟩
    (prefixPartial 11 101540) = some ⟨11, 2, 0, 1388636, 101540, 1493, 262144⟩ := by
  decide +kernel

theorem context_11_101540_1388636 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101540 ⟨1388636, by decide⟩ :=
  accepted_of_selected 11 101540 ⟨1388636, by decide⟩ ⟨11, 2, 0, 1388636, 101540, 1493, 262144⟩
    (by decide) selected_cut_49151

theorem selected_cut_49152 : selected 10 ⟨1388656, by decide⟩
    (prefixPartial 11 101541) = some ⟨11, 2, 0, 1388656, 101541, 713, 262144⟩ := by
  decide +kernel

theorem context_11_101541_1388656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101541 ⟨1388656, by decide⟩ :=
  accepted_of_selected 11 101541 ⟨1388656, by decide⟩ ⟨11, 2, 0, 1388656, 101541, 713, 262144⟩
    (by decide) selected_cut_49152

theorem selected_cut_49153 : selected 10 ⟨1388679, by decide⟩
    (prefixPartial 11 101542) = some ⟨11, 2, 0, 1388679, 101542, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_101542_1388679 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101542 ⟨1388679, by decide⟩ :=
  accepted_of_selected 11 101542 ⟨1388679, by decide⟩ ⟨11, 2, 0, 1388679, 101542, 1589, 262144⟩
    (by decide) selected_cut_49153

theorem selected_cut_49154 : selected 10 ⟨1388719, by decide⟩
    (prefixPartial 11 101543) = some ⟨11, 2, 0, 1388719, 101543, 1717, 262144⟩ := by
  decide +kernel

theorem context_11_101543_1388719 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101543 ⟨1388719, by decide⟩ :=
  accepted_of_selected 11 101543 ⟨1388719, by decide⟩ ⟨11, 2, 0, 1388719, 101543, 1717, 262144⟩
    (by decide) selected_cut_49154

theorem unmarked_context_10_25385_1388720 : frontier 11 ⟨1388720, by decide⟩
    (prefixCache 10 25385) (prefixPartial 10 25385) = false := by
  decide +kernel

theorem node_context_10_25385_1388720 : EJMOriginalGlobalDAGData.nodes 11 ⟨1388720, by decide⟩ =
    .split (coordinate 10) (![⟨1388636, by decide⟩,⟨1388656, by decide⟩,⟨1388679, by decide⟩,⟨1388719, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25385_1388720 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25385 ⟨1388720, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25385
    ⟨1388720, by decide⟩ (by decide) (![⟨1388636, by decide⟩,⟨1388656, by decide⟩,⟨1388679, by decide⟩,⟨1388719, by decide⟩]) unmarked_context_10_25385_1388720 node_context_10_25385_1388720
  intro a
  fin_cases a
  · exact context_11_101540_1388636
  · exact context_11_101541_1388656
  · exact context_11_101542_1388679
  · exact context_11_101543_1388719

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
