/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover518
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_49828 : selected 9 ⟨1413111, by decide⟩
    (prefixPartial 12 409363) = some ⟨12, 2, 0, 1413111, 409363, 2505, 65536⟩ := by
  decide +kernel

theorem context_12_409363_1413111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409363 ⟨1413111, by decide⟩ :=
  accepted_of_selected 12 409363 ⟨1413111, by decide⟩ ⟨12, 2, 0, 1413111, 409363, 2505, 65536⟩
    (by decide) selected_cut_49828

theorem unmarked_context_11_102340_1413112 : frontier 10 ⟨1413112, by decide⟩
    (prefixCache 11 102340) (prefixPartial 11 102340) = false := by
  decide +kernel

theorem node_context_11_102340_1413112 : EJMOriginalGlobalDAGData.nodes 10 ⟨1413112, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1412980, by decide⟩,⟨1413048, by decide⟩,⟨1413111, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102340_1413112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102340 ⟨1413112, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102340
    ⟨1413112, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1412980, by decide⟩,⟨1413048, by decide⟩,⟨1413111, by decide⟩]) unmarked_context_11_102340_1413112 node_context_11_102340_1413112
  intro a
  fin_cases a
  · exact context_12_409360_1108174
  · exact context_12_409361_1412980
  · exact context_12_409362_1413048
  · exact context_12_409363_1413111

theorem selected_cut_49829 : selected 10 ⟨1407133, by decide⟩
    (prefixPartial 11 102341) = some ⟨11, 2, 0, 1407133, 102341, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102341_1407133 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102341 ⟨1407133, by decide⟩ :=
  accepted_of_selected 11 102341 ⟨1407133, by decide⟩ ⟨11, 2, 0, 1407133, 102341, 5, 262144⟩
    (by decide) selected_cut_49829

theorem selected_cut_49830 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409368) = some ⟨12, 1, 0, 1108174, 409368, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409368_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409368 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409368 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409368, 1, 65536⟩
    (by decide) selected_cut_49830

theorem selected_cut_49831 : selected 9 ⟨1413167, by decide⟩
    (prefixPartial 12 409369) = some ⟨12, 2, 0, 1413167, 409369, 2149, 65536⟩ := by
  decide +kernel

theorem context_12_409369_1413167 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409369 ⟨1413167, by decide⟩ :=
  accepted_of_selected 12 409369 ⟨1413167, by decide⟩ ⟨12, 2, 0, 1413167, 409369, 2149, 65536⟩
    (by decide) selected_cut_49831

theorem selected_cut_49832 : selected 9 ⟨1413214, by decide⟩
    (prefixPartial 12 409370) = some ⟨12, 2, 0, 1413214, 409370, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_409370_1413214 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409370 ⟨1413214, by decide⟩ :=
  accepted_of_selected 12 409370 ⟨1413214, by decide⟩ ⟨12, 2, 0, 1413214, 409370, 2177, 65536⟩
    (by decide) selected_cut_49832

theorem selected_cut_49833 : selected 9 ⟨1413256, by decide⟩
    (prefixPartial 12 409371) = some ⟨12, 2, 0, 1413256, 409371, 1961, 65536⟩ := by
  decide +kernel

theorem context_12_409371_1413256 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409371 ⟨1413256, by decide⟩ :=
  accepted_of_selected 12 409371 ⟨1413256, by decide⟩ ⟨12, 2, 0, 1413256, 409371, 1961, 65536⟩
    (by decide) selected_cut_49833

theorem unmarked_context_11_102342_1413257 : frontier 10 ⟨1413257, by decide⟩
    (prefixCache 11 102342) (prefixPartial 11 102342) = false := by
  decide +kernel

theorem node_context_11_102342_1413257 : EJMOriginalGlobalDAGData.nodes 10 ⟨1413257, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1413167, by decide⟩,⟨1413214, by decide⟩,⟨1413256, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102342_1413257 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102342 ⟨1413257, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102342
    ⟨1413257, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1413167, by decide⟩,⟨1413214, by decide⟩,⟨1413256, by decide⟩]) unmarked_context_11_102342_1413257 node_context_11_102342_1413257
  intro a
  fin_cases a
  · exact context_12_409368_1108174
  · exact context_12_409369_1413167
  · exact context_12_409370_1413214
  · exact context_12_409371_1413256

theorem selected_cut_49834 : selected 10 ⟨1413342, by decide⟩
    (prefixPartial 11 102343) = some ⟨11, 2, 0, 1413342, 102343, 4021, 262144⟩ := by
  decide +kernel

theorem context_11_102343_1413342 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102343 ⟨1413342, by decide⟩ :=
  accepted_of_selected 11 102343 ⟨1413342, by decide⟩ ⟨11, 2, 0, 1413342, 102343, 4021, 262144⟩
    (by decide) selected_cut_49834

theorem unmarked_context_10_25585_1413343 : frontier 11 ⟨1413343, by decide⟩
    (prefixCache 10 25585) (prefixPartial 10 25585) = false := by
  decide +kernel

theorem node_context_10_25585_1413343 : EJMOriginalGlobalDAGData.nodes 11 ⟨1413343, by decide⟩ =
    .split (coordinate 10) (![⟨1413112, by decide⟩,⟨1407133, by decide⟩,⟨1413257, by decide⟩,⟨1413342, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25585_1413343 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25585 ⟨1413343, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25585
    ⟨1413343, by decide⟩ (by decide) (![⟨1413112, by decide⟩,⟨1407133, by decide⟩,⟨1413257, by decide⟩,⟨1413342, by decide⟩]) unmarked_context_10_25585_1413343 node_context_10_25585_1413343
  intro a
  fin_cases a
  · exact context_11_102340_1413112
  · exact context_11_102341_1407133
  · exact context_11_102342_1413257
  · exact context_11_102343_1413342

theorem selected_cut_49835 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409376) = some ⟨12, 1, 0, 1108174, 409376, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409376_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409376 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409376 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409376, 1, 65536⟩
    (by decide) selected_cut_49835

theorem selected_cut_49836 : selected 9 ⟨1413399, by decide⟩
    (prefixPartial 12 409377) = some ⟨12, 2, 0, 1413399, 409377, 2405, 65536⟩ := by
  decide +kernel

theorem context_12_409377_1413399 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409377 ⟨1413399, by decide⟩ :=
  accepted_of_selected 12 409377 ⟨1413399, by decide⟩ ⟨12, 2, 0, 1413399, 409377, 2405, 65536⟩
    (by decide) selected_cut_49836

theorem selected_cut_49837 : selected 9 ⟨1413477, by decide⟩
    (prefixPartial 12 409378) = some ⟨12, 2, 0, 1413477, 409378, 2573, 65536⟩ := by
  decide +kernel

theorem context_12_409378_1413477 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409378 ⟨1413477, by decide⟩ :=
  accepted_of_selected 12 409378 ⟨1413477, by decide⟩ ⟨12, 2, 0, 1413477, 409378, 2573, 65536⟩
    (by decide) selected_cut_49837

theorem selected_cut_49838 : selected 9 ⟨1413520, by decide⟩
    (prefixPartial 12 409379) = some ⟨12, 2, 0, 1413520, 409379, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_409379_1413520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409379 ⟨1413520, by decide⟩ :=
  accepted_of_selected 12 409379 ⟨1413520, by decide⟩ ⟨12, 2, 0, 1413520, 409379, 2025, 65536⟩
    (by decide) selected_cut_49838

theorem unmarked_context_11_102344_1413521 : frontier 10 ⟨1413521, by decide⟩
    (prefixCache 11 102344) (prefixPartial 11 102344) = false := by
  decide +kernel

theorem node_context_11_102344_1413521 : EJMOriginalGlobalDAGData.nodes 10 ⟨1413521, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1413399, by decide⟩,⟨1413477, by decide⟩,⟨1413520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102344_1413521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102344 ⟨1413521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102344
    ⟨1413521, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1413399, by decide⟩,⟨1413477, by decide⟩,⟨1413520, by decide⟩]) unmarked_context_11_102344_1413521 node_context_11_102344_1413521
  intro a
  fin_cases a
  · exact context_12_409376_1108174
  · exact context_12_409377_1413399
  · exact context_12_409378_1413477
  · exact context_12_409379_1413520

theorem selected_cut_49839 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409380) = some ⟨12, 1, 0, 1108174, 409380, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409380_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409380 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409380 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409380, 1, 65536⟩
    (by decide) selected_cut_49839

theorem selected_cut_49840 : selected 9 ⟨1413564, by decide⟩
    (prefixPartial 12 409381) = some ⟨12, 2, 0, 1413564, 409381, 1933, 65536⟩ := by
  decide +kernel

theorem context_12_409381_1413564 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409381 ⟨1413564, by decide⟩ :=
  accepted_of_selected 12 409381 ⟨1413564, by decide⟩ ⟨12, 2, 0, 1413564, 409381, 1933, 65536⟩
    (by decide) selected_cut_49840

theorem selected_cut_49841 : selected 9 ⟨1413607, by decide⟩
    (prefixPartial 12 409382) = some ⟨12, 2, 0, 1413607, 409382, 1929, 65536⟩ := by
  decide +kernel

theorem context_12_409382_1413607 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409382 ⟨1413607, by decide⟩ :=
  accepted_of_selected 12 409382 ⟨1413607, by decide⟩ ⟨12, 2, 0, 1413607, 409382, 1929, 65536⟩
    (by decide) selected_cut_49841

theorem selected_cut_49842 : selected 9 ⟨1413641, by decide⟩
    (prefixPartial 12 409383) = some ⟨12, 2, 0, 1413641, 409383, 1633, 65536⟩ := by
  decide +kernel

theorem context_12_409383_1413641 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409383 ⟨1413641, by decide⟩ :=
  accepted_of_selected 12 409383 ⟨1413641, by decide⟩ ⟨12, 2, 0, 1413641, 409383, 1633, 65536⟩
    (by decide) selected_cut_49842

theorem unmarked_context_11_102345_1413642 : frontier 10 ⟨1413642, by decide⟩
    (prefixCache 11 102345) (prefixPartial 11 102345) = false := by
  decide +kernel

theorem node_context_11_102345_1413642 : EJMOriginalGlobalDAGData.nodes 10 ⟨1413642, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1413564, by decide⟩,⟨1413607, by decide⟩,⟨1413641, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102345_1413642 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102345 ⟨1413642, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102345
    ⟨1413642, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1413564, by decide⟩,⟨1413607, by decide⟩,⟨1413641, by decide⟩]) unmarked_context_11_102345_1413642 node_context_11_102345_1413642
  intro a
  fin_cases a
  · exact context_12_409380_1108174
  · exact context_12_409381_1413564
  · exact context_12_409382_1413607
  · exact context_12_409383_1413641

theorem selected_cut_49843 : selected 10 ⟨1413684, by decide⟩
    (prefixPartial 11 102346) = some ⟨11, 2, 0, 1413684, 102346, 1793, 262144⟩ := by
  decide +kernel

theorem context_11_102346_1413684 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102346 ⟨1413684, by decide⟩ :=
  accepted_of_selected 11 102346 ⟨1413684, by decide⟩ ⟨11, 2, 0, 1413684, 102346, 1793, 262144⟩
    (by decide) selected_cut_49843

theorem selected_cut_49844 : selected 10 ⟨1413751, by decide⟩
    (prefixPartial 11 102347) = some ⟨11, 2, 0, 1413751, 102347, 3241, 262144⟩ := by
  decide +kernel

theorem context_11_102347_1413751 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102347 ⟨1413751, by decide⟩ :=
  accepted_of_selected 11 102347 ⟨1413751, by decide⟩ ⟨11, 2, 0, 1413751, 102347, 3241, 262144⟩
    (by decide) selected_cut_49844

theorem unmarked_context_10_25586_1413752 : frontier 11 ⟨1413752, by decide⟩
    (prefixCache 10 25586) (prefixPartial 10 25586) = false := by
  decide +kernel

theorem node_context_10_25586_1413752 : EJMOriginalGlobalDAGData.nodes 11 ⟨1413752, by decide⟩ =
    .split (coordinate 10) (![⟨1413521, by decide⟩,⟨1413642, by decide⟩,⟨1413684, by decide⟩,⟨1413751, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25586_1413752 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25586 ⟨1413752, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25586
    ⟨1413752, by decide⟩ (by decide) (![⟨1413521, by decide⟩,⟨1413642, by decide⟩,⟨1413684, by decide⟩,⟨1413751, by decide⟩]) unmarked_context_10_25586_1413752 node_context_10_25586_1413752
  intro a
  fin_cases a
  · exact context_11_102344_1413521
  · exact context_11_102345_1413642
  · exact context_11_102346_1413684
  · exact context_11_102347_1413751

theorem selected_cut_49845 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 409392) = some ⟨12, 1, 0, 1108174, 409392, 1, 65536⟩ := by
  decide +kernel

theorem context_12_409392_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409392 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 409392 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 409392, 1, 65536⟩
    (by decide) selected_cut_49845

theorem selected_cut_49846 : selected 9 ⟨1413794, by decide⟩
    (prefixPartial 12 409393) = some ⟨12, 2, 0, 1413794, 409393, 1681, 65536⟩ := by
  decide +kernel

theorem context_12_409393_1413794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409393 ⟨1413794, by decide⟩ :=
  accepted_of_selected 12 409393 ⟨1413794, by decide⟩ ⟨12, 2, 0, 1413794, 409393, 1681, 65536⟩
    (by decide) selected_cut_49846

theorem selected_cut_49847 : selected 9 ⟨1413830, by decide⟩
    (prefixPartial 12 409394) = some ⟨12, 2, 0, 1413830, 409394, 1697, 65536⟩ := by
  decide +kernel

theorem context_12_409394_1413830 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409394 ⟨1413830, by decide⟩ :=
  accepted_of_selected 12 409394 ⟨1413830, by decide⟩ ⟨12, 2, 0, 1413830, 409394, 1697, 65536⟩
    (by decide) selected_cut_49847

theorem selected_cut_49848 : selected 9 ⟨1413863, by decide⟩
    (prefixPartial 12 409395) = some ⟨12, 2, 0, 1413863, 409395, 1437, 65536⟩ := by
  decide +kernel

theorem context_12_409395_1413863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 409395 ⟨1413863, by decide⟩ :=
  accepted_of_selected 12 409395 ⟨1413863, by decide⟩ ⟨12, 2, 0, 1413863, 409395, 1437, 65536⟩
    (by decide) selected_cut_49848

theorem unmarked_context_11_102348_1413864 : frontier 10 ⟨1413864, by decide⟩
    (prefixCache 11 102348) (prefixPartial 11 102348) = false := by
  decide +kernel

theorem node_context_11_102348_1413864 : EJMOriginalGlobalDAGData.nodes 10 ⟨1413864, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1413794, by decide⟩,⟨1413830, by decide⟩,⟨1413863, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_102348_1413864 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102348 ⟨1413864, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 102348
    ⟨1413864, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1413794, by decide⟩,⟨1413830, by decide⟩,⟨1413863, by decide⟩]) unmarked_context_11_102348_1413864 node_context_11_102348_1413864
  intro a
  fin_cases a
  · exact context_12_409392_1108174
  · exact context_12_409393_1413794
  · exact context_12_409394_1413830
  · exact context_12_409395_1413863

theorem selected_cut_49849 : selected 10 ⟨1413920, by decide⟩
    (prefixPartial 11 102349) = some ⟨11, 2, 0, 1413920, 102349, 2713, 262144⟩ := by
  decide +kernel

theorem context_11_102349_1413920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102349 ⟨1413920, by decide⟩ :=
  accepted_of_selected 11 102349 ⟨1413920, by decide⟩ ⟨11, 2, 0, 1413920, 102349, 2713, 262144⟩
    (by decide) selected_cut_49849

theorem selected_cut_49850 : selected 10 ⟨1413971, by decide⟩
    (prefixPartial 11 102350) = some ⟨11, 2, 0, 1413971, 102350, 2345, 262144⟩ := by
  decide +kernel

theorem context_11_102350_1413971 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102350 ⟨1413971, by decide⟩ :=
  accepted_of_selected 11 102350 ⟨1413971, by decide⟩ ⟨11, 2, 0, 1413971, 102350, 2345, 262144⟩
    (by decide) selected_cut_49850

theorem selected_cut_49851 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 102351) = some ⟨11, 1, 0, 977886, 102351, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102351_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102351 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 102351 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 102351, 1, 262144⟩
    (by decide) selected_cut_49851

theorem unmarked_context_10_25587_1413972 : frontier 11 ⟨1413972, by decide⟩
    (prefixCache 10 25587) (prefixPartial 10 25587) = false := by
  decide +kernel

theorem node_context_10_25587_1413972 : EJMOriginalGlobalDAGData.nodes 11 ⟨1413972, by decide⟩ =
    .split (coordinate 10) (![⟨1413864, by decide⟩,⟨1413920, by decide⟩,⟨1413971, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25587_1413972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25587 ⟨1413972, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25587
    ⟨1413972, by decide⟩ (by decide) (![⟨1413864, by decide⟩,⟨1413920, by decide⟩,⟨1413971, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25587_1413972 node_context_10_25587_1413972
  intro a
  fin_cases a
  · exact context_11_102348_1413864
  · exact context_11_102349_1413920
  · exact context_11_102350_1413971
  · exact context_11_102351_977886

theorem unmarked_context_9_6396_1413973 : frontier 12 ⟨1413973, by decide⟩
    (prefixCache 9 6396) (prefixPartial 9 6396) = false := by
  decide +kernel

theorem node_context_9_6396_1413973 : EJMOriginalGlobalDAGData.nodes 12 ⟨1413973, by decide⟩ =
    .split (coordinate 9) (![⟨1412900, by decide⟩,⟨1413343, by decide⟩,⟨1413752, by decide⟩,⟨1413972, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6396_1413973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6396 ⟨1413973, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6396
    ⟨1413973, by decide⟩ (by decide) (![⟨1412900, by decide⟩,⟨1413343, by decide⟩,⟨1413752, by decide⟩,⟨1413972, by decide⟩]) unmarked_context_9_6396_1413973 node_context_9_6396_1413973
  intro a
  fin_cases a
  · exact context_10_25584_1412900
  · exact context_10_25585_1413343
  · exact context_10_25586_1413752
  · exact context_10_25587_1413972

theorem selected_cut_49852 : selected 10 ⟨1414013, by decide⟩
    (prefixPartial 11 102352) = some ⟨11, 2, 0, 1414013, 102352, 1693, 262144⟩ := by
  decide +kernel

theorem context_11_102352_1414013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102352 ⟨1414013, by decide⟩ :=
  accepted_of_selected 11 102352 ⟨1414013, by decide⟩ ⟨11, 2, 0, 1414013, 102352, 1693, 262144⟩
    (by decide) selected_cut_49852

theorem selected_cut_49853 : selected 10 ⟨1414075, by decide⟩
    (prefixPartial 11 102353) = some ⟨11, 2, 0, 1414075, 102353, 3805, 262144⟩ := by
  decide +kernel

theorem context_11_102353_1414075 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102353 ⟨1414075, by decide⟩ :=
  accepted_of_selected 11 102353 ⟨1414075, by decide⟩ ⟨11, 2, 0, 1414075, 102353, 3805, 262144⟩
    (by decide) selected_cut_49853

theorem selected_cut_49854 : selected 10 ⟨1414130, by decide⟩
    (prefixPartial 11 102354) = some ⟨11, 2, 0, 1414130, 102354, 3389, 262144⟩ := by
  decide +kernel

theorem context_11_102354_1414130 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102354 ⟨1414130, by decide⟩ :=
  accepted_of_selected 11 102354 ⟨1414130, by decide⟩ ⟨11, 2, 0, 1414130, 102354, 3389, 262144⟩
    (by decide) selected_cut_49854

theorem selected_cut_49855 : selected 10 ⟨1414174, by decide⟩
    (prefixPartial 11 102355) = some ⟨11, 2, 0, 1414174, 102355, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_102355_1414174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102355 ⟨1414174, by decide⟩ :=
  accepted_of_selected 11 102355 ⟨1414174, by decide⟩ ⟨11, 2, 0, 1414174, 102355, 2141, 262144⟩
    (by decide) selected_cut_49855

theorem unmarked_context_10_25588_1414175 : frontier 11 ⟨1414175, by decide⟩
    (prefixCache 10 25588) (prefixPartial 10 25588) = false := by
  decide +kernel

theorem node_context_10_25588_1414175 : EJMOriginalGlobalDAGData.nodes 11 ⟨1414175, by decide⟩ =
    .split (coordinate 10) (![⟨1414013, by decide⟩,⟨1414075, by decide⟩,⟨1414130, by decide⟩,⟨1414174, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25588_1414175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25588 ⟨1414175, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25588
    ⟨1414175, by decide⟩ (by decide) (![⟨1414013, by decide⟩,⟨1414075, by decide⟩,⟨1414130, by decide⟩,⟨1414174, by decide⟩]) unmarked_context_10_25588_1414175 node_context_10_25588_1414175
  intro a
  fin_cases a
  · exact context_11_102352_1414013
  · exact context_11_102353_1414075
  · exact context_11_102354_1414130
  · exact context_11_102355_1414174

theorem selected_cut_49856 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25589) = some ⟨10, 1, 0, 893098, 25589, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25589_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25589 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25589 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25589, 1, 1048576⟩
    (by decide) selected_cut_49856

theorem selected_cut_49857 : selected 10 ⟨1414219, by decide⟩
    (prefixPartial 11 102360) = some ⟨11, 2, 0, 1414219, 102360, 2389, 262144⟩ := by
  decide +kernel

theorem context_11_102360_1414219 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102360 ⟨1414219, by decide⟩ :=
  accepted_of_selected 11 102360 ⟨1414219, by decide⟩ ⟨11, 2, 0, 1414219, 102360, 2389, 262144⟩
    (by decide) selected_cut_49857

theorem selected_cut_49858 : selected 10 ⟨1414262, by decide⟩
    (prefixPartial 11 102361) = some ⟨11, 2, 0, 1414262, 102361, 3025, 262144⟩ := by
  decide +kernel

theorem context_11_102361_1414262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102361 ⟨1414262, by decide⟩ :=
  accepted_of_selected 11 102361 ⟨1414262, by decide⟩ ⟨11, 2, 0, 1414262, 102361, 3025, 262144⟩
    (by decide) selected_cut_49858

theorem selected_cut_49859 : selected 10 ⟨1414276, by decide⟩
    (prefixPartial 11 102362) = some ⟨11, 2, 0, 1414276, 102362, 873, 262144⟩ := by
  decide +kernel

theorem context_11_102362_1414276 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102362 ⟨1414276, by decide⟩ :=
  accepted_of_selected 11 102362 ⟨1414276, by decide⟩ ⟨11, 2, 0, 1414276, 102362, 873, 262144⟩
    (by decide) selected_cut_49859

theorem selected_cut_49860 : selected 10 ⟨1414317, by decide⟩
    (prefixPartial 11 102363) = some ⟨11, 2, 0, 1414317, 102363, 2101, 262144⟩ := by
  decide +kernel

theorem context_11_102363_1414317 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102363 ⟨1414317, by decide⟩ :=
  accepted_of_selected 11 102363 ⟨1414317, by decide⟩ ⟨11, 2, 0, 1414317, 102363, 2101, 262144⟩
    (by decide) selected_cut_49860

theorem unmarked_context_10_25590_1414318 : frontier 11 ⟨1414318, by decide⟩
    (prefixCache 10 25590) (prefixPartial 10 25590) = false := by
  decide +kernel

theorem node_context_10_25590_1414318 : EJMOriginalGlobalDAGData.nodes 11 ⟨1414318, by decide⟩ =
    .split (coordinate 10) (![⟨1414219, by decide⟩,⟨1414262, by decide⟩,⟨1414276, by decide⟩,⟨1414317, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25590_1414318 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25590 ⟨1414318, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25590
    ⟨1414318, by decide⟩ (by decide) (![⟨1414219, by decide⟩,⟨1414262, by decide⟩,⟨1414276, by decide⟩,⟨1414317, by decide⟩]) unmarked_context_10_25590_1414318 node_context_10_25590_1414318
  intro a
  fin_cases a
  · exact context_11_102360_1414219
  · exact context_11_102361_1414262
  · exact context_11_102362_1414276
  · exact context_11_102363_1414317

theorem selected_cut_49861 : selected 10 ⟨1414346, by decide⟩
    (prefixPartial 11 102364) = some ⟨11, 2, 0, 1414346, 102364, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_102364_1414346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102364 ⟨1414346, by decide⟩ :=
  accepted_of_selected 11 102364 ⟨1414346, by decide⟩ ⟨11, 2, 0, 1414346, 102364, 1661, 262144⟩
    (by decide) selected_cut_49861

theorem selected_cut_49862 : selected 10 ⟨1414391, by decide⟩
    (prefixPartial 11 102365) = some ⟨11, 2, 0, 1414391, 102365, 2329, 262144⟩ := by
  decide +kernel

theorem context_11_102365_1414391 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102365 ⟨1414391, by decide⟩ :=
  accepted_of_selected 11 102365 ⟨1414391, by decide⟩ ⟨11, 2, 0, 1414391, 102365, 2329, 262144⟩
    (by decide) selected_cut_49862

theorem selected_cut_49863 : selected 10 ⟨1414413, by decide⟩
    (prefixPartial 11 102366) = some ⟨11, 2, 0, 1414413, 102366, 1277, 262144⟩ := by
  decide +kernel

theorem context_11_102366_1414413 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102366 ⟨1414413, by decide⟩ :=
  accepted_of_selected 11 102366 ⟨1414413, by decide⟩ ⟨11, 2, 0, 1414413, 102366, 1277, 262144⟩
    (by decide) selected_cut_49863

theorem selected_cut_49864 : selected 10 ⟨977886, by decide⟩
    (prefixPartial 11 102367) = some ⟨11, 1, 0, 977886, 102367, 1, 262144⟩ := by
  decide +kernel

theorem context_11_102367_977886 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102367 ⟨977886, by decide⟩ :=
  accepted_of_selected 11 102367 ⟨977886, by decide⟩ ⟨11, 1, 0, 977886, 102367, 1, 262144⟩
    (by decide) selected_cut_49864

theorem unmarked_context_10_25591_1414414 : frontier 11 ⟨1414414, by decide⟩
    (prefixCache 10 25591) (prefixPartial 10 25591) = false := by
  decide +kernel

theorem node_context_10_25591_1414414 : EJMOriginalGlobalDAGData.nodes 11 ⟨1414414, by decide⟩ =
    .split (coordinate 10) (![⟨1414346, by decide⟩,⟨1414391, by decide⟩,⟨1414413, by decide⟩,⟨977886, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25591_1414414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25591 ⟨1414414, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25591
    ⟨1414414, by decide⟩ (by decide) (![⟨1414346, by decide⟩,⟨1414391, by decide⟩,⟨1414413, by decide⟩,⟨977886, by decide⟩]) unmarked_context_10_25591_1414414 node_context_10_25591_1414414
  intro a
  fin_cases a
  · exact context_11_102364_1414346
  · exact context_11_102365_1414391
  · exact context_11_102366_1414413
  · exact context_11_102367_977886

theorem unmarked_context_9_6397_1414415 : frontier 12 ⟨1414415, by decide⟩
    (prefixCache 9 6397) (prefixPartial 9 6397) = false := by
  decide +kernel

theorem node_context_9_6397_1414415 : EJMOriginalGlobalDAGData.nodes 12 ⟨1414415, by decide⟩ =
    .split (coordinate 9) (![⟨1414175, by decide⟩,⟨893098, by decide⟩,⟨1414318, by decide⟩,⟨1414414, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6397_1414415 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6397 ⟨1414415, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6397
    ⟨1414415, by decide⟩ (by decide) (![⟨1414175, by decide⟩,⟨893098, by decide⟩,⟨1414318, by decide⟩,⟨1414414, by decide⟩]) unmarked_context_9_6397_1414415 node_context_9_6397_1414415
  intro a
  fin_cases a
  · exact context_10_25588_1414175
  · exact context_10_25589_893098
  · exact context_10_25590_1414318
  · exact context_10_25591_1414414

theorem selected_cut_49865 : selected 10 ⟨1414437, by decide⟩
    (prefixPartial 11 102368) = some ⟨11, 2, 0, 1414437, 102368, 969, 262144⟩ := by
  decide +kernel

theorem context_11_102368_1414437 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102368 ⟨1414437, by decide⟩ :=
  accepted_of_selected 11 102368 ⟨1414437, by decide⟩ ⟨11, 2, 0, 1414437, 102368, 969, 262144⟩
    (by decide) selected_cut_49865

theorem selected_cut_49866 : selected 10 ⟨1414473, by decide⟩
    (prefixPartial 11 102369) = some ⟨11, 2, 0, 1414473, 102369, 2017, 262144⟩ := by
  decide +kernel

theorem context_11_102369_1414473 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102369 ⟨1414473, by decide⟩ :=
  accepted_of_selected 11 102369 ⟨1414473, by decide⟩ ⟨11, 2, 0, 1414473, 102369, 2017, 262144⟩
    (by decide) selected_cut_49866

theorem selected_cut_49867 : selected 10 ⟨1414503, by decide⟩
    (prefixPartial 11 102370) = some ⟨11, 2, 0, 1414503, 102370, 1857, 262144⟩ := by
  decide +kernel

theorem context_11_102370_1414503 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102370 ⟨1414503, by decide⟩ :=
  accepted_of_selected 11 102370 ⟨1414503, by decide⟩ ⟨11, 2, 0, 1414503, 102370, 1857, 262144⟩
    (by decide) selected_cut_49867

theorem selected_cut_49868 : selected 10 ⟨1414517, by decide⟩
    (prefixPartial 11 102371) = some ⟨11, 2, 0, 1414517, 102371, 1093, 262144⟩ := by
  decide +kernel

theorem context_11_102371_1414517 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102371 ⟨1414517, by decide⟩ :=
  accepted_of_selected 11 102371 ⟨1414517, by decide⟩ ⟨11, 2, 0, 1414517, 102371, 1093, 262144⟩
    (by decide) selected_cut_49868

theorem unmarked_context_10_25592_1414518 : frontier 11 ⟨1414518, by decide⟩
    (prefixCache 10 25592) (prefixPartial 10 25592) = false := by
  decide +kernel

theorem node_context_10_25592_1414518 : EJMOriginalGlobalDAGData.nodes 11 ⟨1414518, by decide⟩ =
    .split (coordinate 10) (![⟨1414437, by decide⟩,⟨1414473, by decide⟩,⟨1414503, by decide⟩,⟨1414517, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25592_1414518 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25592 ⟨1414518, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25592
    ⟨1414518, by decide⟩ (by decide) (![⟨1414437, by decide⟩,⟨1414473, by decide⟩,⟨1414503, by decide⟩,⟨1414517, by decide⟩]) unmarked_context_10_25592_1414518 node_context_10_25592_1414518
  intro a
  fin_cases a
  · exact context_11_102368_1414437
  · exact context_11_102369_1414473
  · exact context_11_102370_1414503
  · exact context_11_102371_1414517

theorem selected_cut_49869 : selected 10 ⟨1414546, by decide⟩
    (prefixPartial 11 102372) = some ⟨11, 2, 0, 1414546, 102372, 1357, 262144⟩ := by
  decide +kernel

theorem context_11_102372_1414546 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102372 ⟨1414546, by decide⟩ :=
  accepted_of_selected 11 102372 ⟨1414546, by decide⟩ ⟨11, 2, 0, 1414546, 102372, 1357, 262144⟩
    (by decide) selected_cut_49869

theorem selected_cut_49870 : selected 10 ⟨1410395, by decide⟩
    (prefixPartial 11 102373) = some ⟨11, 2, 0, 1410395, 102373, 5, 262144⟩ := by
  decide +kernel

theorem context_11_102373_1410395 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102373 ⟨1410395, by decide⟩ :=
  accepted_of_selected 11 102373 ⟨1410395, by decide⟩ ⟨11, 2, 0, 1410395, 102373, 5, 262144⟩
    (by decide) selected_cut_49870

theorem selected_cut_49871 : selected 10 ⟨1414571, by decide⟩
    (prefixPartial 11 102374) = some ⟨11, 2, 0, 1414571, 102374, 1533, 262144⟩ := by
  decide +kernel

theorem context_11_102374_1414571 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102374 ⟨1414571, by decide⟩ :=
  accepted_of_selected 11 102374 ⟨1414571, by decide⟩ ⟨11, 2, 0, 1414571, 102374, 1533, 262144⟩
    (by decide) selected_cut_49871

theorem selected_cut_49872 : selected 10 ⟨1414596, by decide⟩
    (prefixPartial 11 102375) = some ⟨11, 2, 0, 1414596, 102375, 1241, 262144⟩ := by
  decide +kernel

theorem context_11_102375_1414596 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 102375 ⟨1414596, by decide⟩ :=
  accepted_of_selected 11 102375 ⟨1414596, by decide⟩ ⟨11, 2, 0, 1414596, 102375, 1241, 262144⟩
    (by decide) selected_cut_49872

theorem unmarked_context_10_25593_1414597 : frontier 11 ⟨1414597, by decide⟩
    (prefixCache 10 25593) (prefixPartial 10 25593) = false := by
  decide +kernel

theorem node_context_10_25593_1414597 : EJMOriginalGlobalDAGData.nodes 11 ⟨1414597, by decide⟩ =
    .split (coordinate 10) (![⟨1414546, by decide⟩,⟨1410395, by decide⟩,⟨1414571, by decide⟩,⟨1414596, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25593_1414597 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25593 ⟨1414597, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25593
    ⟨1414597, by decide⟩ (by decide) (![⟨1414546, by decide⟩,⟨1410395, by decide⟩,⟨1414571, by decide⟩,⟨1414596, by decide⟩]) unmarked_context_10_25593_1414597 node_context_10_25593_1414597
  intro a
  fin_cases a
  · exact context_11_102372_1414546
  · exact context_11_102373_1410395
  · exact context_11_102374_1414571
  · exact context_11_102375_1414596

theorem selected_cut_49873 : selected 11 ⟨1414611, by decide⟩
    (prefixPartial 10 25594) = some ⟨10, 2, 0, 1414611, 25594, 797, 1048576⟩ := by
  decide +kernel

theorem context_10_25594_1414611 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25594 ⟨1414611, by decide⟩ :=
  accepted_of_selected 10 25594 ⟨1414611, by decide⟩ ⟨10, 2, 0, 1414611, 25594, 797, 1048576⟩
    (by decide) selected_cut_49873

theorem selected_cut_49874 : selected 11 ⟨1414668, by decide⟩
    (prefixPartial 10 25595) = some ⟨10, 2, 0, 1414668, 25595, 2709, 1048576⟩ := by
  decide +kernel

theorem context_10_25595_1414668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25595 ⟨1414668, by decide⟩ :=
  accepted_of_selected 10 25595 ⟨1414668, by decide⟩ ⟨10, 2, 0, 1414668, 25595, 2709, 1048576⟩
    (by decide) selected_cut_49874

theorem unmarked_context_9_6398_1414669 : frontier 12 ⟨1414669, by decide⟩
    (prefixCache 9 6398) (prefixPartial 9 6398) = false := by
  decide +kernel

theorem node_context_9_6398_1414669 : EJMOriginalGlobalDAGData.nodes 12 ⟨1414669, by decide⟩ =
    .split (coordinate 9) (![⟨1414518, by decide⟩,⟨1414597, by decide⟩,⟨1414611, by decide⟩,⟨1414668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6398_1414669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6398 ⟨1414669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6398
    ⟨1414669, by decide⟩ (by decide) (![⟨1414518, by decide⟩,⟨1414597, by decide⟩,⟨1414611, by decide⟩,⟨1414668, by decide⟩]) unmarked_context_9_6398_1414669 node_context_9_6398_1414669
  intro a
  fin_cases a
  · exact context_10_25592_1414518
  · exact context_10_25593_1414597
  · exact context_10_25594_1414611
  · exact context_10_25595_1414668

theorem selected_cut_49875 : selected 12 ⟨1414755, by decide⟩
    (prefixPartial 9 6399) = some ⟨9, 2, 0, 1414755, 6399, 2565, 4194304⟩ := by
  decide +kernel

theorem context_9_6399_1414755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6399 ⟨1414755, by decide⟩ :=
  accepted_of_selected 9 6399 ⟨1414755, by decide⟩ ⟨9, 2, 0, 1414755, 6399, 2565, 4194304⟩
    (by decide) selected_cut_49875

theorem unmarked_context_8_1599_1414756 : frontier 13 ⟨1414756, by decide⟩
    (prefixCache 8 1599) (prefixPartial 8 1599) = false := by
  decide +kernel

theorem node_context_8_1599_1414756 : EJMOriginalGlobalDAGData.nodes 13 ⟨1414756, by decide⟩ =
    .split (coordinate 8) (![⟨1413973, by decide⟩,⟨1414415, by decide⟩,⟨1414669, by decide⟩,⟨1414755, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1599_1414756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1599 ⟨1414756, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1599
    ⟨1414756, by decide⟩ (by decide) (![⟨1413973, by decide⟩,⟨1414415, by decide⟩,⟨1414669, by decide⟩,⟨1414755, by decide⟩]) unmarked_context_8_1599_1414756 node_context_8_1599_1414756
  intro a
  fin_cases a
  · exact context_9_6396_1413973
  · exact context_9_6397_1414415
  · exact context_9_6398_1414669
  · exact context_9_6399_1414755

theorem unmarked_context_7_399_1414757 : frontier 14 ⟨1414757, by decide⟩
    (prefixCache 7 399) (prefixPartial 7 399) = false := by
  decide +kernel

theorem node_context_7_399_1414757 : EJMOriginalGlobalDAGData.nodes 14 ⟨1414757, by decide⟩ =
    .split (coordinate 7) (![⟨1408884, by decide⟩,⟨1410640, by decide⟩,⟨1412824, by decide⟩,⟨1414756, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_399_1414757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 399 ⟨1414757, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 399
    ⟨1414757, by decide⟩ (by decide) (![⟨1408884, by decide⟩,⟨1410640, by decide⟩,⟨1412824, by decide⟩,⟨1414756, by decide⟩]) unmarked_context_7_399_1414757 node_context_7_399_1414757
  intro a
  fin_cases a
  · exact context_8_1596_1408884
  · exact context_8_1597_1410640
  · exact context_8_1598_1412824
  · exact context_8_1599_1414756

theorem unmarked_context_6_99_1414758 : frontier 15 ⟨1414758, by decide⟩
    (prefixCache 6 99) (prefixPartial 6 99) = false := by
  decide +kernel

theorem node_context_6_99_1414758 : EJMOriginalGlobalDAGData.nodes 15 ⟨1414758, by decide⟩ =
    .split (coordinate 6) (![⟨1388990, by decide⟩,⟨1398151, by decide⟩,⟨1406882, by decide⟩,⟨1414757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_99_1414758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 99 ⟨1414758, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 99
    ⟨1414758, by decide⟩ (by decide) (![⟨1388990, by decide⟩,⟨1398151, by decide⟩,⟨1406882, by decide⟩,⟨1414757, by decide⟩]) unmarked_context_6_99_1414758 node_context_6_99_1414758
  intro a
  fin_cases a
  · exact context_7_396_1388990
  · exact context_7_397_1398151
  · exact context_7_398_1406882
  · exact context_7_399_1414757

theorem unmarked_context_5_24_1414759 : frontier 16 ⟨1414759, by decide⟩
    (prefixCache 5 24) (prefixPartial 5 24) = false := by
  decide +kernel

theorem node_context_5_24_1414759 : EJMOriginalGlobalDAGData.nodes 16 ⟨1414759, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨434744, by decide⟩,⟨1384219, by decide⟩,⟨1414758, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_24_1414759 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 24 ⟨1414759, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 24
    ⟨1414759, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨434744, by decide⟩,⟨1384219, by decide⟩,⟨1414758, by decide⟩]) unmarked_context_5_24_1414759 node_context_5_24_1414759
  intro a
  fin_cases a
  · exact context_6_96_434744
  · exact context_6_97_434744
  · exact context_6_98_1384219
  · exact context_6_99_1414758

theorem selected_cut_49876 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 100) = some ⟨6, 1, 0, 434744, 100, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_100_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 100 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 100 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 100, 1, 268435456⟩
    (by decide) selected_cut_49876

theorem selected_cut_49877 : selected 15 ⟨434744, by decide⟩
    (prefixPartial 6 101) = some ⟨6, 1, 0, 434744, 101, 1, 268435456⟩ := by
  decide +kernel

theorem context_6_101_434744 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 101 ⟨434744, by decide⟩ :=
  accepted_of_selected 6 101 ⟨434744, by decide⟩ ⟨6, 1, 0, 434744, 101, 1, 268435456⟩
    (by decide) selected_cut_49877

theorem selected_cut_49878 : selected 14 ⟨116316, by decide⟩
    (prefixPartial 7 408) = some ⟨7, 1, 0, 116316, 408, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_408_116316 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 408 ⟨116316, by decide⟩ :=
  accepted_of_selected 7 408 ⟨116316, by decide⟩ ⟨7, 1, 0, 116316, 408, 1, 67108864⟩
    (by decide) selected_cut_49878

theorem selected_cut_49879 : selected 13 ⟨1364555, by decide⟩
    (prefixPartial 8 1636) = some ⟨8, 1, 0, 1364555, 1636, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1636_1364555 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1636 ⟨1364555, by decide⟩ :=
  accepted_of_selected 8 1636 ⟨1364555, by decide⟩ ⟨8, 1, 0, 1364555, 1636, 1, 16777216⟩
    (by decide) selected_cut_49879

theorem selected_cut_49880 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 104768) = some ⟨11, 1, 0, 434745, 104768, 1, 262144⟩ := by
  decide +kernel

theorem context_11_104768_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104768 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 104768 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 104768, 1, 262144⟩
    (by decide) selected_cut_49880

theorem selected_cut_49881 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 104769) = some ⟨11, 1, 0, 434745, 104769, 1, 262144⟩ := by
  decide +kernel

theorem context_11_104769_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104769 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 104769 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 104769, 1, 262144⟩
    (by decide) selected_cut_49881

theorem selected_cut_49882 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 419080) = some ⟨12, 1, 0, 895, 419080, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419080_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419080 ⟨895, by decide⟩ :=
  accepted_of_selected 12 419080 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 419080, 1, 65536⟩
    (by decide) selected_cut_49882

theorem selected_cut_49883 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 419081) = some ⟨12, 1, 0, 895, 419081, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419081_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419081 ⟨895, by decide⟩ :=
  accepted_of_selected 12 419081 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 419081, 1, 65536⟩
    (by decide) selected_cut_49883

theorem selected_cut_49884 : selected 9 ⟨1414856, by decide⟩
    (prefixPartial 12 419082) = some ⟨12, 2, 0, 1414856, 419082, 1165, 65536⟩ := by
  decide +kernel

theorem context_12_419082_1414856 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419082 ⟨1414856, by decide⟩ :=
  accepted_of_selected 12 419082 ⟨1414856, by decide⟩ ⟨12, 2, 0, 1414856, 419082, 1165, 65536⟩
    (by decide) selected_cut_49884

theorem selected_cut_49885 : selected 9 ⟨1414969, by decide⟩
    (prefixPartial 12 419083) = some ⟨12, 2, 0, 1414969, 419083, 3037, 65536⟩ := by
  decide +kernel

theorem context_12_419083_1414969 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419083 ⟨1414969, by decide⟩ :=
  accepted_of_selected 12 419083 ⟨1414969, by decide⟩ ⟨12, 2, 0, 1414969, 419083, 3037, 65536⟩
    (by decide) selected_cut_49885

theorem unmarked_context_11_104770_1414970 : frontier 10 ⟨1414970, by decide⟩
    (prefixCache 11 104770) (prefixPartial 11 104770) = false := by
  decide +kernel

theorem node_context_11_104770_1414970 : EJMOriginalGlobalDAGData.nodes 10 ⟨1414970, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨1414856, by decide⟩,⟨1414969, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104770_1414970 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104770 ⟨1414970, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104770
    ⟨1414970, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨1414856, by decide⟩,⟨1414969, by decide⟩]) unmarked_context_11_104770_1414970 node_context_11_104770_1414970
  intro a
  fin_cases a
  · exact context_12_419080_895
  · exact context_12_419081_895
  · exact context_12_419082_1414856
  · exact context_12_419083_1414969

theorem selected_cut_49886 : selected 10 ⟨1415031, by decide⟩
    (prefixPartial 11 104771) = some ⟨11, 2, 0, 1415031, 104771, 977, 262144⟩ := by
  decide +kernel

theorem context_11_104771_1415031 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104771 ⟨1415031, by decide⟩ :=
  accepted_of_selected 11 104771 ⟨1415031, by decide⟩ ⟨11, 2, 0, 1415031, 104771, 977, 262144⟩
    (by decide) selected_cut_49886

theorem unmarked_context_10_26192_1415032 : frontier 11 ⟨1415032, by decide⟩
    (prefixCache 10 26192) (prefixPartial 10 26192) = false := by
  decide +kernel

theorem node_context_10_26192_1415032 : EJMOriginalGlobalDAGData.nodes 11 ⟨1415032, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1414970, by decide⟩,⟨1415031, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26192_1415032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26192 ⟨1415032, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26192
    ⟨1415032, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1414970, by decide⟩,⟨1415031, by decide⟩]) unmarked_context_10_26192_1415032 node_context_10_26192_1415032
  intro a
  fin_cases a
  · exact context_11_104768_434745
  · exact context_11_104769_434745
  · exact context_11_104770_1414970
  · exact context_11_104771_1415031

theorem selected_cut_49887 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 419088) = some ⟨12, 1, 0, 1415033, 419088, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419088_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419088 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 419088 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 419088, 1, 65536⟩
    (by decide) selected_cut_49887

theorem selected_cut_49888 : selected 9 ⟨1415097, by decide⟩
    (prefixPartial 12 419089) = some ⟨12, 2, 0, 1415097, 419089, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_419089_1415097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419089 ⟨1415097, by decide⟩ :=
  accepted_of_selected 12 419089 ⟨1415097, by decide⟩ ⟨12, 2, 0, 1415097, 419089, 1729, 65536⟩
    (by decide) selected_cut_49888

theorem selected_cut_49889 : selected 9 ⟨1415161, by decide⟩
    (prefixPartial 12 419090) = some ⟨12, 2, 0, 1415161, 419090, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_419090_1415161 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419090 ⟨1415161, by decide⟩ :=
  accepted_of_selected 12 419090 ⟨1415161, by decide⟩ ⟨12, 2, 0, 1415161, 419090, 2097, 65536⟩
    (by decide) selected_cut_49889

theorem selected_cut_49890 : selected 9 ⟨1415221, by decide⟩
    (prefixPartial 12 419091) = some ⟨12, 2, 0, 1415221, 419091, 2041, 65536⟩ := by
  decide +kernel

theorem context_12_419091_1415221 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419091 ⟨1415221, by decide⟩ :=
  accepted_of_selected 12 419091 ⟨1415221, by decide⟩ ⟨12, 2, 0, 1415221, 419091, 2041, 65536⟩
    (by decide) selected_cut_49890

theorem unmarked_context_11_104772_1415222 : frontier 10 ⟨1415222, by decide⟩
    (prefixCache 11 104772) (prefixPartial 11 104772) = false := by
  decide +kernel

theorem node_context_11_104772_1415222 : EJMOriginalGlobalDAGData.nodes 10 ⟨1415222, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1415097, by decide⟩,⟨1415161, by decide⟩,⟨1415221, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104772_1415222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104772 ⟨1415222, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104772
    ⟨1415222, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1415097, by decide⟩,⟨1415161, by decide⟩,⟨1415221, by decide⟩]) unmarked_context_11_104772_1415222 node_context_11_104772_1415222
  intro a
  fin_cases a
  · exact context_12_419088_1415033
  · exact context_12_419089_1415097
  · exact context_12_419090_1415161
  · exact context_12_419091_1415221

theorem selected_cut_49891 : selected 10 ⟨892405, by decide⟩
    (prefixPartial 11 104773) = some ⟨11, 1, 0, 892405, 104773, 1, 262144⟩ := by
  decide +kernel

theorem context_11_104773_892405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104773 ⟨892405, by decide⟩ :=
  accepted_of_selected 11 104773 ⟨892405, by decide⟩ ⟨11, 1, 0, 892405, 104773, 1, 262144⟩
    (by decide) selected_cut_49891

theorem selected_cut_49892 : selected 10 ⟨1415350, by decide⟩
    (prefixPartial 11 104774) = some ⟨11, 2, 0, 1415350, 104774, 3369, 262144⟩ := by
  decide +kernel

theorem context_11_104774_1415350 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104774 ⟨1415350, by decide⟩ :=
  accepted_of_selected 11 104774 ⟨1415350, by decide⟩ ⟨11, 2, 0, 1415350, 104774, 3369, 262144⟩
    (by decide) selected_cut_49892

theorem selected_cut_49893 : selected 10 ⟨1415450, by decide⟩
    (prefixPartial 11 104775) = some ⟨11, 2, 0, 1415450, 104775, 3417, 262144⟩ := by
  decide +kernel

theorem context_11_104775_1415450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104775 ⟨1415450, by decide⟩ :=
  accepted_of_selected 11 104775 ⟨1415450, by decide⟩ ⟨11, 2, 0, 1415450, 104775, 3417, 262144⟩
    (by decide) selected_cut_49893

theorem unmarked_context_10_26193_1415451 : frontier 11 ⟨1415451, by decide⟩
    (prefixCache 10 26193) (prefixPartial 10 26193) = false := by
  decide +kernel

theorem node_context_10_26193_1415451 : EJMOriginalGlobalDAGData.nodes 11 ⟨1415451, by decide⟩ =
    .split (coordinate 10) (![⟨1415222, by decide⟩,⟨892405, by decide⟩,⟨1415350, by decide⟩,⟨1415450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26193_1415451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26193 ⟨1415451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26193
    ⟨1415451, by decide⟩ (by decide) (![⟨1415222, by decide⟩,⟨892405, by decide⟩,⟨1415350, by decide⟩,⟨1415450, by decide⟩]) unmarked_context_10_26193_1415451 node_context_10_26193_1415451
  intro a
  fin_cases a
  · exact context_11_104772_1415222
  · exact context_11_104773_892405
  · exact context_11_104774_1415350
  · exact context_11_104775_1415450

theorem selected_cut_49894 : selected 9 ⟨435160, by decide⟩
    (prefixPartial 12 419104) = some ⟨12, 1, 0, 435160, 419104, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419104_435160 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419104 ⟨435160, by decide⟩ :=
  accepted_of_selected 12 419104 ⟨435160, by decide⟩ ⟨12, 1, 0, 435160, 419104, 1, 65536⟩
    (by decide) selected_cut_49894

theorem selected_cut_49895 : selected 9 ⟨1415532, by decide⟩
    (prefixPartial 12 419105) = some ⟨12, 2, 0, 1415532, 419105, 1965, 65536⟩ := by
  decide +kernel

theorem context_12_419105_1415532 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419105 ⟨1415532, by decide⟩ :=
  accepted_of_selected 12 419105 ⟨1415532, by decide⟩ ⟨12, 2, 0, 1415532, 419105, 1965, 65536⟩
    (by decide) selected_cut_49895

theorem selected_cut_49896 : selected 9 ⟨1415629, by decide⟩
    (prefixPartial 12 419106) = some ⟨12, 2, 0, 1415629, 419106, 1577, 65536⟩ := by
  decide +kernel

theorem context_12_419106_1415629 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419106 ⟨1415629, by decide⟩ :=
  accepted_of_selected 12 419106 ⟨1415629, by decide⟩ ⟨12, 2, 0, 1415629, 419106, 1577, 65536⟩
    (by decide) selected_cut_49896

theorem selected_cut_49897 : selected 9 ⟨1415701, by decide⟩
    (prefixPartial 12 419107) = some ⟨12, 2, 0, 1415701, 419107, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_419107_1415701 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419107 ⟨1415701, by decide⟩ :=
  accepted_of_selected 12 419107 ⟨1415701, by decide⟩ ⟨12, 2, 0, 1415701, 419107, 2133, 65536⟩
    (by decide) selected_cut_49897

theorem unmarked_context_11_104776_1415702 : frontier 10 ⟨1415702, by decide⟩
    (prefixCache 11 104776) (prefixPartial 11 104776) = false := by
  decide +kernel

theorem node_context_11_104776_1415702 : EJMOriginalGlobalDAGData.nodes 10 ⟨1415702, by decide⟩ =
    .split (coordinate 11) (![⟨435160, by decide⟩,⟨1415532, by decide⟩,⟨1415629, by decide⟩,⟨1415701, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104776_1415702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104776 ⟨1415702, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104776
    ⟨1415702, by decide⟩ (by decide) (![⟨435160, by decide⟩,⟨1415532, by decide⟩,⟨1415629, by decide⟩,⟨1415701, by decide⟩]) unmarked_context_11_104776_1415702 node_context_11_104776_1415702
  intro a
  fin_cases a
  · exact context_12_419104_435160
  · exact context_12_419105_1415532
  · exact context_12_419106_1415629
  · exact context_12_419107_1415701

theorem selected_cut_49898 : selected 10 ⟨1415756, by decide⟩
    (prefixPartial 11 104777) = some ⟨11, 2, 0, 1415756, 104777, 1733, 262144⟩ := by
  decide +kernel

theorem context_11_104777_1415756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104777 ⟨1415756, by decide⟩ :=
  accepted_of_selected 11 104777 ⟨1415756, by decide⟩ ⟨11, 2, 0, 1415756, 104777, 1733, 262144⟩
    (by decide) selected_cut_49898

theorem selected_cut_49899 : selected 10 ⟨1415896, by decide⟩
    (prefixPartial 11 104778) = some ⟨11, 2, 0, 1415896, 104778, 2513, 262144⟩ := by
  decide +kernel

theorem context_11_104778_1415896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104778 ⟨1415896, by decide⟩ :=
  accepted_of_selected 11 104778 ⟨1415896, by decide⟩ ⟨11, 2, 0, 1415896, 104778, 2513, 262144⟩
    (by decide) selected_cut_49899

theorem selected_cut_49900 : selected 9 ⟨1415973, by decide⟩
    (prefixPartial 12 419116) = some ⟨12, 2, 0, 1415973, 419116, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_419116_1415973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419116 ⟨1415973, by decide⟩ :=
  accepted_of_selected 12 419116 ⟨1415973, by decide⟩ ⟨12, 2, 0, 1415973, 419116, 1625, 65536⟩
    (by decide) selected_cut_49900

theorem selected_cut_49901 : selected 9 ⟨1416032, by decide⟩
    (prefixPartial 12 419117) = some ⟨12, 2, 0, 1416032, 419117, 1493, 65536⟩ := by
  decide +kernel

theorem context_12_419117_1416032 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419117 ⟨1416032, by decide⟩ :=
  accepted_of_selected 12 419117 ⟨1416032, by decide⟩ ⟨12, 2, 0, 1416032, 419117, 1493, 65536⟩
    (by decide) selected_cut_49901

theorem selected_cut_49902 : selected 9 ⟨1416100, by decide⟩
    (prefixPartial 12 419118) = some ⟨12, 2, 0, 1416100, 419118, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_419118_1416100 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419118 ⟨1416100, by decide⟩ :=
  accepted_of_selected 12 419118 ⟨1416100, by decide⟩ ⟨12, 2, 0, 1416100, 419118, 1625, 65536⟩
    (by decide) selected_cut_49902

theorem selected_cut_49903 : selected 9 ⟨1416140, by decide⟩
    (prefixPartial 12 419119) = some ⟨12, 2, 0, 1416140, 419119, 1369, 65536⟩ := by
  decide +kernel

theorem context_12_419119_1416140 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419119 ⟨1416140, by decide⟩ :=
  accepted_of_selected 12 419119 ⟨1416140, by decide⟩ ⟨12, 2, 0, 1416140, 419119, 1369, 65536⟩
    (by decide) selected_cut_49903

theorem unmarked_context_11_104779_1416141 : frontier 10 ⟨1416141, by decide⟩
    (prefixCache 11 104779) (prefixPartial 11 104779) = false := by
  decide +kernel

theorem node_context_11_104779_1416141 : EJMOriginalGlobalDAGData.nodes 10 ⟨1416141, by decide⟩ =
    .split (coordinate 11) (![⟨1415973, by decide⟩,⟨1416032, by decide⟩,⟨1416100, by decide⟩,⟨1416140, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104779_1416141 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104779 ⟨1416141, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104779
    ⟨1416141, by decide⟩ (by decide) (![⟨1415973, by decide⟩,⟨1416032, by decide⟩,⟨1416100, by decide⟩,⟨1416140, by decide⟩]) unmarked_context_11_104779_1416141 node_context_11_104779_1416141
  intro a
  fin_cases a
  · exact context_12_419116_1415973
  · exact context_12_419117_1416032
  · exact context_12_419118_1416100
  · exact context_12_419119_1416140

theorem unmarked_context_10_26194_1416142 : frontier 11 ⟨1416142, by decide⟩
    (prefixCache 10 26194) (prefixPartial 10 26194) = false := by
  decide +kernel

theorem node_context_10_26194_1416142 : EJMOriginalGlobalDAGData.nodes 11 ⟨1416142, by decide⟩ =
    .split (coordinate 10) (![⟨1415702, by decide⟩,⟨1415756, by decide⟩,⟨1415896, by decide⟩,⟨1416141, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26194_1416142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26194 ⟨1416142, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26194
    ⟨1416142, by decide⟩ (by decide) (![⟨1415702, by decide⟩,⟨1415756, by decide⟩,⟨1415896, by decide⟩,⟨1416141, by decide⟩]) unmarked_context_10_26194_1416142 node_context_10_26194_1416142
  intro a
  fin_cases a
  · exact context_11_104776_1415702
  · exact context_11_104777_1415756
  · exact context_11_104778_1415896
  · exact context_11_104779_1416141

theorem selected_cut_49904 : selected 10 ⟨1416251, by decide⟩
    (prefixPartial 11 104780) = some ⟨11, 2, 0, 1416251, 104780, 2193, 262144⟩ := by
  decide +kernel

theorem context_11_104780_1416251 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104780 ⟨1416251, by decide⟩ :=
  accepted_of_selected 11 104780 ⟨1416251, by decide⟩ ⟨11, 2, 0, 1416251, 104780, 2193, 262144⟩
    (by decide) selected_cut_49904

theorem selected_cut_49905 : selected 10 ⟨1416297, by decide⟩
    (prefixPartial 11 104781) = some ⟨11, 2, 0, 1416297, 104781, 881, 262144⟩ := by
  decide +kernel

theorem context_11_104781_1416297 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104781 ⟨1416297, by decide⟩ :=
  accepted_of_selected 11 104781 ⟨1416297, by decide⟩ ⟨11, 2, 0, 1416297, 104781, 881, 262144⟩
    (by decide) selected_cut_49905

theorem selected_cut_49906 : selected 10 ⟨1416362, by decide⟩
    (prefixPartial 11 104782) = some ⟨11, 2, 0, 1416362, 104782, 589, 262144⟩ := by
  decide +kernel

theorem context_11_104782_1416362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104782 ⟨1416362, by decide⟩ :=
  accepted_of_selected 11 104782 ⟨1416362, by decide⟩ ⟨11, 2, 0, 1416362, 104782, 589, 262144⟩
    (by decide) selected_cut_49906

theorem selected_cut_49907 : selected 10 ⟨1416420, by decide⟩
    (prefixPartial 11 104783) = some ⟨11, 2, 0, 1416420, 104783, 761, 262144⟩ := by
  decide +kernel

theorem context_11_104783_1416420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104783 ⟨1416420, by decide⟩ :=
  accepted_of_selected 11 104783 ⟨1416420, by decide⟩ ⟨11, 2, 0, 1416420, 104783, 761, 262144⟩
    (by decide) selected_cut_49907

theorem unmarked_context_10_26195_1416421 : frontier 11 ⟨1416421, by decide⟩
    (prefixCache 10 26195) (prefixPartial 10 26195) = false := by
  decide +kernel

theorem node_context_10_26195_1416421 : EJMOriginalGlobalDAGData.nodes 11 ⟨1416421, by decide⟩ =
    .split (coordinate 10) (![⟨1416251, by decide⟩,⟨1416297, by decide⟩,⟨1416362, by decide⟩,⟨1416420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26195_1416421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26195 ⟨1416421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26195
    ⟨1416421, by decide⟩ (by decide) (![⟨1416251, by decide⟩,⟨1416297, by decide⟩,⟨1416362, by decide⟩,⟨1416420, by decide⟩]) unmarked_context_10_26195_1416421 node_context_10_26195_1416421
  intro a
  fin_cases a
  · exact context_11_104780_1416251
  · exact context_11_104781_1416297
  · exact context_11_104782_1416362
  · exact context_11_104783_1416420

theorem unmarked_context_9_6548_1416422 : frontier 12 ⟨1416422, by decide⟩
    (prefixCache 9 6548) (prefixPartial 9 6548) = false := by
  decide +kernel

theorem node_context_9_6548_1416422 : EJMOriginalGlobalDAGData.nodes 12 ⟨1416422, by decide⟩ =
    .split (coordinate 9) (![⟨1415032, by decide⟩,⟨1415451, by decide⟩,⟨1416142, by decide⟩,⟨1416421, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6548_1416422 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6548 ⟨1416422, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6548
    ⟨1416422, by decide⟩ (by decide) (![⟨1415032, by decide⟩,⟨1415451, by decide⟩,⟨1416142, by decide⟩,⟨1416421, by decide⟩]) unmarked_context_9_6548_1416422 node_context_9_6548_1416422
  intro a
  fin_cases a
  · exact context_10_26192_1415032
  · exact context_10_26193_1415451
  · exact context_10_26194_1416142
  · exact context_10_26195_1416421

theorem selected_cut_49908 : selected 12 ⟨1416628, by decide⟩
    (prefixPartial 9 6549) = some ⟨9, 2, 0, 1416628, 6549, 2129, 4194304⟩ := by
  decide +kernel

theorem context_9_6549_1416628 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6549 ⟨1416628, by decide⟩ :=
  accepted_of_selected 9 6549 ⟨1416628, by decide⟩ ⟨9, 2, 0, 1416628, 6549, 2129, 4194304⟩
    (by decide) selected_cut_49908

theorem selected_cut_49909 : selected 12 ⟨1416681, by decide⟩
    (prefixPartial 9 6550) = some ⟨9, 2, 0, 1416681, 6550, 385, 4194304⟩ := by
  decide +kernel

theorem context_9_6550_1416681 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6550 ⟨1416681, by decide⟩ :=
  accepted_of_selected 9 6550 ⟨1416681, by decide⟩ ⟨9, 2, 0, 1416681, 6550, 385, 4194304⟩
    (by decide) selected_cut_49909

theorem selected_cut_49910 : selected 12 ⟨1416682, by decide⟩
    (prefixPartial 9 6551) = some ⟨9, 2, 0, 1416682, 6551, 9, 4194304⟩ := by
  decide +kernel

theorem context_9_6551_1416682 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6551 ⟨1416682, by decide⟩ :=
  accepted_of_selected 9 6551 ⟨1416682, by decide⟩ ⟨9, 2, 0, 1416682, 6551, 9, 4194304⟩
    (by decide) selected_cut_49910

theorem unmarked_context_8_1637_1416683 : frontier 13 ⟨1416683, by decide⟩
    (prefixCache 8 1637) (prefixPartial 8 1637) = false := by
  decide +kernel

theorem node_context_8_1637_1416683 : EJMOriginalGlobalDAGData.nodes 13 ⟨1416683, by decide⟩ =
    .split (coordinate 8) (![⟨1416422, by decide⟩,⟨1416628, by decide⟩,⟨1416681, by decide⟩,⟨1416682, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1637_1416683 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1637 ⟨1416683, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1637
    ⟨1416683, by decide⟩ (by decide) (![⟨1416422, by decide⟩,⟨1416628, by decide⟩,⟨1416681, by decide⟩,⟨1416682, by decide⟩]) unmarked_context_8_1637_1416683 node_context_8_1637_1416683
  intro a
  fin_cases a
  · exact context_9_6548_1416422
  · exact context_9_6549_1416628
  · exact context_9_6550_1416681
  · exact context_9_6551_1416682

theorem selected_cut_49911 : selected 13 ⟨1366235, by decide⟩
    (prefixPartial 8 1638) = some ⟨8, 1, 0, 1366235, 1638, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1638_1366235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1638 ⟨1366235, by decide⟩ :=
  accepted_of_selected 8 1638 ⟨1366235, by decide⟩ ⟨8, 1, 0, 1366235, 1638, 1, 16777216⟩
    (by decide) selected_cut_49911

theorem selected_cut_49912 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 104896) = some ⟨11, 1, 0, 434745, 104896, 1, 262144⟩ := by
  decide +kernel

theorem context_11_104896_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104896 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 104896 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 104896, 1, 262144⟩
    (by decide) selected_cut_49912

theorem selected_cut_49913 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 104897) = some ⟨11, 1, 0, 434745, 104897, 1, 262144⟩ := by
  decide +kernel

theorem context_11_104897_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104897 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 104897 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 104897, 1, 262144⟩
    (by decide) selected_cut_49913

theorem selected_cut_49914 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 419592) = some ⟨12, 1, 0, 895, 419592, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419592_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419592 ⟨895, by decide⟩ :=
  accepted_of_selected 12 419592 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 419592, 1, 65536⟩
    (by decide) selected_cut_49914

theorem selected_cut_49915 : selected 9 ⟨895, by decide⟩
    (prefixPartial 12 419593) = some ⟨12, 1, 0, 895, 419593, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419593_895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419593 ⟨895, by decide⟩ :=
  accepted_of_selected 12 419593 ⟨895, by decide⟩ ⟨12, 1, 0, 895, 419593, 1, 65536⟩
    (by decide) selected_cut_49915

theorem selected_cut_49916 : selected 9 ⟨1416756, by decide⟩
    (prefixPartial 12 419594) = some ⟨12, 2, 0, 1416756, 419594, 1529, 65536⟩ := by
  decide +kernel

theorem context_12_419594_1416756 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419594 ⟨1416756, by decide⟩ :=
  accepted_of_selected 12 419594 ⟨1416756, by decide⟩ ⟨12, 2, 0, 1416756, 419594, 1529, 65536⟩
    (by decide) selected_cut_49916

theorem selected_cut_49917 : selected 9 ⟨1416844, by decide⟩
    (prefixPartial 12 419595) = some ⟨12, 2, 0, 1416844, 419595, 2717, 65536⟩ := by
  decide +kernel

theorem context_12_419595_1416844 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419595 ⟨1416844, by decide⟩ :=
  accepted_of_selected 12 419595 ⟨1416844, by decide⟩ ⟨12, 2, 0, 1416844, 419595, 2717, 65536⟩
    (by decide) selected_cut_49917

theorem unmarked_context_11_104898_1416845 : frontier 10 ⟨1416845, by decide⟩
    (prefixCache 11 104898) (prefixPartial 11 104898) = false := by
  decide +kernel

theorem node_context_11_104898_1416845 : EJMOriginalGlobalDAGData.nodes 10 ⟨1416845, by decide⟩ =
    .split (coordinate 11) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨1416756, by decide⟩,⟨1416844, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104898_1416845 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104898 ⟨1416845, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104898
    ⟨1416845, by decide⟩ (by decide) (![⟨895, by decide⟩,⟨895, by decide⟩,⟨1416756, by decide⟩,⟨1416844, by decide⟩]) unmarked_context_11_104898_1416845 node_context_11_104898_1416845
  intro a
  fin_cases a
  · exact context_12_419592_895
  · exact context_12_419593_895
  · exact context_12_419594_1416756
  · exact context_12_419595_1416844

theorem selected_cut_49918 : selected 10 ⟨1366334, by decide⟩
    (prefixPartial 11 104899) = some ⟨11, 2, 0, 1366334, 104899, 5, 262144⟩ := by
  decide +kernel

theorem context_11_104899_1366334 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104899 ⟨1366334, by decide⟩ :=
  accepted_of_selected 11 104899 ⟨1366334, by decide⟩ ⟨11, 2, 0, 1366334, 104899, 5, 262144⟩
    (by decide) selected_cut_49918

theorem unmarked_context_10_26224_1416846 : frontier 11 ⟨1416846, by decide⟩
    (prefixCache 10 26224) (prefixPartial 10 26224) = false := by
  decide +kernel

theorem node_context_10_26224_1416846 : EJMOriginalGlobalDAGData.nodes 11 ⟨1416846, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1416845, by decide⟩,⟨1366334, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_26224_1416846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 26224 ⟨1416846, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 26224
    ⟨1416846, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨434745, by decide⟩,⟨1416845, by decide⟩,⟨1366334, by decide⟩]) unmarked_context_10_26224_1416846 node_context_10_26224_1416846
  intro a
  fin_cases a
  · exact context_11_104896_434745
  · exact context_11_104897_434745
  · exact context_11_104898_1416845
  · exact context_11_104899_1366334

theorem selected_cut_49919 : selected 9 ⟨1415033, by decide⟩
    (prefixPartial 12 419600) = some ⟨12, 1, 0, 1415033, 419600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_419600_1415033 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419600 ⟨1415033, by decide⟩ :=
  accepted_of_selected 12 419600 ⟨1415033, by decide⟩ ⟨12, 1, 0, 1415033, 419600, 1, 65536⟩
    (by decide) selected_cut_49919

theorem selected_cut_49920 : selected 9 ⟨1416906, by decide⟩
    (prefixPartial 12 419601) = some ⟨12, 2, 0, 1416906, 419601, 1977, 65536⟩ := by
  decide +kernel

theorem context_12_419601_1416906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419601 ⟨1416906, by decide⟩ :=
  accepted_of_selected 12 419601 ⟨1416906, by decide⟩ ⟨12, 2, 0, 1416906, 419601, 1977, 65536⟩
    (by decide) selected_cut_49920

theorem selected_cut_49921 : selected 9 ⟨1416968, by decide⟩
    (prefixPartial 12 419602) = some ⟨12, 2, 0, 1416968, 419602, 2381, 65536⟩ := by
  decide +kernel

theorem context_12_419602_1416968 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419602 ⟨1416968, by decide⟩ :=
  accepted_of_selected 12 419602 ⟨1416968, by decide⟩ ⟨12, 2, 0, 1416968, 419602, 2381, 65536⟩
    (by decide) selected_cut_49921

theorem selected_cut_49922 : selected 9 ⟨1417039, by decide⟩
    (prefixPartial 12 419603) = some ⟨12, 2, 0, 1417039, 419603, 2485, 65536⟩ := by
  decide +kernel

theorem context_12_419603_1417039 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 419603 ⟨1417039, by decide⟩ :=
  accepted_of_selected 12 419603 ⟨1417039, by decide⟩ ⟨12, 2, 0, 1417039, 419603, 2485, 65536⟩
    (by decide) selected_cut_49922

theorem unmarked_context_11_104900_1417040 : frontier 10 ⟨1417040, by decide⟩
    (prefixCache 11 104900) (prefixPartial 11 104900) = false := by
  decide +kernel

theorem node_context_11_104900_1417040 : EJMOriginalGlobalDAGData.nodes 10 ⟨1417040, by decide⟩ =
    .split (coordinate 11) (![⟨1415033, by decide⟩,⟨1416906, by decide⟩,⟨1416968, by decide⟩,⟨1417039, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_104900_1417040 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 104900 ⟨1417040, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 104900
    ⟨1417040, by decide⟩ (by decide) (![⟨1415033, by decide⟩,⟨1416906, by decide⟩,⟨1416968, by decide⟩,⟨1417039, by decide⟩]) unmarked_context_11_104900_1417040 node_context_11_104900_1417040
  intro a
  fin_cases a
  · exact context_12_419600_1415033
  · exact context_12_419601_1416906
  · exact context_12_419602_1416968
  · exact context_12_419603_1417039

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
