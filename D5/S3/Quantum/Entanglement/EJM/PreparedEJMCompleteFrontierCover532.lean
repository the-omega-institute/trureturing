/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover531
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_51077 : selected 10 ⟨1464294, by decide⟩
    (prefixPartial 11 114335) = some ⟨11, 1, 0, 1464294, 114335, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114335_1464294 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114335 ⟨1464294, by decide⟩ :=
  accepted_of_selected 11 114335 ⟨1464294, by decide⟩ ⟨11, 1, 0, 1464294, 114335, 1, 262144⟩
    (by decide) selected_cut_51077

theorem unmarked_context_10_28583_1467735 : frontier 11 ⟨1467735, by decide⟩
    (prefixCache 10 28583) (prefixPartial 10 28583) = false := by
  decide +kernel

theorem node_context_10_28583_1467735 : EJMOriginalGlobalDAGData.nodes 11 ⟨1467735, by decide⟩ =
    .split (coordinate 10) (![⟨1467623, by decide⟩,⟨1467688, by decide⟩,⟨1467734, by decide⟩,⟨1464294, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28583_1467735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28583 ⟨1467735, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28583
    ⟨1467735, by decide⟩ (by decide) (![⟨1467623, by decide⟩,⟨1467688, by decide⟩,⟨1467734, by decide⟩,⟨1464294, by decide⟩]) unmarked_context_10_28583_1467735 node_context_10_28583_1467735
  intro a
  fin_cases a
  · exact context_11_114332_1467623
  · exact context_11_114333_1467688
  · exact context_11_114334_1467734
  · exact context_11_114335_1464294

theorem unmarked_context_9_7145_1467736 : frontier 12 ⟨1467736, by decide⟩
    (prefixCache 9 7145) (prefixPartial 9 7145) = false := by
  decide +kernel

theorem node_context_9_7145_1467736 : EJMOriginalGlobalDAGData.nodes 12 ⟨1467736, by decide⟩ =
    .split (coordinate 9) (![⟨1467383, by decide⟩,⟨893098, by decide⟩,⟨1467581, by decide⟩,⟨1467735, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_7145_1467736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7145 ⟨1467736, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 7145
    ⟨1467736, by decide⟩ (by decide) (![⟨1467383, by decide⟩,⟨893098, by decide⟩,⟨1467581, by decide⟩,⟨1467735, by decide⟩]) unmarked_context_9_7145_1467736 node_context_9_7145_1467736
  intro a
  fin_cases a
  · exact context_10_28580_1467383
  · exact context_10_28581_893098
  · exact context_10_28582_1467581
  · exact context_10_28583_1467735

theorem selected_cut_51078 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 114336) = some ⟨11, 1, 0, 1375697, 114336, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114336_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114336 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 114336 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 114336, 1, 262144⟩
    (by decide) selected_cut_51078

theorem selected_cut_51079 : selected 10 ⟨1467787, by decide⟩
    (prefixPartial 11 114337) = some ⟨11, 2, 0, 1467787, 114337, 2121, 262144⟩ := by
  decide +kernel

theorem context_11_114337_1467787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114337 ⟨1467787, by decide⟩ :=
  accepted_of_selected 11 114337 ⟨1467787, by decide⟩ ⟨11, 2, 0, 1467787, 114337, 2121, 262144⟩
    (by decide) selected_cut_51079

theorem selected_cut_51080 : selected 10 ⟨1467853, by decide⟩
    (prefixPartial 11 114338) = some ⟨11, 2, 0, 1467853, 114338, 2325, 262144⟩ := by
  decide +kernel

theorem context_11_114338_1467853 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114338 ⟨1467853, by decide⟩ :=
  accepted_of_selected 11 114338 ⟨1467853, by decide⟩ ⟨11, 2, 0, 1467853, 114338, 2325, 262144⟩
    (by decide) selected_cut_51080

theorem selected_cut_51081 : selected 10 ⟨1467895, by decide⟩
    (prefixPartial 11 114339) = some ⟨11, 2, 0, 1467895, 114339, 1673, 262144⟩ := by
  decide +kernel

theorem context_11_114339_1467895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114339 ⟨1467895, by decide⟩ :=
  accepted_of_selected 11 114339 ⟨1467895, by decide⟩ ⟨11, 2, 0, 1467895, 114339, 1673, 262144⟩
    (by decide) selected_cut_51081

theorem unmarked_context_10_28584_1467896 : frontier 11 ⟨1467896, by decide⟩
    (prefixCache 10 28584) (prefixPartial 10 28584) = false := by
  decide +kernel

theorem node_context_10_28584_1467896 : EJMOriginalGlobalDAGData.nodes 11 ⟨1467896, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1467787, by decide⟩,⟨1467853, by decide⟩,⟨1467895, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28584_1467896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28584 ⟨1467896, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28584
    ⟨1467896, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1467787, by decide⟩,⟨1467853, by decide⟩,⟨1467895, by decide⟩]) unmarked_context_10_28584_1467896 node_context_10_28584_1467896
  intro a
  fin_cases a
  · exact context_11_114336_1375697
  · exact context_11_114337_1467787
  · exact context_11_114338_1467853
  · exact context_11_114339_1467895

theorem selected_cut_51082 : selected 10 ⟨1467937, by decide⟩
    (prefixPartial 11 114340) = some ⟨11, 2, 0, 1467937, 114340, 1393, 262144⟩ := by
  decide +kernel

theorem context_11_114340_1467937 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114340 ⟨1467937, by decide⟩ :=
  accepted_of_selected 11 114340 ⟨1467937, by decide⟩ ⟨11, 2, 0, 1467937, 114340, 1393, 262144⟩
    (by decide) selected_cut_51082

theorem selected_cut_51083 : selected 10 ⟨1378525, by decide⟩
    (prefixPartial 11 114341) = some ⟨11, 1, 0, 1378525, 114341, 1, 262144⟩ := by
  decide +kernel

theorem context_11_114341_1378525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114341 ⟨1378525, by decide⟩ :=
  accepted_of_selected 11 114341 ⟨1378525, by decide⟩ ⟨11, 1, 0, 1378525, 114341, 1, 262144⟩
    (by decide) selected_cut_51083

theorem selected_cut_51084 : selected 10 ⟨1467976, by decide⟩
    (prefixPartial 11 114342) = some ⟨11, 2, 0, 1467976, 114342, 1893, 262144⟩ := by
  decide +kernel

theorem context_11_114342_1467976 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114342 ⟨1467976, by decide⟩ :=
  accepted_of_selected 11 114342 ⟨1467976, by decide⟩ ⟨11, 2, 0, 1467976, 114342, 1893, 262144⟩
    (by decide) selected_cut_51084

theorem selected_cut_51085 : selected 10 ⟨1468008, by decide⟩
    (prefixPartial 11 114343) = some ⟨11, 2, 0, 1468008, 114343, 1249, 262144⟩ := by
  decide +kernel

theorem context_11_114343_1468008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 114343 ⟨1468008, by decide⟩ :=
  accepted_of_selected 11 114343 ⟨1468008, by decide⟩ ⟨11, 2, 0, 1468008, 114343, 1249, 262144⟩
    (by decide) selected_cut_51085

theorem unmarked_context_10_28585_1468009 : frontier 11 ⟨1468009, by decide⟩
    (prefixCache 10 28585) (prefixPartial 10 28585) = false := by
  decide +kernel

theorem node_context_10_28585_1468009 : EJMOriginalGlobalDAGData.nodes 11 ⟨1468009, by decide⟩ =
    .split (coordinate 10) (![⟨1467937, by decide⟩,⟨1378525, by decide⟩,⟨1467976, by decide⟩,⟨1468008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_28585_1468009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28585 ⟨1468009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 28585
    ⟨1468009, by decide⟩ (by decide) (![⟨1467937, by decide⟩,⟨1378525, by decide⟩,⟨1467976, by decide⟩,⟨1468008, by decide⟩]) unmarked_context_10_28585_1468009 node_context_10_28585_1468009
  intro a
  fin_cases a
  · exact context_11_114340_1467937
  · exact context_11_114341_1378525
  · exact context_11_114342_1467976
  · exact context_11_114343_1468008

theorem selected_cut_51086 : selected 11 ⟨1432895, by decide⟩
    (prefixPartial 10 28586) = some ⟨10, 2, 0, 1432895, 28586, 5, 1048576⟩ := by
  decide +kernel

theorem context_10_28586_1432895 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28586 ⟨1432895, by decide⟩ :=
  accepted_of_selected 10 28586 ⟨1432895, by decide⟩ ⟨10, 2, 0, 1432895, 28586, 5, 1048576⟩
    (by decide) selected_cut_51086

theorem selected_cut_51087 : selected 11 ⟨1468096, by decide⟩
    (prefixPartial 10 28587) = some ⟨10, 2, 0, 1468096, 28587, 3453, 1048576⟩ := by
  decide +kernel

theorem context_10_28587_1468096 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28587 ⟨1468096, by decide⟩ :=
  accepted_of_selected 10 28587 ⟨1468096, by decide⟩ ⟨10, 2, 0, 1468096, 28587, 3453, 1048576⟩
    (by decide) selected_cut_51087

theorem unmarked_context_9_7146_1468097 : frontier 12 ⟨1468097, by decide⟩
    (prefixCache 9 7146) (prefixPartial 9 7146) = false := by
  decide +kernel

theorem node_context_9_7146_1468097 : EJMOriginalGlobalDAGData.nodes 12 ⟨1468097, by decide⟩ =
    .split (coordinate 9) (![⟨1467896, by decide⟩,⟨1468009, by decide⟩,⟨1432895, by decide⟩,⟨1468096, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_7146_1468097 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7146 ⟨1468097, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 7146
    ⟨1468097, by decide⟩ (by decide) (![⟨1467896, by decide⟩,⟨1468009, by decide⟩,⟨1432895, by decide⟩,⟨1468096, by decide⟩]) unmarked_context_9_7146_1468097 node_context_9_7146_1468097
  intro a
  fin_cases a
  · exact context_10_28584_1467896
  · exact context_10_28585_1468009
  · exact context_10_28586_1432895
  · exact context_10_28587_1468096

theorem selected_cut_51088 : selected 11 ⟨1468163, by decide⟩
    (prefixPartial 10 28588) = some ⟨10, 2, 0, 1468163, 28588, 2345, 1048576⟩ := by
  decide +kernel

theorem context_10_28588_1468163 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28588 ⟨1468163, by decide⟩ :=
  accepted_of_selected 10 28588 ⟨1468163, by decide⟩ ⟨10, 2, 0, 1468163, 28588, 2345, 1048576⟩
    (by decide) selected_cut_51088

theorem selected_cut_51089 : selected 11 ⟨1468199, by decide⟩
    (prefixPartial 10 28589) = some ⟨10, 2, 0, 1468199, 28589, 1257, 1048576⟩ := by
  decide +kernel

theorem context_10_28589_1468199 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28589 ⟨1468199, by decide⟩ :=
  accepted_of_selected 10 28589 ⟨1468199, by decide⟩ ⟨10, 2, 0, 1468199, 28589, 1257, 1048576⟩
    (by decide) selected_cut_51089

theorem selected_cut_51090 : selected 11 ⟨1468230, by decide⟩
    (prefixPartial 10 28590) = some ⟨10, 2, 0, 1468230, 28590, 545, 1048576⟩ := by
  decide +kernel

theorem context_10_28590_1468230 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28590 ⟨1468230, by decide⟩ :=
  accepted_of_selected 10 28590 ⟨1468230, by decide⟩ ⟨10, 2, 0, 1468230, 28590, 545, 1048576⟩
    (by decide) selected_cut_51090

theorem selected_cut_51091 : selected 11 ⟨1468234, by decide⟩
    (prefixPartial 10 28591) = some ⟨10, 2, 0, 1468234, 28591, 9, 1048576⟩ := by
  decide +kernel

theorem context_10_28591_1468234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 28591 ⟨1468234, by decide⟩ :=
  accepted_of_selected 10 28591 ⟨1468234, by decide⟩ ⟨10, 2, 0, 1468234, 28591, 9, 1048576⟩
    (by decide) selected_cut_51091

theorem unmarked_context_9_7147_1468235 : frontier 12 ⟨1468235, by decide⟩
    (prefixCache 9 7147) (prefixPartial 9 7147) = false := by
  decide +kernel

theorem node_context_9_7147_1468235 : EJMOriginalGlobalDAGData.nodes 12 ⟨1468235, by decide⟩ =
    .split (coordinate 9) (![⟨1468163, by decide⟩,⟨1468199, by decide⟩,⟨1468230, by decide⟩,⟨1468234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_7147_1468235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 7147 ⟨1468235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 7147
    ⟨1468235, by decide⟩ (by decide) (![⟨1468163, by decide⟩,⟨1468199, by decide⟩,⟨1468230, by decide⟩,⟨1468234, by decide⟩]) unmarked_context_9_7147_1468235 node_context_9_7147_1468235
  intro a
  fin_cases a
  · exact context_10_28588_1468163
  · exact context_10_28589_1468199
  · exact context_10_28590_1468230
  · exact context_10_28591_1468234

theorem unmarked_context_8_1786_1468236 : frontier 13 ⟨1468236, by decide⟩
    (prefixCache 8 1786) (prefixPartial 8 1786) = false := by
  decide +kernel

theorem node_context_8_1786_1468236 : EJMOriginalGlobalDAGData.nodes 13 ⟨1468236, by decide⟩ =
    .split (coordinate 8) (![⟨1467128, by decide⟩,⟨1467736, by decide⟩,⟨1468097, by decide⟩,⟨1468235, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1786_1468236 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1786 ⟨1468236, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1786
    ⟨1468236, by decide⟩ (by decide) (![⟨1467128, by decide⟩,⟨1467736, by decide⟩,⟨1468097, by decide⟩,⟨1468235, by decide⟩]) unmarked_context_8_1786_1468236 node_context_8_1786_1468236
  intro a
  fin_cases a
  · exact context_9_7144_1467128
  · exact context_9_7145_1467736
  · exact context_9_7146_1468097
  · exact context_9_7147_1468235

theorem selected_cut_51092 : selected 13 ⟨814757, by decide⟩
    (prefixPartial 8 1787) = some ⟨8, 1, 0, 814757, 1787, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_1787_814757 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1787 ⟨814757, by decide⟩ :=
  accepted_of_selected 8 1787 ⟨814757, by decide⟩ ⟨8, 1, 0, 814757, 1787, 1, 16777216⟩
    (by decide) selected_cut_51092

theorem unmarked_context_7_446_1468237 : frontier 14 ⟨1468237, by decide⟩
    (prefixCache 7 446) (prefixPartial 7 446) = false := by
  decide +kernel

theorem node_context_7_446_1468237 : EJMOriginalGlobalDAGData.nodes 14 ⟨1468237, by decide⟩ =
    .split (coordinate 7) (![⟨1464377, by decide⟩,⟨1465793, by decide⟩,⟨1468236, by decide⟩,⟨814757, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_446_1468237 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 446 ⟨1468237, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 446
    ⟨1468237, by decide⟩ (by decide) (![⟨1464377, by decide⟩,⟨1465793, by decide⟩,⟨1468236, by decide⟩,⟨814757, by decide⟩]) unmarked_context_7_446_1468237 node_context_7_446_1468237
  intro a
  fin_cases a
  · exact context_8_1784_1464377
  · exact context_8_1785_1465793
  · exact context_8_1786_1468236
  · exact context_8_1787_814757

theorem selected_cut_51093 : selected 14 ⟨1423770, by decide⟩
    (prefixPartial 7 447) = some ⟨7, 1, 0, 1423770, 447, 1, 67108864⟩ := by
  decide +kernel

theorem context_7_447_1423770 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 447 ⟨1423770, by decide⟩ :=
  accepted_of_selected 7 447 ⟨1423770, by decide⟩ ⟨7, 1, 0, 1423770, 447, 1, 67108864⟩
    (by decide) selected_cut_51093

theorem unmarked_context_6_111_1468238 : frontier 15 ⟨1468238, by decide⟩
    (prefixCache 6 111) (prefixPartial 6 111) = false := by
  decide +kernel

theorem node_context_6_111_1468238 : EJMOriginalGlobalDAGData.nodes 15 ⟨1468238, by decide⟩ =
    .split (coordinate 6) (![⟨1423770, by decide⟩,⟨1423770, by decide⟩,⟨1468237, by decide⟩,⟨1423770, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_6_111_1468238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 6 111 ⟨1468238, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 6 111
    ⟨1468238, by decide⟩ (by decide) (![⟨1423770, by decide⟩,⟨1423770, by decide⟩,⟨1468237, by decide⟩,⟨1423770, by decide⟩]) unmarked_context_6_111_1468238 node_context_6_111_1468238
  intro a
  fin_cases a
  · exact context_7_444_1423770
  · exact context_7_445_1423770
  · exact context_7_446_1468237
  · exact context_7_447_1423770

theorem unmarked_context_5_27_1468239 : frontier 16 ⟨1468239, by decide⟩
    (prefixCache 5 27) (prefixPartial 5 27) = false := by
  decide +kernel

theorem node_context_5_27_1468239 : EJMOriginalGlobalDAGData.nodes 16 ⟨1468239, by decide⟩ =
    .split (coordinate 5) (![⟨434744, by decide⟩,⟨434744, by decide⟩,⟨1462402, by decide⟩,⟨1468238, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_5_27_1468239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 5 27 ⟨1468239, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 5 27
    ⟨1468239, by decide⟩ (by decide) (![⟨434744, by decide⟩,⟨434744, by decide⟩,⟨1462402, by decide⟩,⟨1468238, by decide⟩]) unmarked_context_5_27_1468239 node_context_5_27_1468239
  intro a
  fin_cases a
  · exact context_6_108_434744
  · exact context_6_109_434744
  · exact context_6_110_1462402
  · exact context_6_111_1468238

theorem unmarked_context_4_6_1468240 : frontier 17 ⟨1468240, by decide⟩
    (prefixCache 4 6) (prefixPartial 4 6) = false := by
  decide +kernel

theorem node_context_4_6_1468240 : EJMOriginalGlobalDAGData.nodes 17 ⟨1468240, by decide⟩ =
    .split (coordinate 4) (![⟨1414759, by decide⟩,⟨1448343, by decide⟩,⟨1461146, by decide⟩,⟨1468239, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_4_6_1468240 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 6 ⟨1468240, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 4 6
    ⟨1468240, by decide⟩ (by decide) (![⟨1414759, by decide⟩,⟨1448343, by decide⟩,⟨1461146, by decide⟩,⟨1468239, by decide⟩]) unmarked_context_4_6_1468240 node_context_4_6_1468240
  intro a
  fin_cases a
  · exact context_5_24_1414759
  · exact context_5_25_1448343
  · exact context_5_26_1461146
  · exact context_5_27_1468239

theorem selected_cut_51094 : selected 17 ⟨891585, by decide⟩
    (prefixPartial 4 7) = some ⟨4, 1, 0, 891585, 7, 1, 4294967296⟩ := by
  decide +kernel

theorem context_4_7_891585 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 7 ⟨891585, by decide⟩ :=
  accepted_of_selected 4 7 ⟨891585, by decide⟩ ⟨4, 1, 0, 891585, 7, 1, 4294967296⟩
    (by decide) selected_cut_51094

theorem unmarked_context_3_1_1468241 : frontier 18 ⟨1468241, by decide⟩
    (prefixCache 3 1) (prefixPartial 3 1) = false := by
  decide +kernel

theorem node_context_3_1_1468241 : EJMOriginalGlobalDAGData.nodes 18 ⟨1468241, by decide⟩ =
    .split (coordinate 3) (![⟨1107974, by decide⟩,⟨1364554, by decide⟩,⟨1468240, by decide⟩,⟨891585, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_3_1_1468241 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 3 1 ⟨1468241, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 3 1
    ⟨1468241, by decide⟩ (by decide) (![⟨1107974, by decide⟩,⟨1364554, by decide⟩,⟨1468240, by decide⟩,⟨891585, by decide⟩]) unmarked_context_3_1_1468241 node_context_3_1_1468241
  intro a
  fin_cases a
  · exact context_4_4_1107974
  · exact context_4_5_1364554
  · exact context_4_6_1468240
  · exact context_4_7_891585

theorem selected_cut_51095 : selected 18 ⟨1468242, by decide⟩
    (prefixPartial 3 2) = some ⟨3, 1, 0, 1468242, 2, 1, 17179869184⟩ := by
  decide +kernel

theorem context_3_2_1468242 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 3 2 ⟨1468242, by decide⟩ :=
  accepted_of_selected 3 2 ⟨1468242, by decide⟩ ⟨3, 1, 0, 1468242, 2, 1, 17179869184⟩
    (by decide) selected_cut_51095

theorem selected_cut_51096 : selected 18 ⟨1468243, by decide⟩
    (prefixPartial 3 3) = some ⟨3, 1, 0, 1468243, 3, 1, 17179869184⟩ := by
  decide +kernel

theorem context_3_3_1468243 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 3 3 ⟨1468243, by decide⟩ :=
  accepted_of_selected 3 3 ⟨1468243, by decide⟩ ⟨3, 1, 0, 1468243, 3, 1, 17179869184⟩
    (by decide) selected_cut_51096

theorem unmarked_context_2_0_1468244 : frontier 19 ⟨1468244, by decide⟩
    (prefixCache 2 0) (prefixPartial 2 0) = false := by
  decide +kernel

theorem node_context_2_0_1468244 : EJMOriginalGlobalDAGData.nodes 19 ⟨1468244, by decide⟩ =
    .split (coordinate 2) (![⟨891586, by decide⟩,⟨1468241, by decide⟩,⟨1468242, by decide⟩,⟨1468243, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_2_0_1468244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 2 0 ⟨1468244, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 2 0
    ⟨1468244, by decide⟩ (by decide) (![⟨891586, by decide⟩,⟨1468241, by decide⟩,⟨1468242, by decide⟩,⟨1468243, by decide⟩]) unmarked_context_2_0_1468244 node_context_2_0_1468244
  intro a
  fin_cases a
  · exact context_3_0_891586
  · exact context_3_1_1468241
  · exact context_3_2_1468242
  · exact context_3_3_1468243

theorem selected_cut_51097 : selected 17 ⟨1468245, by decide⟩
    (prefixPartial 4 16) = some ⟨4, 1, 0, 1468245, 16, 1, 4294967296⟩ := by
  decide +kernel

theorem context_4_16_1468245 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 4 16 ⟨1468245, by decide⟩ :=
  accepted_of_selected 4 16 ⟨1468245, by decide⟩ ⟨4, 1, 0, 1468245, 16, 1, 4294967296⟩
    (by decide) selected_cut_51097

theorem selected_cut_51098 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 69632) = some ⟨10, 1, 0, 1468246, 69632, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69632_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69632 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 69632 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 69632, 1, 1048576⟩
    (by decide) selected_cut_51098

theorem selected_cut_51099 : selected 11 ⟨1468587, by decide⟩
    (prefixPartial 10 69633) = some ⟨10, 2, 0, 1468587, 69633, 3585, 1048576⟩ := by
  decide +kernel

theorem context_10_69633_1468587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69633 ⟨1468587, by decide⟩ :=
  accepted_of_selected 10 69633 ⟨1468587, by decide⟩ ⟨10, 2, 0, 1468587, 69633, 3585, 1048576⟩
    (by decide) selected_cut_51099

theorem selected_cut_51100 : selected 11 ⟨1468787, by decide⟩
    (prefixPartial 10 69634) = some ⟨10, 2, 0, 1468787, 69634, 2517, 1048576⟩ := by
  decide +kernel

theorem context_10_69634_1468787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69634 ⟨1468787, by decide⟩ :=
  accepted_of_selected 10 69634 ⟨1468787, by decide⟩ ⟨10, 2, 0, 1468787, 69634, 2517, 1048576⟩
    (by decide) selected_cut_51100

theorem selected_cut_51101 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 69635) = some ⟨10, 1, 0, 3440, 69635, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69635_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69635 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 69635 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 69635, 1, 1048576⟩
    (by decide) selected_cut_51101

theorem unmarked_context_9_17408_1468788 : frontier 12 ⟨1468788, by decide⟩
    (prefixCache 9 17408) (prefixPartial 9 17408) = false := by
  decide +kernel

theorem node_context_9_17408_1468788 : EJMOriginalGlobalDAGData.nodes 12 ⟨1468788, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1468587, by decide⟩,⟨1468787, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17408_1468788 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17408 ⟨1468788, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17408
    ⟨1468788, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1468587, by decide⟩,⟨1468787, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_17408_1468788 node_context_9_17408_1468788
  intro a
  fin_cases a
  · exact context_10_69632_1468246
  · exact context_10_69633_1468587
  · exact context_10_69634_1468787
  · exact context_10_69635_3440

theorem selected_cut_51102 : selected 12 ⟨1468980, by decide⟩
    (prefixPartial 9 17409) = some ⟨9, 2, 0, 1468980, 17409, 2093, 4194304⟩ := by
  decide +kernel

theorem context_9_17409_1468980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17409 ⟨1468980, by decide⟩ :=
  accepted_of_selected 9 17409 ⟨1468980, by decide⟩ ⟨9, 2, 0, 1468980, 17409, 2093, 4194304⟩
    (by decide) selected_cut_51102

theorem selected_cut_51103 : selected 12 ⟨1469115, by decide⟩
    (prefixPartial 9 17410) = some ⟨9, 2, 0, 1469115, 17410, 1217, 4194304⟩ := by
  decide +kernel

theorem context_9_17410_1469115 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17410 ⟨1469115, by decide⟩ :=
  accepted_of_selected 9 17410 ⟨1469115, by decide⟩ ⟨9, 2, 0, 1469115, 17410, 1217, 4194304⟩
    (by decide) selected_cut_51103

theorem selected_cut_51104 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 17411) = some ⟨9, 1, 0, 4601, 17411, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_17411_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17411 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 17411 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 17411, 1, 4194304⟩
    (by decide) selected_cut_51104

theorem unmarked_context_8_4352_1469116 : frontier 13 ⟨1469116, by decide⟩
    (prefixCache 8 4352) (prefixPartial 8 4352) = false := by
  decide +kernel

theorem node_context_8_4352_1469116 : EJMOriginalGlobalDAGData.nodes 13 ⟨1469116, by decide⟩ =
    .split (coordinate 8) (![⟨1468788, by decide⟩,⟨1468980, by decide⟩,⟨1469115, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4352_1469116 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4352 ⟨1469116, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4352
    ⟨1469116, by decide⟩ (by decide) (![⟨1468788, by decide⟩,⟨1468980, by decide⟩,⟨1469115, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_4352_1469116 node_context_8_4352_1469116
  intro a
  fin_cases a
  · exact context_9_17408_1468788
  · exact context_9_17409_1468980
  · exact context_9_17410_1469115
  · exact context_9_17411_4601

theorem selected_cut_51105 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 69648) = some ⟨10, 1, 0, 1468246, 69648, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69648_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69648 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 69648 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 69648, 1, 1048576⟩
    (by decide) selected_cut_51105

theorem selected_cut_51106 : selected 10 ⟨1469225, by decide⟩
    (prefixPartial 11 278596) = some ⟨11, 2, 0, 1469225, 278596, 1841, 262144⟩ := by
  decide +kernel

theorem context_11_278596_1469225 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278596 ⟨1469225, by decide⟩ :=
  accepted_of_selected 11 278596 ⟨1469225, by decide⟩ ⟨11, 2, 0, 1469225, 278596, 1841, 262144⟩
    (by decide) selected_cut_51106

theorem selected_cut_51107 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 278597) = some ⟨11, 1, 0, 1468419, 278597, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278597_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278597 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 278597 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 278597, 1, 262144⟩
    (by decide) selected_cut_51107

theorem selected_cut_51108 : selected 10 ⟨1469340, by decide⟩
    (prefixPartial 11 278598) = some ⟨11, 2, 0, 1469340, 278598, 2725, 262144⟩ := by
  decide +kernel

theorem context_11_278598_1469340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278598 ⟨1469340, by decide⟩ :=
  accepted_of_selected 11 278598 ⟨1469340, by decide⟩ ⟨11, 2, 0, 1469340, 278598, 2725, 262144⟩
    (by decide) selected_cut_51108

theorem selected_cut_51109 : selected 10 ⟨1736, by decide⟩
    (prefixPartial 11 278599) = some ⟨11, 1, 0, 1736, 278599, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278599_1736 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278599 ⟨1736, by decide⟩ :=
  accepted_of_selected 11 278599 ⟨1736, by decide⟩ ⟨11, 1, 0, 1736, 278599, 1, 262144⟩
    (by decide) selected_cut_51109

theorem unmarked_context_10_69649_1469341 : frontier 11 ⟨1469341, by decide⟩
    (prefixCache 10 69649) (prefixPartial 10 69649) = false := by
  decide +kernel

theorem node_context_10_69649_1469341 : EJMOriginalGlobalDAGData.nodes 11 ⟨1469341, by decide⟩ =
    .split (coordinate 10) (![⟨1469225, by decide⟩,⟨1468419, by decide⟩,⟨1469340, by decide⟩,⟨1736, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69649_1469341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69649 ⟨1469341, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69649
    ⟨1469341, by decide⟩ (by decide) (![⟨1469225, by decide⟩,⟨1468419, by decide⟩,⟨1469340, by decide⟩,⟨1736, by decide⟩]) unmarked_context_10_69649_1469341 node_context_10_69649_1469341
  intro a
  fin_cases a
  · exact context_11_278596_1469225
  · exact context_11_278597_1468419
  · exact context_11_278598_1469340
  · exact context_11_278599_1736

theorem selected_cut_51110 : selected 10 ⟨1469436, by decide⟩
    (prefixPartial 11 278600) = some ⟨11, 2, 0, 1469436, 278600, 3157, 262144⟩ := by
  decide +kernel

theorem context_11_278600_1469436 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278600 ⟨1469436, by decide⟩ :=
  accepted_of_selected 11 278600 ⟨1469436, by decide⟩ ⟨11, 2, 0, 1469436, 278600, 3157, 262144⟩
    (by decide) selected_cut_51110

theorem selected_cut_51111 : selected 10 ⟨1469501, by decide⟩
    (prefixPartial 11 278601) = some ⟨11, 2, 0, 1469501, 278601, 2113, 262144⟩ := by
  decide +kernel

theorem context_11_278601_1469501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278601 ⟨1469501, by decide⟩ :=
  accepted_of_selected 11 278601 ⟨1469501, by decide⟩ ⟨11, 2, 0, 1469501, 278601, 2113, 262144⟩
    (by decide) selected_cut_51111

theorem selected_cut_51112 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 278602) = some ⟨11, 1, 0, 1468743, 278602, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278602_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278602 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 278602 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 278602, 1, 262144⟩
    (by decide) selected_cut_51112

theorem selected_cut_51113 : selected 10 ⟨1469586, by decide⟩
    (prefixPartial 11 278603) = some ⟨11, 2, 0, 1469586, 278603, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_278603_1469586 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278603 ⟨1469586, by decide⟩ :=
  accepted_of_selected 11 278603 ⟨1469586, by decide⟩ ⟨11, 2, 0, 1469586, 278603, 2173, 262144⟩
    (by decide) selected_cut_51113

theorem unmarked_context_10_69650_1469587 : frontier 11 ⟨1469587, by decide⟩
    (prefixCache 10 69650) (prefixPartial 10 69650) = false := by
  decide +kernel

theorem node_context_10_69650_1469587 : EJMOriginalGlobalDAGData.nodes 11 ⟨1469587, by decide⟩ =
    .split (coordinate 10) (![⟨1469436, by decide⟩,⟨1469501, by decide⟩,⟨1468743, by decide⟩,⟨1469586, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69650_1469587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69650 ⟨1469587, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69650
    ⟨1469587, by decide⟩ (by decide) (![⟨1469436, by decide⟩,⟨1469501, by decide⟩,⟨1468743, by decide⟩,⟨1469586, by decide⟩]) unmarked_context_10_69650_1469587 node_context_10_69650_1469587
  intro a
  fin_cases a
  · exact context_11_278600_1469436
  · exact context_11_278601_1469501
  · exact context_11_278602_1468743
  · exact context_11_278603_1469586

theorem selected_cut_51114 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 69651) = some ⟨10, 1, 0, 3440, 69651, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69651_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69651 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 69651 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 69651, 1, 1048576⟩
    (by decide) selected_cut_51114

theorem unmarked_context_9_17412_1469588 : frontier 12 ⟨1469588, by decide⟩
    (prefixCache 9 17412) (prefixPartial 9 17412) = false := by
  decide +kernel

theorem node_context_9_17412_1469588 : EJMOriginalGlobalDAGData.nodes 12 ⟨1469588, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1469341, by decide⟩,⟨1469587, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17412_1469588 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17412 ⟨1469588, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17412
    ⟨1469588, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1469341, by decide⟩,⟨1469587, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_17412_1469588 node_context_9_17412_1469588
  intro a
  fin_cases a
  · exact context_10_69648_1468246
  · exact context_10_69649_1469341
  · exact context_10_69650_1469587
  · exact context_10_69651_3440

theorem selected_cut_51115 : selected 11 ⟨1469663, by decide⟩
    (prefixPartial 10 69652) = some ⟨10, 2, 0, 1469663, 69652, 1925, 1048576⟩ := by
  decide +kernel

theorem context_10_69652_1469663 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69652 ⟨1469663, by decide⟩ :=
  accepted_of_selected 10 69652 ⟨1469663, by decide⟩ ⟨10, 2, 0, 1469663, 69652, 1925, 1048576⟩
    (by decide) selected_cut_51115

theorem selected_cut_51116 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 69653) = some ⟨10, 1, 0, 1468874, 69653, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69653_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69653 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 69653 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 69653, 1, 1048576⟩
    (by decide) selected_cut_51116

theorem selected_cut_51117 : selected 10 ⟨1469702, by decide⟩
    (prefixPartial 11 278616) = some ⟨11, 2, 0, 1469702, 278616, 1353, 262144⟩ := by
  decide +kernel

theorem context_11_278616_1469702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278616 ⟨1469702, by decide⟩ :=
  accepted_of_selected 11 278616 ⟨1469702, by decide⟩ ⟨11, 2, 0, 1469702, 278616, 1353, 262144⟩
    (by decide) selected_cut_51117

theorem selected_cut_51118 : selected 10 ⟨1469763, by decide⟩
    (prefixPartial 11 278617) = some ⟨11, 2, 0, 1469763, 278617, 1861, 262144⟩ := by
  decide +kernel

theorem context_11_278617_1469763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278617 ⟨1469763, by decide⟩ :=
  accepted_of_selected 11 278617 ⟨1469763, by decide⟩ ⟨11, 2, 0, 1469763, 278617, 1861, 262144⟩
    (by decide) selected_cut_51118

theorem selected_cut_51119 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 278618) = some ⟨11, 1, 0, 1468743, 278618, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278618_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278618 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 278618 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 278618, 1, 262144⟩
    (by decide) selected_cut_51119

theorem selected_cut_51120 : selected 10 ⟨1469807, by decide⟩
    (prefixPartial 11 278619) = some ⟨11, 2, 0, 1469807, 278619, 1269, 262144⟩ := by
  decide +kernel

theorem context_11_278619_1469807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278619 ⟨1469807, by decide⟩ :=
  accepted_of_selected 11 278619 ⟨1469807, by decide⟩ ⟨11, 2, 0, 1469807, 278619, 1269, 262144⟩
    (by decide) selected_cut_51120

theorem unmarked_context_10_69654_1469808 : frontier 11 ⟨1469808, by decide⟩
    (prefixCache 10 69654) (prefixPartial 10 69654) = false := by
  decide +kernel

theorem node_context_10_69654_1469808 : EJMOriginalGlobalDAGData.nodes 11 ⟨1469808, by decide⟩ =
    .split (coordinate 10) (![⟨1469702, by decide⟩,⟨1469763, by decide⟩,⟨1468743, by decide⟩,⟨1469807, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69654_1469808 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69654 ⟨1469808, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69654
    ⟨1469808, by decide⟩ (by decide) (![⟨1469702, by decide⟩,⟨1469763, by decide⟩,⟨1468743, by decide⟩,⟨1469807, by decide⟩]) unmarked_context_10_69654_1469808 node_context_10_69654_1469808
  intro a
  fin_cases a
  · exact context_11_278616_1469702
  · exact context_11_278617_1469763
  · exact context_11_278618_1468743
  · exact context_11_278619_1469807

theorem selected_cut_51121 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 69655) = some ⟨10, 1, 0, 3440, 69655, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69655_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69655 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 69655 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 69655, 1, 1048576⟩
    (by decide) selected_cut_51121

theorem unmarked_context_9_17413_1469809 : frontier 12 ⟨1469809, by decide⟩
    (prefixCache 9 17413) (prefixPartial 9 17413) = false := by
  decide +kernel

theorem node_context_9_17413_1469809 : EJMOriginalGlobalDAGData.nodes 12 ⟨1469809, by decide⟩ =
    .split (coordinate 9) (![⟨1469663, by decide⟩,⟨1468874, by decide⟩,⟨1469808, by decide⟩,⟨3440, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17413_1469809 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17413 ⟨1469809, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17413
    ⟨1469809, by decide⟩ (by decide) (![⟨1469663, by decide⟩,⟨1468874, by decide⟩,⟨1469808, by decide⟩,⟨3440, by decide⟩]) unmarked_context_9_17413_1469809 node_context_9_17413_1469809
  intro a
  fin_cases a
  · exact context_10_69652_1469663
  · exact context_10_69653_1468874
  · exact context_10_69654_1469808
  · exact context_10_69655_3440

theorem selected_cut_51122 : selected 11 ⟨1469906, by decide⟩
    (prefixPartial 10 69656) = some ⟨10, 2, 0, 1469906, 69656, 2973, 1048576⟩ := by
  decide +kernel

theorem context_10_69656_1469906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69656 ⟨1469906, by decide⟩ :=
  accepted_of_selected 10 69656 ⟨1469906, by decide⟩ ⟨10, 2, 0, 1469906, 69656, 2973, 1048576⟩
    (by decide) selected_cut_51122

theorem selected_cut_51123 : selected 11 ⟨1469978, by decide⟩
    (prefixPartial 10 69657) = some ⟨10, 2, 0, 1469978, 69657, 2053, 1048576⟩ := by
  decide +kernel

theorem context_10_69657_1469978 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69657 ⟨1469978, by decide⟩ :=
  accepted_of_selected 10 69657 ⟨1469978, by decide⟩ ⟨10, 2, 0, 1469978, 69657, 2053, 1048576⟩
    (by decide) selected_cut_51123

theorem selected_cut_51124 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 69658) = some ⟨10, 1, 0, 1469103, 69658, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69658_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69658 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 69658 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 69658, 1, 1048576⟩
    (by decide) selected_cut_51124

theorem selected_cut_51125 : selected 11 ⟨1470045, by decide⟩
    (prefixPartial 10 69659) = some ⟨10, 2, 0, 1470045, 69659, 825, 1048576⟩ := by
  decide +kernel

theorem context_10_69659_1470045 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69659 ⟨1470045, by decide⟩ :=
  accepted_of_selected 10 69659 ⟨1470045, by decide⟩ ⟨10, 2, 0, 1470045, 69659, 825, 1048576⟩
    (by decide) selected_cut_51125

theorem unmarked_context_9_17414_1470046 : frontier 12 ⟨1470046, by decide⟩
    (prefixCache 9 17414) (prefixPartial 9 17414) = false := by
  decide +kernel

theorem node_context_9_17414_1470046 : EJMOriginalGlobalDAGData.nodes 12 ⟨1470046, by decide⟩ =
    .split (coordinate 9) (![⟨1469906, by decide⟩,⟨1469978, by decide⟩,⟨1469103, by decide⟩,⟨1470045, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17414_1470046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17414 ⟨1470046, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17414
    ⟨1470046, by decide⟩ (by decide) (![⟨1469906, by decide⟩,⟨1469978, by decide⟩,⟨1469103, by decide⟩,⟨1470045, by decide⟩]) unmarked_context_9_17414_1470046 node_context_9_17414_1470046
  intro a
  fin_cases a
  · exact context_10_69656_1469906
  · exact context_10_69657_1469978
  · exact context_10_69658_1469103
  · exact context_10_69659_1470045

theorem selected_cut_51126 : selected 12 ⟨4601, by decide⟩
    (prefixPartial 9 17415) = some ⟨9, 1, 0, 4601, 17415, 1, 4194304⟩ := by
  decide +kernel

theorem context_9_17415_4601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17415 ⟨4601, by decide⟩ :=
  accepted_of_selected 9 17415 ⟨4601, by decide⟩ ⟨9, 1, 0, 4601, 17415, 1, 4194304⟩
    (by decide) selected_cut_51126

theorem unmarked_context_8_4353_1470047 : frontier 13 ⟨1470047, by decide⟩
    (prefixCache 8 4353) (prefixPartial 8 4353) = false := by
  decide +kernel

theorem node_context_8_4353_1470047 : EJMOriginalGlobalDAGData.nodes 13 ⟨1470047, by decide⟩ =
    .split (coordinate 8) (![⟨1469588, by decide⟩,⟨1469809, by decide⟩,⟨1470046, by decide⟩,⟨4601, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4353_1470047 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4353 ⟨1470047, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4353
    ⟨1470047, by decide⟩ (by decide) (![⟨1469588, by decide⟩,⟨1469809, by decide⟩,⟨1470046, by decide⟩,⟨4601, by decide⟩]) unmarked_context_8_4353_1470047 node_context_8_4353_1470047
  intro a
  fin_cases a
  · exact context_9_17412_1469588
  · exact context_9_17413_1469809
  · exact context_9_17414_1470046
  · exact context_9_17415_4601

theorem selected_cut_51127 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 69664) = some ⟨10, 1, 0, 1468246, 69664, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69664_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69664 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 69664 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 69664, 1, 1048576⟩
    (by decide) selected_cut_51127

theorem selected_cut_51128 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 1114640) = some ⟨12, 1, 0, 448748, 1114640, 1, 65536⟩ := by
  decide +kernel

theorem context_12_1114640_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1114640 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 1114640 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 1114640, 1, 65536⟩
    (by decide) selected_cut_51128

theorem selected_cut_51129 : selected 9 ⟨1470153, by decide⟩
    (prefixPartial 12 1114641) = some ⟨12, 2, 0, 1470153, 1114641, 1925, 65536⟩ := by
  decide +kernel

theorem context_12_1114641_1470153 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1114641 ⟨1470153, by decide⟩ :=
  accepted_of_selected 12 1114641 ⟨1470153, by decide⟩ ⟨12, 2, 0, 1470153, 1114641, 1925, 65536⟩
    (by decide) selected_cut_51129

theorem selected_cut_51130 : selected 9 ⟨1470193, by decide⟩
    (prefixPartial 12 1114642) = some ⟨12, 2, 0, 1470193, 1114642, 1297, 65536⟩ := by
  decide +kernel

theorem context_12_1114642_1470193 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1114642 ⟨1470193, by decide⟩ :=
  accepted_of_selected 12 1114642 ⟨1470193, by decide⟩ ⟨12, 2, 0, 1470193, 1114642, 1297, 65536⟩
    (by decide) selected_cut_51130

theorem selected_cut_51131 : selected 9 ⟨1470234, by decide⟩
    (prefixPartial 12 1114643) = some ⟨12, 2, 0, 1470234, 1114643, 1445, 65536⟩ := by
  decide +kernel

theorem context_12_1114643_1470234 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 1114643 ⟨1470234, by decide⟩ :=
  accepted_of_selected 12 1114643 ⟨1470234, by decide⟩ ⟨12, 2, 0, 1470234, 1114643, 1445, 65536⟩
    (by decide) selected_cut_51131

theorem unmarked_context_11_278660_1470235 : frontier 10 ⟨1470235, by decide⟩
    (prefixCache 11 278660) (prefixPartial 11 278660) = false := by
  decide +kernel

theorem node_context_11_278660_1470235 : EJMOriginalGlobalDAGData.nodes 10 ⟨1470235, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1470153, by decide⟩,⟨1470193, by decide⟩,⟨1470234, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_278660_1470235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278660 ⟨1470235, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 278660
    ⟨1470235, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1470153, by decide⟩,⟨1470193, by decide⟩,⟨1470234, by decide⟩]) unmarked_context_11_278660_1470235 node_context_11_278660_1470235
  intro a
  fin_cases a
  · exact context_12_1114640_448748
  · exact context_12_1114641_1470153
  · exact context_12_1114642_1470193
  · exact context_12_1114643_1470234

theorem selected_cut_51132 : selected 10 ⟨1468419, by decide⟩
    (prefixPartial 11 278661) = some ⟨11, 1, 0, 1468419, 278661, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278661_1468419 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278661 ⟨1468419, by decide⟩ :=
  accepted_of_selected 11 278661 ⟨1468419, by decide⟩ ⟨11, 1, 0, 1468419, 278661, 1, 262144⟩
    (by decide) selected_cut_51132

theorem selected_cut_51133 : selected 10 ⟨1470340, by decide⟩
    (prefixPartial 11 278662) = some ⟨11, 2, 0, 1470340, 278662, 3213, 262144⟩ := by
  decide +kernel

theorem context_11_278662_1470340 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278662 ⟨1470340, by decide⟩ :=
  accepted_of_selected 11 278662 ⟨1470340, by decide⟩ ⟨11, 2, 0, 1470340, 278662, 3213, 262144⟩
    (by decide) selected_cut_51133

theorem selected_cut_51134 : selected 10 ⟨1470454, by decide⟩
    (prefixPartial 11 278663) = some ⟨11, 2, 0, 1470454, 278663, 3241, 262144⟩ := by
  decide +kernel

theorem context_11_278663_1470454 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278663 ⟨1470454, by decide⟩ :=
  accepted_of_selected 11 278663 ⟨1470454, by decide⟩ ⟨11, 2, 0, 1470454, 278663, 3241, 262144⟩
    (by decide) selected_cut_51134

theorem unmarked_context_10_69665_1470455 : frontier 11 ⟨1470455, by decide⟩
    (prefixCache 10 69665) (prefixPartial 10 69665) = false := by
  decide +kernel

theorem node_context_10_69665_1470455 : EJMOriginalGlobalDAGData.nodes 11 ⟨1470455, by decide⟩ =
    .split (coordinate 10) (![⟨1470235, by decide⟩,⟨1468419, by decide⟩,⟨1470340, by decide⟩,⟨1470454, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69665_1470455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69665 ⟨1470455, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69665
    ⟨1470455, by decide⟩ (by decide) (![⟨1470235, by decide⟩,⟨1468419, by decide⟩,⟨1470340, by decide⟩,⟨1470454, by decide⟩]) unmarked_context_10_69665_1470455 node_context_10_69665_1470455
  intro a
  fin_cases a
  · exact context_11_278660_1470235
  · exact context_11_278661_1468419
  · exact context_11_278662_1470340
  · exact context_11_278663_1470454

theorem selected_cut_51135 : selected 10 ⟨1470511, by decide⟩
    (prefixPartial 11 278664) = some ⟨11, 2, 0, 1470511, 278664, 2269, 262144⟩ := by
  decide +kernel

theorem context_11_278664_1470511 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278664 ⟨1470511, by decide⟩ :=
  accepted_of_selected 11 278664 ⟨1470511, by decide⟩ ⟨11, 2, 0, 1470511, 278664, 2269, 262144⟩
    (by decide) selected_cut_51135

theorem selected_cut_51136 : selected 10 ⟨1470576, by decide⟩
    (prefixPartial 11 278665) = some ⟨11, 2, 0, 1470576, 278665, 2377, 262144⟩ := by
  decide +kernel

theorem context_11_278665_1470576 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278665 ⟨1470576, by decide⟩ :=
  accepted_of_selected 11 278665 ⟨1470576, by decide⟩ ⟨11, 2, 0, 1470576, 278665, 2377, 262144⟩
    (by decide) selected_cut_51136

theorem selected_cut_51137 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 278666) = some ⟨11, 1, 0, 1468743, 278666, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278666_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278666 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 278666 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 278666, 1, 262144⟩
    (by decide) selected_cut_51137

theorem selected_cut_51138 : selected 10 ⟨1470649, by decide⟩
    (prefixPartial 11 278667) = some ⟨11, 2, 0, 1470649, 278667, 2557, 262144⟩ := by
  decide +kernel

theorem context_11_278667_1470649 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278667 ⟨1470649, by decide⟩ :=
  accepted_of_selected 11 278667 ⟨1470649, by decide⟩ ⟨11, 2, 0, 1470649, 278667, 2557, 262144⟩
    (by decide) selected_cut_51138

theorem unmarked_context_10_69666_1470650 : frontier 11 ⟨1470650, by decide⟩
    (prefixCache 10 69666) (prefixPartial 10 69666) = false := by
  decide +kernel

theorem node_context_10_69666_1470650 : EJMOriginalGlobalDAGData.nodes 11 ⟨1470650, by decide⟩ =
    .split (coordinate 10) (![⟨1470511, by decide⟩,⟨1470576, by decide⟩,⟨1468743, by decide⟩,⟨1470649, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69666_1470650 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69666 ⟨1470650, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69666
    ⟨1470650, by decide⟩ (by decide) (![⟨1470511, by decide⟩,⟨1470576, by decide⟩,⟨1468743, by decide⟩,⟨1470649, by decide⟩]) unmarked_context_10_69666_1470650 node_context_10_69666_1470650
  intro a
  fin_cases a
  · exact context_11_278664_1470511
  · exact context_11_278665_1470576
  · exact context_11_278666_1468743
  · exact context_11_278667_1470649

theorem selected_cut_51139 : selected 10 ⟨1470733, by decide⟩
    (prefixPartial 11 278668) = some ⟨11, 2, 0, 1470733, 278668, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_278668_1470733 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278668 ⟨1470733, by decide⟩ :=
  accepted_of_selected 11 278668 ⟨1470733, by decide⟩ ⟨11, 2, 0, 1470733, 278668, 2429, 262144⟩
    (by decide) selected_cut_51139

theorem selected_cut_51140 : selected 10 ⟨1470787, by decide⟩
    (prefixPartial 11 278669) = some ⟨11, 2, 0, 1470787, 278669, 2065, 262144⟩ := by
  decide +kernel

theorem context_11_278669_1470787 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278669 ⟨1470787, by decide⟩ :=
  accepted_of_selected 11 278669 ⟨1470787, by decide⟩ ⟨11, 2, 0, 1470787, 278669, 2065, 262144⟩
    (by decide) selected_cut_51140

theorem selected_cut_51141 : selected 10 ⟨1470832, by decide⟩
    (prefixPartial 11 278670) = some ⟨11, 2, 0, 1470832, 278670, 2009, 262144⟩ := by
  decide +kernel

theorem context_11_278670_1470832 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278670 ⟨1470832, by decide⟩ :=
  accepted_of_selected 11 278670 ⟨1470832, by decide⟩ ⟨11, 2, 0, 1470832, 278670, 2009, 262144⟩
    (by decide) selected_cut_51141

theorem selected_cut_51142 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 278671) = some ⟨11, 1, 0, 1470044, 278671, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278671_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278671 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 278671 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 278671, 1, 262144⟩
    (by decide) selected_cut_51142

theorem unmarked_context_10_69667_1470833 : frontier 11 ⟨1470833, by decide⟩
    (prefixCache 10 69667) (prefixPartial 10 69667) = false := by
  decide +kernel

theorem node_context_10_69667_1470833 : EJMOriginalGlobalDAGData.nodes 11 ⟨1470833, by decide⟩ =
    .split (coordinate 10) (![⟨1470733, by decide⟩,⟨1470787, by decide⟩,⟨1470832, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69667_1470833 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69667 ⟨1470833, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69667
    ⟨1470833, by decide⟩ (by decide) (![⟨1470733, by decide⟩,⟨1470787, by decide⟩,⟨1470832, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_69667_1470833 node_context_10_69667_1470833
  intro a
  fin_cases a
  · exact context_11_278668_1470733
  · exact context_11_278669_1470787
  · exact context_11_278670_1470832
  · exact context_11_278671_1470044

theorem unmarked_context_9_17416_1470834 : frontier 12 ⟨1470834, by decide⟩
    (prefixCache 9 17416) (prefixPartial 9 17416) = false := by
  decide +kernel

theorem node_context_9_17416_1470834 : EJMOriginalGlobalDAGData.nodes 12 ⟨1470834, by decide⟩ =
    .split (coordinate 9) (![⟨1468246, by decide⟩,⟨1470455, by decide⟩,⟨1470650, by decide⟩,⟨1470833, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17416_1470834 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17416 ⟨1470834, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17416
    ⟨1470834, by decide⟩ (by decide) (![⟨1468246, by decide⟩,⟨1470455, by decide⟩,⟨1470650, by decide⟩,⟨1470833, by decide⟩]) unmarked_context_9_17416_1470834 node_context_9_17416_1470834
  intro a
  fin_cases a
  · exact context_10_69664_1468246
  · exact context_10_69665_1470455
  · exact context_10_69666_1470650
  · exact context_10_69667_1470833

theorem selected_cut_51143 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 278672) = some ⟨11, 1, 0, 434745, 278672, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278672_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278672 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 278672 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 278672, 1, 262144⟩
    (by decide) selected_cut_51143

theorem selected_cut_51144 : selected 10 ⟨1470894, by decide⟩
    (prefixPartial 11 278673) = some ⟨11, 2, 0, 1470894, 278673, 1661, 262144⟩ := by
  decide +kernel

theorem context_11_278673_1470894 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278673 ⟨1470894, by decide⟩ :=
  accepted_of_selected 11 278673 ⟨1470894, by decide⟩ ⟨11, 2, 0, 1470894, 278673, 1661, 262144⟩
    (by decide) selected_cut_51144

theorem selected_cut_51145 : selected 10 ⟨1470938, by decide⟩
    (prefixPartial 11 278674) = some ⟨11, 2, 0, 1470938, 278674, 1353, 262144⟩ := by
  decide +kernel

theorem context_11_278674_1470938 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278674 ⟨1470938, by decide⟩ :=
  accepted_of_selected 11 278674 ⟨1470938, by decide⟩ ⟨11, 2, 0, 1470938, 278674, 1353, 262144⟩
    (by decide) selected_cut_51145

theorem selected_cut_51146 : selected 10 ⟨1470973, by decide⟩
    (prefixPartial 11 278675) = some ⟨11, 2, 0, 1470973, 278675, 1345, 262144⟩ := by
  decide +kernel

theorem context_11_278675_1470973 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278675 ⟨1470973, by decide⟩ :=
  accepted_of_selected 11 278675 ⟨1470973, by decide⟩ ⟨11, 2, 0, 1470973, 278675, 1345, 262144⟩
    (by decide) selected_cut_51146

theorem unmarked_context_10_69668_1470974 : frontier 11 ⟨1470974, by decide⟩
    (prefixCache 10 69668) (prefixPartial 10 69668) = false := by
  decide +kernel

theorem node_context_10_69668_1470974 : EJMOriginalGlobalDAGData.nodes 11 ⟨1470974, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1470894, by decide⟩,⟨1470938, by decide⟩,⟨1470973, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69668_1470974 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69668 ⟨1470974, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69668
    ⟨1470974, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1470894, by decide⟩,⟨1470938, by decide⟩,⟨1470973, by decide⟩]) unmarked_context_10_69668_1470974 node_context_10_69668_1470974
  intro a
  fin_cases a
  · exact context_11_278672_434745
  · exact context_11_278673_1470894
  · exact context_11_278674_1470938
  · exact context_11_278675_1470973

theorem selected_cut_51147 : selected 11 ⟨1468874, by decide⟩
    (prefixPartial 10 69669) = some ⟨10, 1, 0, 1468874, 69669, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69669_1468874 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69669 ⟨1468874, by decide⟩ :=
  accepted_of_selected 10 69669 ⟨1468874, by decide⟩ ⟨10, 1, 0, 1468874, 69669, 1, 1048576⟩
    (by decide) selected_cut_51147

theorem selected_cut_51148 : selected 10 ⟨1471009, by decide⟩
    (prefixPartial 11 278680) = some ⟨11, 2, 0, 1471009, 278680, 1481, 262144⟩ := by
  decide +kernel

theorem context_11_278680_1471009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278680 ⟨1471009, by decide⟩ :=
  accepted_of_selected 11 278680 ⟨1471009, by decide⟩ ⟨11, 2, 0, 1471009, 278680, 1481, 262144⟩
    (by decide) selected_cut_51148

theorem selected_cut_51149 : selected 10 ⟨1471066, by decide⟩
    (prefixPartial 11 278681) = some ⟨11, 2, 0, 1471066, 278681, 2177, 262144⟩ := by
  decide +kernel

theorem context_11_278681_1471066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278681 ⟨1471066, by decide⟩ :=
  accepted_of_selected 11 278681 ⟨1471066, by decide⟩ ⟨11, 2, 0, 1471066, 278681, 2177, 262144⟩
    (by decide) selected_cut_51149

theorem selected_cut_51150 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 278682) = some ⟨11, 1, 0, 1468743, 278682, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278682_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278682 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 278682 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 278682, 1, 262144⟩
    (by decide) selected_cut_51150

theorem selected_cut_51151 : selected 10 ⟨1471104, by decide⟩
    (prefixPartial 11 278683) = some ⟨11, 2, 0, 1471104, 278683, 1469, 262144⟩ := by
  decide +kernel

theorem context_11_278683_1471104 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278683 ⟨1471104, by decide⟩ :=
  accepted_of_selected 11 278683 ⟨1471104, by decide⟩ ⟨11, 2, 0, 1471104, 278683, 1469, 262144⟩
    (by decide) selected_cut_51151

theorem unmarked_context_10_69670_1471105 : frontier 11 ⟨1471105, by decide⟩
    (prefixCache 10 69670) (prefixPartial 10 69670) = false := by
  decide +kernel

theorem node_context_10_69670_1471105 : EJMOriginalGlobalDAGData.nodes 11 ⟨1471105, by decide⟩ =
    .split (coordinate 10) (![⟨1471009, by decide⟩,⟨1471066, by decide⟩,⟨1468743, by decide⟩,⟨1471104, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69670_1471105 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69670 ⟨1471105, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69670
    ⟨1471105, by decide⟩ (by decide) (![⟨1471009, by decide⟩,⟨1471066, by decide⟩,⟨1468743, by decide⟩,⟨1471104, by decide⟩]) unmarked_context_10_69670_1471105 node_context_10_69670_1471105
  intro a
  fin_cases a
  · exact context_11_278680_1471009
  · exact context_11_278681_1471066
  · exact context_11_278682_1468743
  · exact context_11_278683_1471104

theorem selected_cut_51152 : selected 10 ⟨1471134, by decide⟩
    (prefixPartial 11 278684) = some ⟨11, 2, 0, 1471134, 278684, 1281, 262144⟩ := by
  decide +kernel

theorem context_11_278684_1471134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278684 ⟨1471134, by decide⟩ :=
  accepted_of_selected 11 278684 ⟨1471134, by decide⟩ ⟨11, 2, 0, 1471134, 278684, 1281, 262144⟩
    (by decide) selected_cut_51152

theorem selected_cut_51153 : selected 10 ⟨1471176, by decide⟩
    (prefixPartial 11 278685) = some ⟨11, 2, 0, 1471176, 278685, 1777, 262144⟩ := by
  decide +kernel

theorem context_11_278685_1471176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278685 ⟨1471176, by decide⟩ :=
  accepted_of_selected 11 278685 ⟨1471176, by decide⟩ ⟨11, 2, 0, 1471176, 278685, 1777, 262144⟩
    (by decide) selected_cut_51153

theorem selected_cut_51154 : selected 10 ⟨1471208, by decide⟩
    (prefixPartial 11 278686) = some ⟨11, 2, 0, 1471208, 278686, 1097, 262144⟩ := by
  decide +kernel

theorem context_11_278686_1471208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278686 ⟨1471208, by decide⟩ :=
  accepted_of_selected 11 278686 ⟨1471208, by decide⟩ ⟨11, 2, 0, 1471208, 278686, 1097, 262144⟩
    (by decide) selected_cut_51154

theorem selected_cut_51155 : selected 10 ⟨1470044, by decide⟩
    (prefixPartial 11 278687) = some ⟨11, 1, 0, 1470044, 278687, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278687_1470044 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278687 ⟨1470044, by decide⟩ :=
  accepted_of_selected 11 278687 ⟨1470044, by decide⟩ ⟨11, 1, 0, 1470044, 278687, 1, 262144⟩
    (by decide) selected_cut_51155

theorem unmarked_context_10_69671_1471209 : frontier 11 ⟨1471209, by decide⟩
    (prefixCache 10 69671) (prefixPartial 10 69671) = false := by
  decide +kernel

theorem node_context_10_69671_1471209 : EJMOriginalGlobalDAGData.nodes 11 ⟨1471209, by decide⟩ =
    .split (coordinate 10) (![⟨1471134, by decide⟩,⟨1471176, by decide⟩,⟨1471208, by decide⟩,⟨1470044, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69671_1471209 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69671 ⟨1471209, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69671
    ⟨1471209, by decide⟩ (by decide) (![⟨1471134, by decide⟩,⟨1471176, by decide⟩,⟨1471208, by decide⟩,⟨1470044, by decide⟩]) unmarked_context_10_69671_1471209 node_context_10_69671_1471209
  intro a
  fin_cases a
  · exact context_11_278684_1471134
  · exact context_11_278685_1471176
  · exact context_11_278686_1471208
  · exact context_11_278687_1470044

theorem unmarked_context_9_17417_1471210 : frontier 12 ⟨1471210, by decide⟩
    (prefixCache 9 17417) (prefixPartial 9 17417) = false := by
  decide +kernel

theorem node_context_9_17417_1471210 : EJMOriginalGlobalDAGData.nodes 12 ⟨1471210, by decide⟩ =
    .split (coordinate 9) (![⟨1470974, by decide⟩,⟨1468874, by decide⟩,⟨1471105, by decide⟩,⟨1471209, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17417_1471210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17417 ⟨1471210, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17417
    ⟨1471210, by decide⟩ (by decide) (![⟨1470974, by decide⟩,⟨1468874, by decide⟩,⟨1471105, by decide⟩,⟨1471209, by decide⟩]) unmarked_context_9_17417_1471210 node_context_9_17417_1471210
  intro a
  fin_cases a
  · exact context_10_69668_1470974
  · exact context_10_69669_1468874
  · exact context_10_69670_1471105
  · exact context_10_69671_1471209

theorem selected_cut_51156 : selected 11 ⟨1471262, by decide⟩
    (prefixPartial 10 69672) = some ⟨10, 2, 0, 1471262, 69672, 2769, 1048576⟩ := by
  decide +kernel

theorem context_10_69672_1471262 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69672 ⟨1471262, by decide⟩ :=
  accepted_of_selected 10 69672 ⟨1471262, by decide⟩ ⟨10, 2, 0, 1471262, 69672, 2769, 1048576⟩
    (by decide) selected_cut_51156

theorem selected_cut_51157 : selected 11 ⟨1471356, by decide⟩
    (prefixPartial 10 69673) = some ⟨10, 2, 0, 1471356, 69673, 3261, 1048576⟩ := by
  decide +kernel

theorem context_10_69673_1471356 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69673 ⟨1471356, by decide⟩ :=
  accepted_of_selected 10 69673 ⟨1471356, by decide⟩ ⟨10, 2, 0, 1471356, 69673, 3261, 1048576⟩
    (by decide) selected_cut_51157

theorem selected_cut_51158 : selected 11 ⟨1469103, by decide⟩
    (prefixPartial 10 69674) = some ⟨10, 1, 0, 1469103, 69674, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69674_1469103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69674 ⟨1469103, by decide⟩ :=
  accepted_of_selected 10 69674 ⟨1469103, by decide⟩ ⟨10, 1, 0, 1469103, 69674, 1, 1048576⟩
    (by decide) selected_cut_51158

theorem selected_cut_51159 : selected 11 ⟨1471404, by decide⟩
    (prefixPartial 10 69675) = some ⟨10, 2, 0, 1471404, 69675, 2077, 1048576⟩ := by
  decide +kernel

theorem context_10_69675_1471404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69675 ⟨1471404, by decide⟩ :=
  accepted_of_selected 10 69675 ⟨1471404, by decide⟩ ⟨10, 2, 0, 1471404, 69675, 2077, 1048576⟩
    (by decide) selected_cut_51159

theorem unmarked_context_9_17418_1471405 : frontier 12 ⟨1471405, by decide⟩
    (prefixCache 9 17418) (prefixPartial 9 17418) = false := by
  decide +kernel

theorem node_context_9_17418_1471405 : EJMOriginalGlobalDAGData.nodes 12 ⟨1471405, by decide⟩ =
    .split (coordinate 9) (![⟨1471262, by decide⟩,⟨1471356, by decide⟩,⟨1469103, by decide⟩,⟨1471404, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_17418_1471405 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17418 ⟨1471405, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 17418
    ⟨1471405, by decide⟩ (by decide) (![⟨1471262, by decide⟩,⟨1471356, by decide⟩,⟨1469103, by decide⟩,⟨1471404, by decide⟩]) unmarked_context_9_17418_1471405 node_context_9_17418_1471405
  intro a
  fin_cases a
  · exact context_10_69672_1471262
  · exact context_10_69673_1471356
  · exact context_10_69674_1469103
  · exact context_10_69675_1471404

theorem selected_cut_51160 : selected 12 ⟨1471520, by decide⟩
    (prefixPartial 9 17419) = some ⟨9, 2, 0, 1471520, 17419, 2793, 4194304⟩ := by
  decide +kernel

theorem context_9_17419_1471520 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 17419 ⟨1471520, by decide⟩ :=
  accepted_of_selected 9 17419 ⟨1471520, by decide⟩ ⟨9, 2, 0, 1471520, 17419, 2793, 4194304⟩
    (by decide) selected_cut_51160

theorem unmarked_context_8_4354_1471521 : frontier 13 ⟨1471521, by decide⟩
    (prefixCache 8 4354) (prefixPartial 8 4354) = false := by
  decide +kernel

theorem node_context_8_4354_1471521 : EJMOriginalGlobalDAGData.nodes 13 ⟨1471521, by decide⟩ =
    .split (coordinate 8) (![⟨1470834, by decide⟩,⟨1471210, by decide⟩,⟨1471405, by decide⟩,⟨1471520, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_4354_1471521 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4354 ⟨1471521, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 4354
    ⟨1471521, by decide⟩ (by decide) (![⟨1470834, by decide⟩,⟨1471210, by decide⟩,⟨1471405, by decide⟩,⟨1471520, by decide⟩]) unmarked_context_8_4354_1471521 node_context_8_4354_1471521
  intro a
  fin_cases a
  · exact context_9_17416_1470834
  · exact context_9_17417_1471210
  · exact context_9_17418_1471405
  · exact context_9_17419_1471520

theorem selected_cut_51161 : selected 13 ⟨14298, by decide⟩
    (prefixPartial 8 4355) = some ⟨8, 1, 0, 14298, 4355, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4355_14298 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4355 ⟨14298, by decide⟩ :=
  accepted_of_selected 8 4355 ⟨14298, by decide⟩ ⟨8, 1, 0, 14298, 4355, 1, 16777216⟩
    (by decide) selected_cut_51161

theorem unmarked_context_7_1088_1471522 : frontier 14 ⟨1471522, by decide⟩
    (prefixCache 7 1088) (prefixPartial 7 1088) = false := by
  decide +kernel

theorem node_context_7_1088_1471522 : EJMOriginalGlobalDAGData.nodes 14 ⟨1471522, by decide⟩ =
    .split (coordinate 7) (![⟨1469116, by decide⟩,⟨1470047, by decide⟩,⟨1471521, by decide⟩,⟨14298, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_7_1088_1471522 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 7 1088 ⟨1471522, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 7 1088
    ⟨1471522, by decide⟩ (by decide) (![⟨1469116, by decide⟩,⟨1470047, by decide⟩,⟨1471521, by decide⟩,⟨14298, by decide⟩]) unmarked_context_7_1088_1471522 node_context_7_1088_1471522
  intro a
  fin_cases a
  · exact context_8_4352_1469116
  · exact context_8_4353_1470047
  · exact context_8_4354_1471521
  · exact context_8_4355_14298

theorem selected_cut_51162 : selected 13 ⟨14300, by decide⟩
    (prefixPartial 8 4356) = some ⟨8, 1, 0, 14300, 4356, 1, 16777216⟩ := by
  decide +kernel

theorem context_8_4356_14300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 4356 ⟨14300, by decide⟩ :=
  accepted_of_selected 8 4356 ⟨14300, by decide⟩ ⟨8, 1, 0, 14300, 4356, 1, 16777216⟩
    (by decide) selected_cut_51162

theorem selected_cut_51163 : selected 11 ⟨1468246, by decide⟩
    (prefixPartial 10 69712) = some ⟨10, 1, 0, 1468246, 69712, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69712_1468246 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69712 ⟨1468246, by decide⟩ :=
  accepted_of_selected 10 69712 ⟨1468246, by decide⟩ ⟨10, 1, 0, 1468246, 69712, 1, 1048576⟩
    (by decide) selected_cut_51163

theorem selected_cut_51164 : selected 11 ⟨1471677, by decide⟩
    (prefixPartial 10 69713) = some ⟨10, 2, 0, 1471677, 69713, 3925, 1048576⟩ := by
  decide +kernel

theorem context_10_69713_1471677 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69713 ⟨1471677, by decide⟩ :=
  accepted_of_selected 10 69713 ⟨1471677, by decide⟩ ⟨10, 2, 0, 1471677, 69713, 3925, 1048576⟩
    (by decide) selected_cut_51164

theorem selected_cut_51165 : selected 10 ⟨1471735, by decide⟩
    (prefixPartial 11 278856) = some ⟨11, 2, 0, 1471735, 278856, 1581, 262144⟩ := by
  decide +kernel

theorem context_11_278856_1471735 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278856 ⟨1471735, by decide⟩ :=
  accepted_of_selected 11 278856 ⟨1471735, by decide⟩ ⟨11, 2, 0, 1471735, 278856, 1581, 262144⟩
    (by decide) selected_cut_51165

theorem selected_cut_51166 : selected 10 ⟨1471794, by decide⟩
    (prefixPartial 11 278857) = some ⟨11, 2, 0, 1471794, 278857, 1513, 262144⟩ := by
  decide +kernel

theorem context_11_278857_1471794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278857 ⟨1471794, by decide⟩ :=
  accepted_of_selected 11 278857 ⟨1471794, by decide⟩ ⟨11, 2, 0, 1471794, 278857, 1513, 262144⟩
    (by decide) selected_cut_51166

theorem selected_cut_51167 : selected 10 ⟨1468743, by decide⟩
    (prefixPartial 11 278858) = some ⟨11, 1, 0, 1468743, 278858, 1, 262144⟩ := by
  decide +kernel

theorem context_11_278858_1468743 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278858 ⟨1468743, by decide⟩ :=
  accepted_of_selected 11 278858 ⟨1468743, by decide⟩ ⟨11, 1, 0, 1468743, 278858, 1, 262144⟩
    (by decide) selected_cut_51167

theorem selected_cut_51168 : selected 10 ⟨1471849, by decide⟩
    (prefixPartial 11 278859) = some ⟨11, 2, 0, 1471849, 278859, 1117, 262144⟩ := by
  decide +kernel

theorem context_11_278859_1471849 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 278859 ⟨1471849, by decide⟩ :=
  accepted_of_selected 11 278859 ⟨1471849, by decide⟩ ⟨11, 2, 0, 1471849, 278859, 1117, 262144⟩
    (by decide) selected_cut_51168

theorem unmarked_context_10_69714_1471850 : frontier 11 ⟨1471850, by decide⟩
    (prefixCache 10 69714) (prefixPartial 10 69714) = false := by
  decide +kernel

theorem node_context_10_69714_1471850 : EJMOriginalGlobalDAGData.nodes 11 ⟨1471850, by decide⟩ =
    .split (coordinate 10) (![⟨1471735, by decide⟩,⟨1471794, by decide⟩,⟨1468743, by decide⟩,⟨1471849, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_69714_1471850 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69714 ⟨1471850, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 69714
    ⟨1471850, by decide⟩ (by decide) (![⟨1471735, by decide⟩,⟨1471794, by decide⟩,⟨1468743, by decide⟩,⟨1471849, by decide⟩]) unmarked_context_10_69714_1471850 node_context_10_69714_1471850
  intro a
  fin_cases a
  · exact context_11_278856_1471735
  · exact context_11_278857_1471794
  · exact context_11_278858_1468743
  · exact context_11_278859_1471849

theorem selected_cut_51169 : selected 11 ⟨3440, by decide⟩
    (prefixPartial 10 69715) = some ⟨10, 1, 0, 3440, 69715, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_69715_3440 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 69715 ⟨3440, by decide⟩ :=
  accepted_of_selected 10 69715 ⟨3440, by decide⟩ ⟨10, 1, 0, 3440, 69715, 1, 1048576⟩
    (by decide) selected_cut_51169

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
