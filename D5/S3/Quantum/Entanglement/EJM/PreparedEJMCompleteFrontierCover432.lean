/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover431
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem unmarked_context_11_83993_1134023 : frontier 10 ⟨1134023, by decide⟩
    (prefixCache 11 83993) (prefixPartial 11 83993) = false := by
  decide +kernel

theorem node_context_11_83993_1134023 : EJMOriginalGlobalDAGData.nodes 10 ⟨1134023, by decide⟩ =
    .split (coordinate 11) (![⟨1133973, by decide⟩,⟨642794, by decide⟩,⟨1134000, by decide⟩,⟨1134022, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83993_1134023 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83993 ⟨1134023, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83993
    ⟨1134023, by decide⟩ (by decide) (![⟨1133973, by decide⟩,⟨642794, by decide⟩,⟨1134000, by decide⟩,⟨1134022, by decide⟩]) unmarked_context_11_83993_1134023 node_context_11_83993_1134023
  intro a
  fin_cases a
  · exact context_12_335972_1133973
  · exact context_12_335973_642794
  · exact context_12_335974_1134000
  · exact context_12_335975_1134022

theorem selected_cut_41475 : selected 9 ⟨1134046, by decide⟩
    (prefixPartial 12 335976) = some ⟨12, 2, 0, 1134046, 335976, 1537, 65536⟩ := by
  decide +kernel

theorem context_12_335976_1134046 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335976 ⟨1134046, by decide⟩ :=
  accepted_of_selected 12 335976 ⟨1134046, by decide⟩ ⟨12, 2, 0, 1134046, 335976, 1537, 65536⟩
    (by decide) selected_cut_41475

theorem selected_cut_41476 : selected 9 ⟨1134074, by decide⟩
    (prefixPartial 12 335977) = some ⟨12, 2, 0, 1134074, 335977, 1589, 65536⟩ := by
  decide +kernel

theorem context_12_335977_1134074 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335977 ⟨1134074, by decide⟩ :=
  accepted_of_selected 12 335977 ⟨1134074, by decide⟩ ⟨12, 2, 0, 1134074, 335977, 1589, 65536⟩
    (by decide) selected_cut_41476

theorem selected_cut_41477 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 335978) = some ⟨12, 1, 0, 474208, 335978, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335978_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335978 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 335978 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 335978, 1, 65536⟩
    (by decide) selected_cut_41477

theorem selected_cut_41478 : selected 9 ⟨1134101, by decide⟩
    (prefixPartial 12 335979) = some ⟨12, 2, 0, 1134101, 335979, 1721, 65536⟩ := by
  decide +kernel

theorem context_12_335979_1134101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335979 ⟨1134101, by decide⟩ :=
  accepted_of_selected 12 335979 ⟨1134101, by decide⟩ ⟨12, 2, 0, 1134101, 335979, 1721, 65536⟩
    (by decide) selected_cut_41478

theorem unmarked_context_11_83994_1134102 : frontier 10 ⟨1134102, by decide⟩
    (prefixCache 11 83994) (prefixPartial 11 83994) = false := by
  decide +kernel

theorem node_context_11_83994_1134102 : EJMOriginalGlobalDAGData.nodes 10 ⟨1134102, by decide⟩ =
    .split (coordinate 11) (![⟨1134046, by decide⟩,⟨1134074, by decide⟩,⟨474208, by decide⟩,⟨1134101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83994_1134102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83994 ⟨1134102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83994
    ⟨1134102, by decide⟩ (by decide) (![⟨1134046, by decide⟩,⟨1134074, by decide⟩,⟨474208, by decide⟩,⟨1134101, by decide⟩]) unmarked_context_11_83994_1134102 node_context_11_83994_1134102
  intro a
  fin_cases a
  · exact context_12_335976_1134046
  · exact context_12_335977_1134074
  · exact context_12_335978_474208
  · exact context_12_335979_1134101

theorem selected_cut_41479 : selected 9 ⟨1134121, by decide⟩
    (prefixPartial 12 335980) = some ⟨12, 2, 0, 1134121, 335980, 1441, 65536⟩ := by
  decide +kernel

theorem context_12_335980_1134121 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335980 ⟨1134121, by decide⟩ :=
  accepted_of_selected 12 335980 ⟨1134121, by decide⟩ ⟨12, 2, 0, 1134121, 335980, 1441, 65536⟩
    (by decide) selected_cut_41479

theorem selected_cut_41480 : selected 9 ⟨1134150, by decide⟩
    (prefixPartial 12 335981) = some ⟨12, 2, 0, 1134150, 335981, 1517, 65536⟩ := by
  decide +kernel

theorem context_12_335981_1134150 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335981 ⟨1134150, by decide⟩ :=
  accepted_of_selected 12 335981 ⟨1134150, by decide⟩ ⟨12, 2, 0, 1134150, 335981, 1517, 65536⟩
    (by decide) selected_cut_41480

theorem selected_cut_41481 : selected 9 ⟨1134172, by decide⟩
    (prefixPartial 12 335982) = some ⟨12, 2, 0, 1134172, 335982, 1513, 65536⟩ := by
  decide +kernel

theorem context_12_335982_1134172 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335982 ⟨1134172, by decide⟩ :=
  accepted_of_selected 12 335982 ⟨1134172, by decide⟩ ⟨12, 2, 0, 1134172, 335982, 1513, 65536⟩
    (by decide) selected_cut_41481

theorem selected_cut_41482 : selected 9 ⟨1134190, by decide⟩
    (prefixPartial 12 335983) = some ⟨12, 2, 0, 1134190, 335983, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_335983_1134190 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335983 ⟨1134190, by decide⟩ :=
  accepted_of_selected 12 335983 ⟨1134190, by decide⟩ ⟨12, 2, 0, 1134190, 335983, 1465, 65536⟩
    (by decide) selected_cut_41482

theorem unmarked_context_11_83995_1134191 : frontier 10 ⟨1134191, by decide⟩
    (prefixCache 11 83995) (prefixPartial 11 83995) = false := by
  decide +kernel

theorem node_context_11_83995_1134191 : EJMOriginalGlobalDAGData.nodes 10 ⟨1134191, by decide⟩ =
    .split (coordinate 11) (![⟨1134121, by decide⟩,⟨1134150, by decide⟩,⟨1134172, by decide⟩,⟨1134190, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83995_1134191 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83995 ⟨1134191, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83995
    ⟨1134191, by decide⟩ (by decide) (![⟨1134121, by decide⟩,⟨1134150, by decide⟩,⟨1134172, by decide⟩,⟨1134190, by decide⟩]) unmarked_context_11_83995_1134191 node_context_11_83995_1134191
  intro a
  fin_cases a
  · exact context_12_335980_1134121
  · exact context_12_335981_1134150
  · exact context_12_335982_1134172
  · exact context_12_335983_1134190

theorem unmarked_context_10_20998_1134192 : frontier 11 ⟨1134192, by decide⟩
    (prefixCache 10 20998) (prefixPartial 10 20998) = false := by
  decide +kernel

theorem node_context_10_20998_1134192 : EJMOriginalGlobalDAGData.nodes 11 ⟨1134192, by decide⟩ =
    .split (coordinate 10) (![⟨1133943, by decide⟩,⟨1134023, by decide⟩,⟨1134102, by decide⟩,⟨1134191, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20998_1134192 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20998 ⟨1134192, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20998
    ⟨1134192, by decide⟩ (by decide) (![⟨1133943, by decide⟩,⟨1134023, by decide⟩,⟨1134102, by decide⟩,⟨1134191, by decide⟩]) unmarked_context_10_20998_1134192 node_context_10_20998_1134192
  intro a
  fin_cases a
  · exact context_11_83992_1133943
  · exact context_11_83993_1134023
  · exact context_11_83994_1134102
  · exact context_11_83995_1134191

theorem selected_cut_41483 : selected 9 ⟨985390, by decide⟩
    (prefixPartial 12 335984) = some ⟨12, 1, 0, 985390, 335984, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335984_985390 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335984 ⟨985390, by decide⟩ :=
  accepted_of_selected 12 335984 ⟨985390, by decide⟩ ⟨12, 1, 0, 985390, 335984, 1, 65536⟩
    (by decide) selected_cut_41483

theorem selected_cut_41484 : selected 9 ⟨1134212, by decide⟩
    (prefixPartial 12 335985) = some ⟨12, 2, 0, 1134212, 335985, 1433, 65536⟩ := by
  decide +kernel

theorem context_12_335985_1134212 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335985 ⟨1134212, by decide⟩ :=
  accepted_of_selected 12 335985 ⟨1134212, by decide⟩ ⟨12, 2, 0, 1134212, 335985, 1433, 65536⟩
    (by decide) selected_cut_41484

theorem selected_cut_41485 : selected 9 ⟨1134227, by decide⟩
    (prefixPartial 12 335986) = some ⟨12, 2, 0, 1134227, 335986, 1409, 65536⟩ := by
  decide +kernel

theorem context_12_335986_1134227 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335986 ⟨1134227, by decide⟩ :=
  accepted_of_selected 12 335986 ⟨1134227, by decide⟩ ⟨12, 2, 0, 1134227, 335986, 1409, 65536⟩
    (by decide) selected_cut_41485

theorem selected_cut_41486 : selected 9 ⟨1134249, by decide⟩
    (prefixPartial 12 335987) = some ⟨12, 2, 0, 1134249, 335987, 1485, 65536⟩ := by
  decide +kernel

theorem context_12_335987_1134249 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335987 ⟨1134249, by decide⟩ :=
  accepted_of_selected 12 335987 ⟨1134249, by decide⟩ ⟨12, 2, 0, 1134249, 335987, 1485, 65536⟩
    (by decide) selected_cut_41486

theorem unmarked_context_11_83996_1134250 : frontier 10 ⟨1134250, by decide⟩
    (prefixCache 11 83996) (prefixPartial 11 83996) = false := by
  decide +kernel

theorem node_context_11_83996_1134250 : EJMOriginalGlobalDAGData.nodes 10 ⟨1134250, by decide⟩ =
    .split (coordinate 11) (![⟨985390, by decide⟩,⟨1134212, by decide⟩,⟨1134227, by decide⟩,⟨1134249, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83996_1134250 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83996 ⟨1134250, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83996
    ⟨1134250, by decide⟩ (by decide) (![⟨985390, by decide⟩,⟨1134212, by decide⟩,⟨1134227, by decide⟩,⟨1134249, by decide⟩]) unmarked_context_11_83996_1134250 node_context_11_83996_1134250
  intro a
  fin_cases a
  · exact context_12_335984_985390
  · exact context_12_335985_1134212
  · exact context_12_335986_1134227
  · exact context_12_335987_1134249

theorem selected_cut_41487 : selected 9 ⟨1134272, by decide⟩
    (prefixPartial 12 335988) = some ⟨12, 2, 0, 1134272, 335988, 1449, 65536⟩ := by
  decide +kernel

theorem context_12_335988_1134272 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335988 ⟨1134272, by decide⟩ :=
  accepted_of_selected 12 335988 ⟨1134272, by decide⟩ ⟨12, 2, 0, 1134272, 335988, 1449, 65536⟩
    (by decide) selected_cut_41487

theorem selected_cut_41488 : selected 9 ⟨642794, by decide⟩
    (prefixPartial 12 335989) = some ⟨12, 1, 0, 642794, 335989, 1, 65536⟩ := by
  decide +kernel

theorem context_12_335989_642794 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335989 ⟨642794, by decide⟩ :=
  accepted_of_selected 12 335989 ⟨642794, by decide⟩ ⟨12, 1, 0, 642794, 335989, 1, 65536⟩
    (by decide) selected_cut_41488

theorem selected_cut_41489 : selected 9 ⟨1134295, by decide⟩
    (prefixPartial 12 335990) = some ⟨12, 2, 0, 1134295, 335990, 1477, 65536⟩ := by
  decide +kernel

theorem context_12_335990_1134295 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335990 ⟨1134295, by decide⟩ :=
  accepted_of_selected 12 335990 ⟨1134295, by decide⟩ ⟨12, 2, 0, 1134295, 335990, 1477, 65536⟩
    (by decide) selected_cut_41489

theorem selected_cut_41490 : selected 9 ⟨1134332, by decide⟩
    (prefixPartial 12 335991) = some ⟨12, 2, 0, 1134332, 335991, 1641, 65536⟩ := by
  decide +kernel

theorem context_12_335991_1134332 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335991 ⟨1134332, by decide⟩ :=
  accepted_of_selected 12 335991 ⟨1134332, by decide⟩ ⟨12, 2, 0, 1134332, 335991, 1641, 65536⟩
    (by decide) selected_cut_41490

theorem unmarked_context_11_83997_1134333 : frontier 10 ⟨1134333, by decide⟩
    (prefixCache 11 83997) (prefixPartial 11 83997) = false := by
  decide +kernel

theorem node_context_11_83997_1134333 : EJMOriginalGlobalDAGData.nodes 10 ⟨1134333, by decide⟩ =
    .split (coordinate 11) (![⟨1134272, by decide⟩,⟨642794, by decide⟩,⟨1134295, by decide⟩,⟨1134332, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83997_1134333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83997 ⟨1134333, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83997
    ⟨1134333, by decide⟩ (by decide) (![⟨1134272, by decide⟩,⟨642794, by decide⟩,⟨1134295, by decide⟩,⟨1134332, by decide⟩]) unmarked_context_11_83997_1134333 node_context_11_83997_1134333
  intro a
  fin_cases a
  · exact context_12_335988_1134272
  · exact context_12_335989_642794
  · exact context_12_335990_1134295
  · exact context_12_335991_1134332

theorem selected_cut_41491 : selected 9 ⟨1134352, by decide⟩
    (prefixPartial 12 335992) = some ⟨12, 2, 0, 1134352, 335992, 1349, 65536⟩ := by
  decide +kernel

theorem context_12_335992_1134352 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335992 ⟨1134352, by decide⟩ :=
  accepted_of_selected 12 335992 ⟨1134352, by decide⟩ ⟨12, 2, 0, 1134352, 335992, 1349, 65536⟩
    (by decide) selected_cut_41491

theorem selected_cut_41492 : selected 9 ⟨1134373, by decide⟩
    (prefixPartial 12 335993) = some ⟨12, 2, 0, 1134373, 335993, 1405, 65536⟩ := by
  decide +kernel

theorem context_12_335993_1134373 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335993 ⟨1134373, by decide⟩ :=
  accepted_of_selected 12 335993 ⟨1134373, by decide⟩ ⟨12, 2, 0, 1134373, 335993, 1405, 65536⟩
    (by decide) selected_cut_41492

theorem selected_cut_41493 : selected 9 ⟨1134392, by decide⟩
    (prefixPartial 12 335994) = some ⟨12, 2, 0, 1134392, 335994, 1357, 65536⟩ := by
  decide +kernel

theorem context_12_335994_1134392 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335994 ⟨1134392, by decide⟩ :=
  accepted_of_selected 12 335994 ⟨1134392, by decide⟩ ⟨12, 2, 0, 1134392, 335994, 1357, 65536⟩
    (by decide) selected_cut_41493

theorem selected_cut_41494 : selected 9 ⟨1134420, by decide⟩
    (prefixPartial 12 335995) = some ⟨12, 2, 0, 1134420, 335995, 1561, 65536⟩ := by
  decide +kernel

theorem context_12_335995_1134420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 335995 ⟨1134420, by decide⟩ :=
  accepted_of_selected 12 335995 ⟨1134420, by decide⟩ ⟨12, 2, 0, 1134420, 335995, 1561, 65536⟩
    (by decide) selected_cut_41494

theorem unmarked_context_11_83998_1134421 : frontier 10 ⟨1134421, by decide⟩
    (prefixCache 11 83998) (prefixPartial 11 83998) = false := by
  decide +kernel

theorem node_context_11_83998_1134421 : EJMOriginalGlobalDAGData.nodes 10 ⟨1134421, by decide⟩ =
    .split (coordinate 11) (![⟨1134352, by decide⟩,⟨1134373, by decide⟩,⟨1134392, by decide⟩,⟨1134420, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_83998_1134421 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83998 ⟨1134421, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 83998
    ⟨1134421, by decide⟩ (by decide) (![⟨1134352, by decide⟩,⟨1134373, by decide⟩,⟨1134392, by decide⟩,⟨1134420, by decide⟩]) unmarked_context_11_83998_1134421 node_context_11_83998_1134421
  intro a
  fin_cases a
  · exact context_12_335992_1134352
  · exact context_12_335993_1134373
  · exact context_12_335994_1134392
  · exact context_12_335995_1134420

theorem selected_cut_41495 : selected 10 ⟨1134488, by decide⟩
    (prefixPartial 11 83999) = some ⟨11, 2, 0, 1134488, 83999, 3961, 262144⟩ := by
  decide +kernel

theorem context_11_83999_1134488 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 83999 ⟨1134488, by decide⟩ :=
  accepted_of_selected 11 83999 ⟨1134488, by decide⟩ ⟨11, 2, 0, 1134488, 83999, 3961, 262144⟩
    (by decide) selected_cut_41495

theorem unmarked_context_10_20999_1134489 : frontier 11 ⟨1134489, by decide⟩
    (prefixCache 10 20999) (prefixPartial 10 20999) = false := by
  decide +kernel

theorem node_context_10_20999_1134489 : EJMOriginalGlobalDAGData.nodes 11 ⟨1134489, by decide⟩ =
    .split (coordinate 10) (![⟨1134250, by decide⟩,⟨1134333, by decide⟩,⟨1134421, by decide⟩,⟨1134488, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_20999_1134489 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 20999 ⟨1134489, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 20999
    ⟨1134489, by decide⟩ (by decide) (![⟨1134250, by decide⟩,⟨1134333, by decide⟩,⟨1134421, by decide⟩,⟨1134488, by decide⟩]) unmarked_context_10_20999_1134489 node_context_10_20999_1134489
  intro a
  fin_cases a
  · exact context_11_83996_1134250
  · exact context_11_83997_1134333
  · exact context_11_83998_1134421
  · exact context_11_83999_1134488

theorem unmarked_context_9_5249_1134490 : frontier 12 ⟨1134490, by decide⟩
    (prefixCache 9 5249) (prefixPartial 9 5249) = false := by
  decide +kernel

theorem node_context_9_5249_1134490 : EJMOriginalGlobalDAGData.nodes 12 ⟨1134490, by decide⟩ =
    .split (coordinate 9) (![⟨1133880, by decide⟩,⟨893098, by decide⟩,⟨1134192, by decide⟩,⟨1134489, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5249_1134490 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5249 ⟨1134490, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5249
    ⟨1134490, by decide⟩ (by decide) (![⟨1133880, by decide⟩,⟨893098, by decide⟩,⟨1134192, by decide⟩,⟨1134489, by decide⟩]) unmarked_context_9_5249_1134490 node_context_9_5249_1134490
  intro a
  fin_cases a
  · exact context_10_20996_1133880
  · exact context_10_20997_893098
  · exact context_10_20998_1134192
  · exact context_10_20999_1134489

theorem selected_cut_41496 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 84000) = some ⟨11, 1, 0, 907917, 84000, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84000_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84000 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 84000 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 84000, 1, 262144⟩
    (by decide) selected_cut_41496

theorem selected_cut_41497 : selected 9 ⟨1134501, by decide⟩
    (prefixPartial 12 336004) = some ⟨12, 2, 0, 1134501, 336004, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_336004_1134501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336004 ⟨1134501, by decide⟩ :=
  accepted_of_selected 12 336004 ⟨1134501, by decide⟩ ⟨12, 2, 0, 1134501, 336004, 1049, 65536⟩
    (by decide) selected_cut_41497

theorem selected_cut_41498 : selected 9 ⟨1134512, by decide⟩
    (prefixPartial 12 336005) = some ⟨12, 2, 0, 1134512, 336005, 1085, 65536⟩ := by
  decide +kernel

theorem context_12_336005_1134512 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336005 ⟨1134512, by decide⟩ :=
  accepted_of_selected 12 336005 ⟨1134512, by decide⟩ ⟨12, 2, 0, 1134512, 336005, 1085, 65536⟩
    (by decide) selected_cut_41498

theorem selected_cut_41499 : selected 9 ⟨1134528, by decide⟩
    (prefixPartial 12 336006) = some ⟨12, 2, 0, 1134528, 336006, 1137, 65536⟩ := by
  decide +kernel

theorem context_12_336006_1134528 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336006 ⟨1134528, by decide⟩ :=
  accepted_of_selected 12 336006 ⟨1134528, by decide⟩ ⟨12, 2, 0, 1134528, 336006, 1137, 65536⟩
    (by decide) selected_cut_41499

theorem selected_cut_41500 : selected 9 ⟨1134543, by decide⟩
    (prefixPartial 12 336007) = some ⟨12, 2, 0, 1134543, 336007, 1133, 65536⟩ := by
  decide +kernel

theorem context_12_336007_1134543 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336007 ⟨1134543, by decide⟩ :=
  accepted_of_selected 12 336007 ⟨1134543, by decide⟩ ⟨12, 2, 0, 1134543, 336007, 1133, 65536⟩
    (by decide) selected_cut_41500

theorem unmarked_context_11_84001_1134544 : frontier 10 ⟨1134544, by decide⟩
    (prefixCache 11 84001) (prefixPartial 11 84001) = false := by
  decide +kernel

theorem node_context_11_84001_1134544 : EJMOriginalGlobalDAGData.nodes 10 ⟨1134544, by decide⟩ =
    .split (coordinate 11) (![⟨1134501, by decide⟩,⟨1134512, by decide⟩,⟨1134528, by decide⟩,⟨1134543, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84001_1134544 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84001 ⟨1134544, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84001
    ⟨1134544, by decide⟩ (by decide) (![⟨1134501, by decide⟩,⟨1134512, by decide⟩,⟨1134528, by decide⟩,⟨1134543, by decide⟩]) unmarked_context_11_84001_1134544 node_context_11_84001_1134544
  intro a
  fin_cases a
  · exact context_12_336004_1134501
  · exact context_12_336005_1134512
  · exact context_12_336006_1134528
  · exact context_12_336007_1134543

theorem selected_cut_41501 : selected 10 ⟨1134601, by decide⟩
    (prefixPartial 11 84002) = some ⟨11, 2, 0, 1134601, 84002, 3513, 262144⟩ := by
  decide +kernel

theorem context_11_84002_1134601 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84002 ⟨1134601, by decide⟩ :=
  accepted_of_selected 11 84002 ⟨1134601, by decide⟩ ⟨11, 2, 0, 1134601, 84002, 3513, 262144⟩
    (by decide) selected_cut_41501

theorem selected_cut_41502 : selected 9 ⟨1134614, by decide⟩
    (prefixPartial 12 336012) = some ⟨12, 2, 0, 1134614, 336012, 929, 65536⟩ := by
  decide +kernel

theorem context_12_336012_1134614 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336012 ⟨1134614, by decide⟩ :=
  accepted_of_selected 12 336012 ⟨1134614, by decide⟩ ⟨12, 2, 0, 1134614, 336012, 929, 65536⟩
    (by decide) selected_cut_41502

theorem selected_cut_41503 : selected 9 ⟨1134626, by decide⟩
    (prefixPartial 12 336013) = some ⟨12, 2, 0, 1134626, 336013, 1105, 65536⟩ := by
  decide +kernel

theorem context_12_336013_1134626 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336013 ⟨1134626, by decide⟩ :=
  accepted_of_selected 12 336013 ⟨1134626, by decide⟩ ⟨12, 2, 0, 1134626, 336013, 1105, 65536⟩
    (by decide) selected_cut_41503

theorem selected_cut_41504 : selected 9 ⟨1134637, by decide⟩
    (prefixPartial 12 336014) = some ⟨12, 2, 0, 1134637, 336014, 1049, 65536⟩ := by
  decide +kernel

theorem context_12_336014_1134637 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336014 ⟨1134637, by decide⟩ :=
  accepted_of_selected 12 336014 ⟨1134637, by decide⟩ ⟨12, 2, 0, 1134637, 336014, 1049, 65536⟩
    (by decide) selected_cut_41504

theorem selected_cut_41505 : selected 9 ⟨1134654, by decide⟩
    (prefixPartial 12 336015) = some ⟨12, 2, 0, 1134654, 336015, 1105, 65536⟩ := by
  decide +kernel

theorem context_12_336015_1134654 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336015 ⟨1134654, by decide⟩ :=
  accepted_of_selected 12 336015 ⟨1134654, by decide⟩ ⟨12, 2, 0, 1134654, 336015, 1105, 65536⟩
    (by decide) selected_cut_41505

theorem unmarked_context_11_84003_1134655 : frontier 10 ⟨1134655, by decide⟩
    (prefixCache 11 84003) (prefixPartial 11 84003) = false := by
  decide +kernel

theorem node_context_11_84003_1134655 : EJMOriginalGlobalDAGData.nodes 10 ⟨1134655, by decide⟩ =
    .split (coordinate 11) (![⟨1134614, by decide⟩,⟨1134626, by decide⟩,⟨1134637, by decide⟩,⟨1134654, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84003_1134655 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84003 ⟨1134655, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84003
    ⟨1134655, by decide⟩ (by decide) (![⟨1134614, by decide⟩,⟨1134626, by decide⟩,⟨1134637, by decide⟩,⟨1134654, by decide⟩]) unmarked_context_11_84003_1134655 node_context_11_84003_1134655
  intro a
  fin_cases a
  · exact context_12_336012_1134614
  · exact context_12_336013_1134626
  · exact context_12_336014_1134637
  · exact context_12_336015_1134654

theorem unmarked_context_10_21000_1134656 : frontier 11 ⟨1134656, by decide⟩
    (prefixCache 10 21000) (prefixPartial 10 21000) = false := by
  decide +kernel

theorem node_context_10_21000_1134656 : EJMOriginalGlobalDAGData.nodes 11 ⟨1134656, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1134544, by decide⟩,⟨1134601, by decide⟩,⟨1134655, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21000_1134656 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21000 ⟨1134656, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21000
    ⟨1134656, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1134544, by decide⟩,⟨1134601, by decide⟩,⟨1134655, by decide⟩]) unmarked_context_10_21000_1134656 node_context_10_21000_1134656
  intro a
  fin_cases a
  · exact context_11_84000_907917
  · exact context_11_84001_1134544
  · exact context_11_84002_1134601
  · exact context_11_84003_1134655

theorem selected_cut_41506 : selected 10 ⟨1134702, by decide⟩
    (prefixPartial 11 84004) = some ⟨11, 2, 0, 1134702, 84004, 2969, 262144⟩ := by
  decide +kernel

theorem context_11_84004_1134702 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84004 ⟨1134702, by decide⟩ :=
  accepted_of_selected 11 84004 ⟨1134702, by decide⟩ ⟨11, 2, 0, 1134702, 84004, 2969, 262144⟩
    (by decide) selected_cut_41506

theorem selected_cut_41507 : selected 10 ⟨1134758, by decide⟩
    (prefixPartial 11 84005) = some ⟨11, 2, 0, 1134758, 84005, 3313, 262144⟩ := by
  decide +kernel

theorem context_11_84005_1134758 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84005 ⟨1134758, by decide⟩ :=
  accepted_of_selected 11 84005 ⟨1134758, by decide⟩ ⟨11, 2, 0, 1134758, 84005, 3313, 262144⟩
    (by decide) selected_cut_41507

theorem selected_cut_41508 : selected 10 ⟨1134798, by decide⟩
    (prefixPartial 11 84006) = some ⟨11, 2, 0, 1134798, 84006, 2753, 262144⟩ := by
  decide +kernel

theorem context_11_84006_1134798 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84006 ⟨1134798, by decide⟩ :=
  accepted_of_selected 11 84006 ⟨1134798, by decide⟩ ⟨11, 2, 0, 1134798, 84006, 2753, 262144⟩
    (by decide) selected_cut_41508

theorem selected_cut_41509 : selected 10 ⟨1134846, by decide⟩
    (prefixPartial 11 84007) = some ⟨11, 2, 0, 1134846, 84007, 3453, 262144⟩ := by
  decide +kernel

theorem context_11_84007_1134846 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84007 ⟨1134846, by decide⟩ :=
  accepted_of_selected 11 84007 ⟨1134846, by decide⟩ ⟨11, 2, 0, 1134846, 84007, 3453, 262144⟩
    (by decide) selected_cut_41509

theorem unmarked_context_10_21001_1134847 : frontier 11 ⟨1134847, by decide⟩
    (prefixCache 10 21001) (prefixPartial 10 21001) = false := by
  decide +kernel

theorem node_context_10_21001_1134847 : EJMOriginalGlobalDAGData.nodes 11 ⟨1134847, by decide⟩ =
    .split (coordinate 10) (![⟨1134702, by decide⟩,⟨1134758, by decide⟩,⟨1134798, by decide⟩,⟨1134846, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21001_1134847 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21001 ⟨1134847, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21001
    ⟨1134847, by decide⟩ (by decide) (![⟨1134702, by decide⟩,⟨1134758, by decide⟩,⟨1134798, by decide⟩,⟨1134846, by decide⟩]) unmarked_context_10_21001_1134847 node_context_10_21001_1134847
  intro a
  fin_cases a
  · exact context_11_84004_1134702
  · exact context_11_84005_1134758
  · exact context_11_84006_1134798
  · exact context_11_84007_1134846

theorem selected_cut_41510 : selected 10 ⟨1134865, by decide⟩
    (prefixPartial 11 84008) = some ⟨11, 2, 0, 1134865, 84008, 1525, 262144⟩ := by
  decide +kernel

theorem context_11_84008_1134865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84008 ⟨1134865, by decide⟩ :=
  accepted_of_selected 11 84008 ⟨1134865, by decide⟩ ⟨11, 2, 0, 1134865, 84008, 1525, 262144⟩
    (by decide) selected_cut_41510

theorem selected_cut_41511 : selected 10 ⟨1134906, by decide⟩
    (prefixPartial 11 84009) = some ⟨11, 2, 0, 1134906, 84009, 2429, 262144⟩ := by
  decide +kernel

theorem context_11_84009_1134906 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84009 ⟨1134906, by decide⟩ :=
  accepted_of_selected 11 84009 ⟨1134906, by decide⟩ ⟨11, 2, 0, 1134906, 84009, 2429, 262144⟩
    (by decide) selected_cut_41511

theorem selected_cut_41512 : selected 10 ⟨1109453, by decide⟩
    (prefixPartial 11 84010) = some ⟨11, 1, 0, 1109453, 84010, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84010_1109453 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84010 ⟨1109453, by decide⟩ :=
  accepted_of_selected 11 84010 ⟨1109453, by decide⟩ ⟨11, 1, 0, 1109453, 84010, 1, 262144⟩
    (by decide) selected_cut_41512

theorem selected_cut_41513 : selected 10 ⟨1134941, by decide⟩
    (prefixPartial 11 84011) = some ⟨11, 2, 0, 1134941, 84011, 2277, 262144⟩ := by
  decide +kernel

theorem context_11_84011_1134941 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84011 ⟨1134941, by decide⟩ :=
  accepted_of_selected 11 84011 ⟨1134941, by decide⟩ ⟨11, 2, 0, 1134941, 84011, 2277, 262144⟩
    (by decide) selected_cut_41513

theorem unmarked_context_10_21002_1134942 : frontier 11 ⟨1134942, by decide⟩
    (prefixCache 10 21002) (prefixPartial 10 21002) = false := by
  decide +kernel

theorem node_context_10_21002_1134942 : EJMOriginalGlobalDAGData.nodes 11 ⟨1134942, by decide⟩ =
    .split (coordinate 10) (![⟨1134865, by decide⟩,⟨1134906, by decide⟩,⟨1109453, by decide⟩,⟨1134941, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21002_1134942 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21002 ⟨1134942, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21002
    ⟨1134942, by decide⟩ (by decide) (![⟨1134865, by decide⟩,⟨1134906, by decide⟩,⟨1109453, by decide⟩,⟨1134941, by decide⟩]) unmarked_context_10_21002_1134942 node_context_10_21002_1134942
  intro a
  fin_cases a
  · exact context_11_84008_1134865
  · exact context_11_84009_1134906
  · exact context_11_84010_1109453
  · exact context_11_84011_1134941

theorem selected_cut_41514 : selected 10 ⟨1134972, by decide⟩
    (prefixPartial 11 84012) = some ⟨11, 2, 0, 1134972, 84012, 2125, 262144⟩ := by
  decide +kernel

theorem context_11_84012_1134972 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84012 ⟨1134972, by decide⟩ :=
  accepted_of_selected 11 84012 ⟨1134972, by decide⟩ ⟨11, 2, 0, 1134972, 84012, 2125, 262144⟩
    (by decide) selected_cut_41514

theorem selected_cut_41515 : selected 10 ⟨1135025, by decide⟩
    (prefixPartial 11 84013) = some ⟨11, 2, 0, 1135025, 84013, 2821, 262144⟩ := by
  decide +kernel

theorem context_11_84013_1135025 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84013 ⟨1135025, by decide⟩ :=
  accepted_of_selected 11 84013 ⟨1135025, by decide⟩ ⟨11, 2, 0, 1135025, 84013, 2821, 262144⟩
    (by decide) selected_cut_41515

theorem selected_cut_41516 : selected 10 ⟨1135065, by decide⟩
    (prefixPartial 11 84014) = some ⟨11, 2, 0, 1135065, 84014, 2085, 262144⟩ := by
  decide +kernel

theorem context_11_84014_1135065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84014 ⟨1135065, by decide⟩ :=
  accepted_of_selected 11 84014 ⟨1135065, by decide⟩ ⟨11, 2, 0, 1135065, 84014, 2085, 262144⟩
    (by decide) selected_cut_41516

theorem selected_cut_41517 : selected 10 ⟨1135101, by decide⟩
    (prefixPartial 11 84015) = some ⟨11, 2, 0, 1135101, 84015, 1769, 262144⟩ := by
  decide +kernel

theorem context_11_84015_1135101 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84015 ⟨1135101, by decide⟩ :=
  accepted_of_selected 11 84015 ⟨1135101, by decide⟩ ⟨11, 2, 0, 1135101, 84015, 1769, 262144⟩
    (by decide) selected_cut_41517

theorem unmarked_context_10_21003_1135102 : frontier 11 ⟨1135102, by decide⟩
    (prefixCache 10 21003) (prefixPartial 10 21003) = false := by
  decide +kernel

theorem node_context_10_21003_1135102 : EJMOriginalGlobalDAGData.nodes 11 ⟨1135102, by decide⟩ =
    .split (coordinate 10) (![⟨1134972, by decide⟩,⟨1135025, by decide⟩,⟨1135065, by decide⟩,⟨1135101, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21003_1135102 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21003 ⟨1135102, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21003
    ⟨1135102, by decide⟩ (by decide) (![⟨1134972, by decide⟩,⟨1135025, by decide⟩,⟨1135065, by decide⟩,⟨1135101, by decide⟩]) unmarked_context_10_21003_1135102 node_context_10_21003_1135102
  intro a
  fin_cases a
  · exact context_11_84012_1134972
  · exact context_11_84013_1135025
  · exact context_11_84014_1135065
  · exact context_11_84015_1135101

theorem unmarked_context_9_5250_1135103 : frontier 12 ⟨1135103, by decide⟩
    (prefixCache 9 5250) (prefixPartial 9 5250) = false := by
  decide +kernel

theorem node_context_9_5250_1135103 : EJMOriginalGlobalDAGData.nodes 12 ⟨1135103, by decide⟩ =
    .split (coordinate 9) (![⟨1134656, by decide⟩,⟨1134847, by decide⟩,⟨1134942, by decide⟩,⟨1135102, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5250_1135103 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5250 ⟨1135103, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5250
    ⟨1135103, by decide⟩ (by decide) (![⟨1134656, by decide⟩,⟨1134847, by decide⟩,⟨1134942, by decide⟩,⟨1135102, by decide⟩]) unmarked_context_9_5250_1135103 node_context_9_5250_1135103
  intro a
  fin_cases a
  · exact context_10_21000_1134656
  · exact context_10_21001_1134847
  · exact context_10_21002_1134942
  · exact context_10_21003_1135102

theorem selected_cut_41518 : selected 10 ⟨907917, by decide⟩
    (prefixPartial 11 84016) = some ⟨11, 1, 0, 907917, 84016, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84016_907917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84016 ⟨907917, by decide⟩ :=
  accepted_of_selected 11 84016 ⟨907917, by decide⟩ ⟨11, 1, 0, 907917, 84016, 1, 262144⟩
    (by decide) selected_cut_41518

theorem selected_cut_41519 : selected 10 ⟨1135119, by decide⟩
    (prefixPartial 11 84017) = some ⟨11, 2, 0, 1135119, 84017, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_84017_1135119 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84017 ⟨1135119, by decide⟩ :=
  accepted_of_selected 11 84017 ⟨1135119, by decide⟩ ⟨11, 2, 0, 1135119, 84017, 1685, 262144⟩
    (by decide) selected_cut_41519

theorem selected_cut_41520 : selected 10 ⟨1135136, by decide⟩
    (prefixPartial 11 84018) = some ⟨11, 2, 0, 1135136, 84018, 1585, 262144⟩ := by
  decide +kernel

theorem context_11_84018_1135136 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84018 ⟨1135136, by decide⟩ :=
  accepted_of_selected 11 84018 ⟨1135136, by decide⟩ ⟨11, 2, 0, 1135136, 84018, 1585, 262144⟩
    (by decide) selected_cut_41520

theorem selected_cut_41521 : selected 10 ⟨1135154, by decide⟩
    (prefixPartial 11 84019) = some ⟨11, 2, 0, 1135154, 84019, 1141, 262144⟩ := by
  decide +kernel

theorem context_11_84019_1135154 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84019 ⟨1135154, by decide⟩ :=
  accepted_of_selected 11 84019 ⟨1135154, by decide⟩ ⟨11, 2, 0, 1135154, 84019, 1141, 262144⟩
    (by decide) selected_cut_41521

theorem unmarked_context_10_21004_1135155 : frontier 11 ⟨1135155, by decide⟩
    (prefixCache 10 21004) (prefixPartial 10 21004) = false := by
  decide +kernel

theorem node_context_10_21004_1135155 : EJMOriginalGlobalDAGData.nodes 11 ⟨1135155, by decide⟩ =
    .split (coordinate 10) (![⟨907917, by decide⟩,⟨1135119, by decide⟩,⟨1135136, by decide⟩,⟨1135154, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21004_1135155 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21004 ⟨1135155, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21004
    ⟨1135155, by decide⟩ (by decide) (![⟨907917, by decide⟩,⟨1135119, by decide⟩,⟨1135136, by decide⟩,⟨1135154, by decide⟩]) unmarked_context_10_21004_1135155 node_context_10_21004_1135155
  intro a
  fin_cases a
  · exact context_11_84016_907917
  · exact context_11_84017_1135119
  · exact context_11_84018_1135136
  · exact context_11_84019_1135154

theorem selected_cut_41522 : selected 11 ⟨1135200, by decide⟩
    (prefixPartial 10 21005) = some ⟨10, 2, 0, 1135200, 21005, 3725, 1048576⟩ := by
  decide +kernel

theorem context_10_21005_1135200 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21005 ⟨1135200, by decide⟩ :=
  accepted_of_selected 10 21005 ⟨1135200, by decide⟩ ⟨10, 2, 0, 1135200, 21005, 3725, 1048576⟩
    (by decide) selected_cut_41522

theorem selected_cut_41523 : selected 11 ⟨1135244, by decide⟩
    (prefixPartial 10 21006) = some ⟨10, 2, 0, 1135244, 21006, 2137, 1048576⟩ := by
  decide +kernel

theorem context_10_21006_1135244 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21006 ⟨1135244, by decide⟩ :=
  accepted_of_selected 10 21006 ⟨1135244, by decide⟩ ⟨10, 2, 0, 1135244, 21006, 2137, 1048576⟩
    (by decide) selected_cut_41523

theorem selected_cut_41524 : selected 11 ⟨1135259, by decide⟩
    (prefixPartial 10 21007) = some ⟨10, 2, 0, 1135259, 21007, 469, 1048576⟩ := by
  decide +kernel

theorem context_10_21007_1135259 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21007 ⟨1135259, by decide⟩ :=
  accepted_of_selected 10 21007 ⟨1135259, by decide⟩ ⟨10, 2, 0, 1135259, 21007, 469, 1048576⟩
    (by decide) selected_cut_41524

theorem unmarked_context_9_5251_1135260 : frontier 12 ⟨1135260, by decide⟩
    (prefixCache 9 5251) (prefixPartial 9 5251) = false := by
  decide +kernel

theorem node_context_9_5251_1135260 : EJMOriginalGlobalDAGData.nodes 12 ⟨1135260, by decide⟩ =
    .split (coordinate 9) (![⟨1135155, by decide⟩,⟨1135200, by decide⟩,⟨1135244, by decide⟩,⟨1135259, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_5251_1135260 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 5251 ⟨1135260, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 5251
    ⟨1135260, by decide⟩ (by decide) (![⟨1135155, by decide⟩,⟨1135200, by decide⟩,⟨1135244, by decide⟩,⟨1135259, by decide⟩]) unmarked_context_9_5251_1135260 node_context_9_5251_1135260
  intro a
  fin_cases a
  · exact context_10_21004_1135155
  · exact context_10_21005_1135200
  · exact context_10_21006_1135244
  · exact context_10_21007_1135259

theorem unmarked_context_8_1312_1135261 : frontier 13 ⟨1135261, by decide⟩
    (prefixCache 8 1312) (prefixPartial 8 1312) = false := by
  decide +kernel

theorem node_context_8_1312_1135261 : EJMOriginalGlobalDAGData.nodes 13 ⟨1135261, by decide⟩ =
    .split (coordinate 8) (![⟨1133605, by decide⟩,⟨1134490, by decide⟩,⟨1135103, by decide⟩,⟨1135260, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1312_1135261 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1312 ⟨1135261, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1312
    ⟨1135261, by decide⟩ (by decide) (![⟨1133605, by decide⟩,⟨1134490, by decide⟩,⟨1135103, by decide⟩,⟨1135260, by decide⟩]) unmarked_context_8_1312_1135261 node_context_8_1312_1135261
  intro a
  fin_cases a
  · exact context_9_5248_1133605
  · exact context_9_5249_1134490
  · exact context_9_5250_1135103
  · exact context_9_5251_1135260

theorem selected_cut_41525 : selected 10 ⟨434745, by decide⟩
    (prefixPartial 11 84032) = some ⟨11, 1, 0, 434745, 84032, 1, 262144⟩ := by
  decide +kernel

theorem context_11_84032_434745 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84032 ⟨434745, by decide⟩ :=
  accepted_of_selected 11 84032 ⟨434745, by decide⟩ ⟨11, 1, 0, 434745, 84032, 1, 262144⟩
    (by decide) selected_cut_41525

theorem selected_cut_41526 : selected 10 ⟨1135353, by decide⟩
    (prefixPartial 11 84033) = some ⟨11, 2, 0, 1135353, 84033, 2521, 262144⟩ := by
  decide +kernel

theorem context_11_84033_1135353 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84033 ⟨1135353, by decide⟩ :=
  accepted_of_selected 11 84033 ⟨1135353, by decide⟩ ⟨11, 2, 0, 1135353, 84033, 2521, 262144⟩
    (by decide) selected_cut_41526

theorem selected_cut_41527 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 336136) = some ⟨12, 1, 0, 448748, 336136, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336136_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336136 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 336136 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 336136, 1, 65536⟩
    (by decide) selected_cut_41527

theorem selected_cut_41528 : selected 9 ⟨1135414, by decide⟩
    (prefixPartial 12 336137) = some ⟨12, 2, 0, 1135414, 336137, 2725, 65536⟩ := by
  decide +kernel

theorem context_12_336137_1135414 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336137 ⟨1135414, by decide⟩ :=
  accepted_of_selected 12 336137 ⟨1135414, by decide⟩ ⟨12, 2, 0, 1135414, 336137, 2725, 65536⟩
    (by decide) selected_cut_41528

theorem selected_cut_41529 : selected 9 ⟨1135462, by decide⟩
    (prefixPartial 12 336138) = some ⟨12, 2, 0, 1135462, 336138, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_336138_1135462 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336138 ⟨1135462, by decide⟩ :=
  accepted_of_selected 12 336138 ⟨1135462, by decide⟩ ⟨12, 2, 0, 1135462, 336138, 2097, 65536⟩
    (by decide) selected_cut_41529

theorem selected_cut_41530 : selected 9 ⟨1135507, by decide⟩
    (prefixPartial 12 336139) = some ⟨12, 2, 0, 1135507, 336139, 2265, 65536⟩ := by
  decide +kernel

theorem context_12_336139_1135507 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336139 ⟨1135507, by decide⟩ :=
  accepted_of_selected 12 336139 ⟨1135507, by decide⟩ ⟨12, 2, 0, 1135507, 336139, 2265, 65536⟩
    (by decide) selected_cut_41530

theorem unmarked_context_11_84034_1135508 : frontier 10 ⟨1135508, by decide⟩
    (prefixCache 11 84034) (prefixPartial 11 84034) = false := by
  decide +kernel

theorem node_context_11_84034_1135508 : EJMOriginalGlobalDAGData.nodes 10 ⟨1135508, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1135414, by decide⟩,⟨1135462, by decide⟩,⟨1135507, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84034_1135508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84034 ⟨1135508, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84034
    ⟨1135508, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1135414, by decide⟩,⟨1135462, by decide⟩,⟨1135507, by decide⟩]) unmarked_context_11_84034_1135508 node_context_11_84034_1135508
  intro a
  fin_cases a
  · exact context_12_336136_448748
  · exact context_12_336137_1135414
  · exact context_12_336138_1135462
  · exact context_12_336139_1135507

theorem selected_cut_41531 : selected 9 ⟨448748, by decide⟩
    (prefixPartial 12 336140) = some ⟨12, 1, 0, 448748, 336140, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336140_448748 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336140 ⟨448748, by decide⟩ :=
  accepted_of_selected 12 336140 ⟨448748, by decide⟩ ⟨12, 1, 0, 448748, 336140, 1, 65536⟩
    (by decide) selected_cut_41531

theorem selected_cut_41532 : selected 9 ⟨1135542, by decide⟩
    (prefixPartial 12 336141) = some ⟨12, 2, 0, 1135542, 336141, 1253, 65536⟩ := by
  decide +kernel

theorem context_12_336141_1135542 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336141 ⟨1135542, by decide⟩ :=
  accepted_of_selected 12 336141 ⟨1135542, by decide⟩ ⟨12, 2, 0, 1135542, 336141, 1253, 65536⟩
    (by decide) selected_cut_41532

theorem selected_cut_41533 : selected 9 ⟨1135587, by decide⟩
    (prefixPartial 12 336142) = some ⟨12, 2, 0, 1135587, 336142, 1853, 65536⟩ := by
  decide +kernel

theorem context_12_336142_1135587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336142 ⟨1135587, by decide⟩ :=
  accepted_of_selected 12 336142 ⟨1135587, by decide⟩ ⟨12, 2, 0, 1135587, 336142, 1853, 65536⟩
    (by decide) selected_cut_41533

theorem selected_cut_41534 : selected 9 ⟨1135621, by decide⟩
    (prefixPartial 12 336143) = some ⟨12, 2, 0, 1135621, 336143, 2069, 65536⟩ := by
  decide +kernel

theorem context_12_336143_1135621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336143 ⟨1135621, by decide⟩ :=
  accepted_of_selected 12 336143 ⟨1135621, by decide⟩ ⟨12, 2, 0, 1135621, 336143, 2069, 65536⟩
    (by decide) selected_cut_41534

theorem unmarked_context_11_84035_1135622 : frontier 10 ⟨1135622, by decide⟩
    (prefixCache 11 84035) (prefixPartial 11 84035) = false := by
  decide +kernel

theorem node_context_11_84035_1135622 : EJMOriginalGlobalDAGData.nodes 10 ⟨1135622, by decide⟩ =
    .split (coordinate 11) (![⟨448748, by decide⟩,⟨1135542, by decide⟩,⟨1135587, by decide⟩,⟨1135621, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84035_1135622 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84035 ⟨1135622, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84035
    ⟨1135622, by decide⟩ (by decide) (![⟨448748, by decide⟩,⟨1135542, by decide⟩,⟨1135587, by decide⟩,⟨1135621, by decide⟩]) unmarked_context_11_84035_1135622 node_context_11_84035_1135622
  intro a
  fin_cases a
  · exact context_12_336140_448748
  · exact context_12_336141_1135542
  · exact context_12_336142_1135587
  · exact context_12_336143_1135621

theorem unmarked_context_10_21008_1135623 : frontier 11 ⟨1135623, by decide⟩
    (prefixCache 10 21008) (prefixPartial 10 21008) = false := by
  decide +kernel

theorem node_context_10_21008_1135623 : EJMOriginalGlobalDAGData.nodes 11 ⟨1135623, by decide⟩ =
    .split (coordinate 10) (![⟨434745, by decide⟩,⟨1135353, by decide⟩,⟨1135508, by decide⟩,⟨1135622, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21008_1135623 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21008 ⟨1135623, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21008
    ⟨1135623, by decide⟩ (by decide) (![⟨434745, by decide⟩,⟨1135353, by decide⟩,⟨1135508, by decide⟩,⟨1135622, by decide⟩]) unmarked_context_10_21008_1135623 node_context_10_21008_1135623
  intro a
  fin_cases a
  · exact context_11_84032_434745
  · exact context_11_84033_1135353
  · exact context_11_84034_1135508
  · exact context_11_84035_1135622

theorem selected_cut_41535 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336144) = some ⟨12, 1, 0, 1108174, 336144, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336144_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336144 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336144 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336144, 1, 65536⟩
    (by decide) selected_cut_41535

theorem selected_cut_41536 : selected 9 ⟨1135667, by decide⟩
    (prefixPartial 12 336145) = some ⟨12, 2, 0, 1135667, 336145, 2309, 65536⟩ := by
  decide +kernel

theorem context_12_336145_1135667 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336145 ⟨1135667, by decide⟩ :=
  accepted_of_selected 12 336145 ⟨1135667, by decide⟩ ⟨12, 2, 0, 1135667, 336145, 2309, 65536⟩
    (by decide) selected_cut_41536

theorem selected_cut_41537 : selected 9 ⟨1135698, by decide⟩
    (prefixPartial 12 336146) = some ⟨12, 2, 0, 1135698, 336146, 2093, 65536⟩ := by
  decide +kernel

theorem context_12_336146_1135698 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336146 ⟨1135698, by decide⟩ :=
  accepted_of_selected 12 336146 ⟨1135698, by decide⟩ ⟨12, 2, 0, 1135698, 336146, 2093, 65536⟩
    (by decide) selected_cut_41537

theorem selected_cut_41538 : selected 9 ⟨1135722, by decide⟩
    (prefixPartial 12 336147) = some ⟨12, 2, 0, 1135722, 336147, 2201, 65536⟩ := by
  decide +kernel

theorem context_12_336147_1135722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336147 ⟨1135722, by decide⟩ :=
  accepted_of_selected 12 336147 ⟨1135722, by decide⟩ ⟨12, 2, 0, 1135722, 336147, 2201, 65536⟩
    (by decide) selected_cut_41538

theorem unmarked_context_11_84036_1135723 : frontier 10 ⟨1135723, by decide⟩
    (prefixCache 11 84036) (prefixPartial 11 84036) = false := by
  decide +kernel

theorem node_context_11_84036_1135723 : EJMOriginalGlobalDAGData.nodes 10 ⟨1135723, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1135667, by decide⟩,⟨1135698, by decide⟩,⟨1135722, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84036_1135723 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84036 ⟨1135723, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84036
    ⟨1135723, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1135667, by decide⟩,⟨1135698, by decide⟩,⟨1135722, by decide⟩]) unmarked_context_11_84036_1135723 node_context_11_84036_1135723
  intro a
  fin_cases a
  · exact context_12_336144_1108174
  · exact context_12_336145_1135667
  · exact context_12_336146_1135698
  · exact context_12_336147_1135722

theorem selected_cut_41539 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336148) = some ⟨12, 1, 0, 1108174, 336148, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336148_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336148 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336148 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336148, 1, 65536⟩
    (by decide) selected_cut_41539

theorem selected_cut_41540 : selected 9 ⟨308705, by decide⟩
    (prefixPartial 12 336149) = some ⟨12, 1, 0, 308705, 336149, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336149_308705 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336149 ⟨308705, by decide⟩ :=
  accepted_of_selected 12 336149 ⟨308705, by decide⟩ ⟨12, 1, 0, 308705, 336149, 1, 65536⟩
    (by decide) selected_cut_41540

theorem selected_cut_41541 : selected 9 ⟨1135763, by decide⟩
    (prefixPartial 12 336150) = some ⟨12, 2, 0, 1135763, 336150, 2133, 65536⟩ := by
  decide +kernel

theorem context_12_336150_1135763 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336150 ⟨1135763, by decide⟩ :=
  accepted_of_selected 12 336150 ⟨1135763, by decide⟩ ⟨12, 2, 0, 1135763, 336150, 2133, 65536⟩
    (by decide) selected_cut_41541

theorem selected_cut_41542 : selected 9 ⟨1135804, by decide⟩
    (prefixPartial 12 336151) = some ⟨12, 2, 0, 1135804, 336151, 2229, 65536⟩ := by
  decide +kernel

theorem context_12_336151_1135804 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336151 ⟨1135804, by decide⟩ :=
  accepted_of_selected 12 336151 ⟨1135804, by decide⟩ ⟨12, 2, 0, 1135804, 336151, 2229, 65536⟩
    (by decide) selected_cut_41542

theorem unmarked_context_11_84037_1135805 : frontier 10 ⟨1135805, by decide⟩
    (prefixCache 11 84037) (prefixPartial 11 84037) = false := by
  decide +kernel

theorem node_context_11_84037_1135805 : EJMOriginalGlobalDAGData.nodes 10 ⟨1135805, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1135763, by decide⟩,⟨1135804, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84037_1135805 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84037 ⟨1135805, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84037
    ⟨1135805, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨308705, by decide⟩,⟨1135763, by decide⟩,⟨1135804, by decide⟩]) unmarked_context_11_84037_1135805 node_context_11_84037_1135805
  intro a
  fin_cases a
  · exact context_12_336148_1108174
  · exact context_12_336149_308705
  · exact context_12_336150_1135763
  · exact context_12_336151_1135804

theorem selected_cut_41543 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336152) = some ⟨12, 1, 0, 1108174, 336152, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336152_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336152 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336152 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336152, 1, 65536⟩
    (by decide) selected_cut_41543

theorem selected_cut_41544 : selected 9 ⟨1135851, by decide⟩
    (prefixPartial 12 336153) = some ⟨12, 2, 0, 1135851, 336153, 2245, 65536⟩ := by
  decide +kernel

theorem context_12_336153_1135851 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336153 ⟨1135851, by decide⟩ :=
  accepted_of_selected 12 336153 ⟨1135851, by decide⟩ ⟨12, 2, 0, 1135851, 336153, 2245, 65536⟩
    (by decide) selected_cut_41544

theorem selected_cut_41545 : selected 9 ⟨1135884, by decide⟩
    (prefixPartial 12 336154) = some ⟨12, 2, 0, 1135884, 336154, 2097, 65536⟩ := by
  decide +kernel

theorem context_12_336154_1135884 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336154 ⟨1135884, by decide⟩ :=
  accepted_of_selected 12 336154 ⟨1135884, by decide⟩ ⟨12, 2, 0, 1135884, 336154, 2097, 65536⟩
    (by decide) selected_cut_41545

theorem selected_cut_41546 : selected 9 ⟨1135912, by decide⟩
    (prefixPartial 12 336155) = some ⟨12, 2, 0, 1135912, 336155, 2177, 65536⟩ := by
  decide +kernel

theorem context_12_336155_1135912 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336155 ⟨1135912, by decide⟩ :=
  accepted_of_selected 12 336155 ⟨1135912, by decide⟩ ⟨12, 2, 0, 1135912, 336155, 2177, 65536⟩
    (by decide) selected_cut_41546

theorem unmarked_context_11_84038_1135913 : frontier 10 ⟨1135913, by decide⟩
    (prefixCache 11 84038) (prefixPartial 11 84038) = false := by
  decide +kernel

theorem node_context_11_84038_1135913 : EJMOriginalGlobalDAGData.nodes 10 ⟨1135913, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1135851, by decide⟩,⟨1135884, by decide⟩,⟨1135912, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84038_1135913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84038 ⟨1135913, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84038
    ⟨1135913, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1135851, by decide⟩,⟨1135884, by decide⟩,⟨1135912, by decide⟩]) unmarked_context_11_84038_1135913 node_context_11_84038_1135913
  intro a
  fin_cases a
  · exact context_12_336152_1108174
  · exact context_12_336153_1135851
  · exact context_12_336154_1135884
  · exact context_12_336155_1135912

theorem selected_cut_41547 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336156) = some ⟨12, 1, 0, 1108174, 336156, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336156_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336156 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336156 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336156, 1, 65536⟩
    (by decide) selected_cut_41547

theorem selected_cut_41548 : selected 9 ⟨1135949, by decide⟩
    (prefixPartial 12 336157) = some ⟨12, 2, 0, 1135949, 336157, 1993, 65536⟩ := by
  decide +kernel

theorem context_12_336157_1135949 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336157 ⟨1135949, by decide⟩ :=
  accepted_of_selected 12 336157 ⟨1135949, by decide⟩ ⟨12, 2, 0, 1135949, 336157, 1993, 65536⟩
    (by decide) selected_cut_41548

theorem selected_cut_41549 : selected 9 ⟨1135980, by decide⟩
    (prefixPartial 12 336158) = some ⟨12, 2, 0, 1135980, 336158, 1829, 65536⟩ := by
  decide +kernel

theorem context_12_336158_1135980 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336158 ⟨1135980, by decide⟩ :=
  accepted_of_selected 12 336158 ⟨1135980, by decide⟩ ⟨12, 2, 0, 1135980, 336158, 1829, 65536⟩
    (by decide) selected_cut_41549

theorem selected_cut_41550 : selected 9 ⟨1136008, by decide⟩
    (prefixPartial 12 336159) = some ⟨12, 2, 0, 1136008, 336159, 1941, 65536⟩ := by
  decide +kernel

theorem context_12_336159_1136008 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336159 ⟨1136008, by decide⟩ :=
  accepted_of_selected 12 336159 ⟨1136008, by decide⟩ ⟨12, 2, 0, 1136008, 336159, 1941, 65536⟩
    (by decide) selected_cut_41550

theorem unmarked_context_11_84039_1136009 : frontier 10 ⟨1136009, by decide⟩
    (prefixCache 11 84039) (prefixPartial 11 84039) = false := by
  decide +kernel

theorem node_context_11_84039_1136009 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136009, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1135949, by decide⟩,⟨1135980, by decide⟩,⟨1136008, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84039_1136009 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84039 ⟨1136009, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84039
    ⟨1136009, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1135949, by decide⟩,⟨1135980, by decide⟩,⟨1136008, by decide⟩]) unmarked_context_11_84039_1136009 node_context_11_84039_1136009
  intro a
  fin_cases a
  · exact context_12_336156_1108174
  · exact context_12_336157_1135949
  · exact context_12_336158_1135980
  · exact context_12_336159_1136008

theorem unmarked_context_10_21009_1136010 : frontier 11 ⟨1136010, by decide⟩
    (prefixCache 10 21009) (prefixPartial 10 21009) = false := by
  decide +kernel

theorem node_context_10_21009_1136010 : EJMOriginalGlobalDAGData.nodes 11 ⟨1136010, by decide⟩ =
    .split (coordinate 10) (![⟨1135723, by decide⟩,⟨1135805, by decide⟩,⟨1135913, by decide⟩,⟨1136009, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21009_1136010 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21009 ⟨1136010, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21009
    ⟨1136010, by decide⟩ (by decide) (![⟨1135723, by decide⟩,⟨1135805, by decide⟩,⟨1135913, by decide⟩,⟨1136009, by decide⟩]) unmarked_context_10_21009_1136010 node_context_10_21009_1136010
  intro a
  fin_cases a
  · exact context_11_84036_1135723
  · exact context_11_84037_1135805
  · exact context_11_84038_1135913
  · exact context_11_84039_1136009

theorem selected_cut_41551 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336160) = some ⟨12, 1, 0, 1108174, 336160, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336160_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336160 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336160 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336160, 1, 65536⟩
    (by decide) selected_cut_41551

theorem selected_cut_41552 : selected 9 ⟨1136054, by decide⟩
    (prefixPartial 12 336161) = some ⟨12, 2, 0, 1136054, 336161, 2305, 65536⟩ := by
  decide +kernel

theorem context_12_336161_1136054 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336161 ⟨1136054, by decide⟩ :=
  accepted_of_selected 12 336161 ⟨1136054, by decide⟩ ⟨12, 2, 0, 1136054, 336161, 2305, 65536⟩
    (by decide) selected_cut_41552

theorem selected_cut_41553 : selected 9 ⟨1136084, by decide⟩
    (prefixPartial 12 336162) = some ⟨12, 2, 0, 1136084, 336162, 1797, 65536⟩ := by
  decide +kernel

theorem context_12_336162_1136084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336162 ⟨1136084, by decide⟩ :=
  accepted_of_selected 12 336162 ⟨1136084, by decide⟩ ⟨12, 2, 0, 1136084, 336162, 1797, 65536⟩
    (by decide) selected_cut_41553

theorem selected_cut_41554 : selected 9 ⟨1136110, by decide⟩
    (prefixPartial 12 336163) = some ⟨12, 2, 0, 1136110, 336163, 1997, 65536⟩ := by
  decide +kernel

theorem context_12_336163_1136110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336163 ⟨1136110, by decide⟩ :=
  accepted_of_selected 12 336163 ⟨1136110, by decide⟩ ⟨12, 2, 0, 1136110, 336163, 1997, 65536⟩
    (by decide) selected_cut_41554

theorem unmarked_context_11_84040_1136111 : frontier 10 ⟨1136111, by decide⟩
    (prefixCache 11 84040) (prefixPartial 11 84040) = false := by
  decide +kernel

theorem node_context_11_84040_1136111 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136111, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1136054, by decide⟩,⟨1136084, by decide⟩,⟨1136110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84040_1136111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84040 ⟨1136111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84040
    ⟨1136111, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1136054, by decide⟩,⟨1136084, by decide⟩,⟨1136110, by decide⟩]) unmarked_context_11_84040_1136111 node_context_11_84040_1136111
  intro a
  fin_cases a
  · exact context_12_336160_1108174
  · exact context_12_336161_1136054
  · exact context_12_336162_1136084
  · exact context_12_336163_1136110

theorem selected_cut_41555 : selected 10 ⟨1136178, by decide⟩
    (prefixPartial 11 84041) = some ⟨11, 2, 0, 1136178, 84041, 4041, 262144⟩ := by
  decide +kernel

theorem context_11_84041_1136178 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84041 ⟨1136178, by decide⟩ :=
  accepted_of_selected 11 84041 ⟨1136178, by decide⟩ ⟨11, 2, 0, 1136178, 84041, 4041, 262144⟩
    (by decide) selected_cut_41555

theorem selected_cut_41556 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336168) = some ⟨12, 1, 0, 1108174, 336168, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336168_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336168 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336168 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336168, 1, 65536⟩
    (by decide) selected_cut_41556

theorem selected_cut_41557 : selected 9 ⟨1136235, by decide⟩
    (prefixPartial 12 336169) = some ⟨12, 2, 0, 1136235, 336169, 2445, 65536⟩ := by
  decide +kernel

theorem context_12_336169_1136235 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336169 ⟨1136235, by decide⟩ :=
  accepted_of_selected 12 336169 ⟨1136235, by decide⟩ ⟨12, 2, 0, 1136235, 336169, 2445, 65536⟩
    (by decide) selected_cut_41557

theorem selected_cut_41558 : selected 9 ⟨474208, by decide⟩
    (prefixPartial 12 336170) = some ⟨12, 1, 0, 474208, 336170, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336170_474208 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336170 ⟨474208, by decide⟩ :=
  accepted_of_selected 12 336170 ⟨474208, by decide⟩ ⟨12, 1, 0, 474208, 336170, 1, 65536⟩
    (by decide) selected_cut_41558

theorem selected_cut_41559 : selected 9 ⟨1136264, by decide⟩
    (prefixPartial 12 336171) = some ⟨12, 2, 0, 1136264, 336171, 2025, 65536⟩ := by
  decide +kernel

theorem context_12_336171_1136264 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336171 ⟨1136264, by decide⟩ :=
  accepted_of_selected 12 336171 ⟨1136264, by decide⟩ ⟨12, 2, 0, 1136264, 336171, 2025, 65536⟩
    (by decide) selected_cut_41559

theorem unmarked_context_11_84042_1136265 : frontier 10 ⟨1136265, by decide⟩
    (prefixCache 11 84042) (prefixPartial 11 84042) = false := by
  decide +kernel

theorem node_context_11_84042_1136265 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136265, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1136235, by decide⟩,⟨474208, by decide⟩,⟨1136264, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84042_1136265 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84042 ⟨1136265, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84042
    ⟨1136265, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1136235, by decide⟩,⟨474208, by decide⟩,⟨1136264, by decide⟩]) unmarked_context_11_84042_1136265 node_context_11_84042_1136265
  intro a
  fin_cases a
  · exact context_12_336168_1108174
  · exact context_12_336169_1136235
  · exact context_12_336170_474208
  · exact context_12_336171_1136264

theorem selected_cut_41560 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336172) = some ⟨12, 1, 0, 1108174, 336172, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336172_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336172 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336172 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336172, 1, 65536⟩
    (by decide) selected_cut_41560

theorem selected_cut_41561 : selected 9 ⟨1136300, by decide⟩
    (prefixPartial 12 336173) = some ⟨12, 2, 0, 1136300, 336173, 2001, 65536⟩ := by
  decide +kernel

theorem context_12_336173_1136300 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336173 ⟨1136300, by decide⟩ :=
  accepted_of_selected 12 336173 ⟨1136300, by decide⟩ ⟨12, 2, 0, 1136300, 336173, 2001, 65536⟩
    (by decide) selected_cut_41561

theorem selected_cut_41562 : selected 9 ⟨1136331, by decide⟩
    (prefixPartial 12 336174) = some ⟨12, 2, 0, 1136331, 336174, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_336174_1136331 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336174 ⟨1136331, by decide⟩ :=
  accepted_of_selected 12 336174 ⟨1136331, by decide⟩ ⟨12, 2, 0, 1136331, 336174, 1669, 65536⟩
    (by decide) selected_cut_41562

theorem selected_cut_41563 : selected 9 ⟨1136359, by decide⟩
    (prefixPartial 12 336175) = some ⟨12, 2, 0, 1136359, 336175, 1857, 65536⟩ := by
  decide +kernel

theorem context_12_336175_1136359 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336175 ⟨1136359, by decide⟩ :=
  accepted_of_selected 12 336175 ⟨1136359, by decide⟩ ⟨12, 2, 0, 1136359, 336175, 1857, 65536⟩
    (by decide) selected_cut_41563

theorem unmarked_context_11_84043_1136360 : frontier 10 ⟨1136360, by decide⟩
    (prefixCache 11 84043) (prefixPartial 11 84043) = false := by
  decide +kernel

theorem node_context_11_84043_1136360 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136360, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1136300, by decide⟩,⟨1136331, by decide⟩,⟨1136359, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84043_1136360 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84043 ⟨1136360, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84043
    ⟨1136360, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1136300, by decide⟩,⟨1136331, by decide⟩,⟨1136359, by decide⟩]) unmarked_context_11_84043_1136360 node_context_11_84043_1136360
  intro a
  fin_cases a
  · exact context_12_336172_1108174
  · exact context_12_336173_1136300
  · exact context_12_336174_1136331
  · exact context_12_336175_1136359

theorem unmarked_context_10_21010_1136361 : frontier 11 ⟨1136361, by decide⟩
    (prefixCache 10 21010) (prefixPartial 10 21010) = false := by
  decide +kernel

theorem node_context_10_21010_1136361 : EJMOriginalGlobalDAGData.nodes 11 ⟨1136361, by decide⟩ =
    .split (coordinate 10) (![⟨1136111, by decide⟩,⟨1136178, by decide⟩,⟨1136265, by decide⟩,⟨1136360, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_21010_1136361 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 21010 ⟨1136361, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 21010
    ⟨1136361, by decide⟩ (by decide) (![⟨1136111, by decide⟩,⟨1136178, by decide⟩,⟨1136265, by decide⟩,⟨1136360, by decide⟩]) unmarked_context_10_21010_1136361 node_context_10_21010_1136361
  intro a
  fin_cases a
  · exact context_11_84040_1136111
  · exact context_11_84041_1136178
  · exact context_11_84042_1136265
  · exact context_11_84043_1136360

theorem selected_cut_41564 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336176) = some ⟨12, 1, 0, 1108174, 336176, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336176_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336176 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336176 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336176, 1, 65536⟩
    (by decide) selected_cut_41564

theorem selected_cut_41565 : selected 9 ⟨1136407, by decide⟩
    (prefixPartial 12 336177) = some ⟨12, 2, 0, 1136407, 336177, 2073, 65536⟩ := by
  decide +kernel

theorem context_12_336177_1136407 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336177 ⟨1136407, by decide⟩ :=
  accepted_of_selected 12 336177 ⟨1136407, by decide⟩ ⟨12, 2, 0, 1136407, 336177, 2073, 65536⟩
    (by decide) selected_cut_41565

theorem selected_cut_41566 : selected 9 ⟨1136429, by decide⟩
    (prefixPartial 12 336178) = some ⟨12, 2, 0, 1136429, 336178, 1765, 65536⟩ := by
  decide +kernel

theorem context_12_336178_1136429 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336178 ⟨1136429, by decide⟩ :=
  accepted_of_selected 12 336178 ⟨1136429, by decide⟩ ⟨12, 2, 0, 1136429, 336178, 1765, 65536⟩
    (by decide) selected_cut_41566

theorem selected_cut_41567 : selected 9 ⟨1136455, by decide⟩
    (prefixPartial 12 336179) = some ⟨12, 2, 0, 1136455, 336179, 1937, 65536⟩ := by
  decide +kernel

theorem context_12_336179_1136455 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336179 ⟨1136455, by decide⟩ :=
  accepted_of_selected 12 336179 ⟨1136455, by decide⟩ ⟨12, 2, 0, 1136455, 336179, 1937, 65536⟩
    (by decide) selected_cut_41567

theorem unmarked_context_11_84044_1136456 : frontier 10 ⟨1136456, by decide⟩
    (prefixCache 11 84044) (prefixPartial 11 84044) = false := by
  decide +kernel

theorem node_context_11_84044_1136456 : EJMOriginalGlobalDAGData.nodes 10 ⟨1136456, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1136407, by decide⟩,⟨1136429, by decide⟩,⟨1136455, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_84044_1136456 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84044 ⟨1136456, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 84044
    ⟨1136456, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1136407, by decide⟩,⟨1136429, by decide⟩,⟨1136455, by decide⟩]) unmarked_context_11_84044_1136456 node_context_11_84044_1136456
  intro a
  fin_cases a
  · exact context_12_336176_1108174
  · exact context_12_336177_1136407
  · exact context_12_336178_1136429
  · exact context_12_336179_1136455

theorem selected_cut_41568 : selected 10 ⟨1136508, by decide⟩
    (prefixPartial 11 84045) = some ⟨11, 2, 0, 1136508, 84045, 3737, 262144⟩ := by
  decide +kernel

theorem context_11_84045_1136508 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 84045 ⟨1136508, by decide⟩ :=
  accepted_of_selected 11 84045 ⟨1136508, by decide⟩ ⟨11, 2, 0, 1136508, 84045, 3737, 262144⟩
    (by decide) selected_cut_41568

theorem selected_cut_41569 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 336184) = some ⟨12, 1, 0, 1108174, 336184, 1, 65536⟩ := by
  decide +kernel

theorem context_12_336184_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336184 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 336184 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 336184, 1, 65536⟩
    (by decide) selected_cut_41569

theorem selected_cut_41570 : selected 9 ⟨1136561, by decide⟩
    (prefixPartial 12 336185) = some ⟨12, 2, 0, 1136561, 336185, 2221, 65536⟩ := by
  decide +kernel

theorem context_12_336185_1136561 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 336185 ⟨1136561, by decide⟩ :=
  accepted_of_selected 12 336185 ⟨1136561, by decide⟩ ⟨12, 2, 0, 1136561, 336185, 2221, 65536⟩
    (by decide) selected_cut_41570

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
