/- Generated prepared source. Not compiled or kernel accepted.
All original coordinates, four values, F1/F2, 32 blocks and scale are retained. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierSelector
import Mathlib.Tactic.FinCases
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierCover514
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 100000000
set_option maxRecDepth 65536
namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open EJMOriginalReplayAssembly (coordinate prefixCache prefixPartial)
theorem selected_cut_49443 : selected 9 ⟨1398773, by decide⟩
    (prefixPartial 12 407586) = some ⟨12, 2, 0, 1398773, 407586, 1669, 65536⟩ := by
  decide +kernel

theorem context_12_407586_1398773 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407586 ⟨1398773, by decide⟩ :=
  accepted_of_selected 12 407586 ⟨1398773, by decide⟩ ⟨12, 2, 0, 1398773, 407586, 1669, 65536⟩
    (by decide) selected_cut_49443

theorem selected_cut_49444 : selected 9 ⟨1398806, by decide⟩
    (prefixPartial 12 407587) = some ⟨12, 2, 0, 1398806, 407587, 1505, 65536⟩ := by
  decide +kernel

theorem context_12_407587_1398806 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407587 ⟨1398806, by decide⟩ :=
  accepted_of_selected 12 407587 ⟨1398806, by decide⟩ ⟨12, 2, 0, 1398806, 407587, 1505, 65536⟩
    (by decide) selected_cut_49444

theorem unmarked_context_11_101896_1398807 : frontier 10 ⟨1398807, by decide⟩
    (prefixCache 11 101896) (prefixPartial 11 101896) = false := by
  decide +kernel

theorem node_context_11_101896_1398807 : EJMOriginalGlobalDAGData.nodes 10 ⟨1398807, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1398733, by decide⟩,⟨1398773, by decide⟩,⟨1398806, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101896_1398807 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101896 ⟨1398807, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101896
    ⟨1398807, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1398733, by decide⟩,⟨1398773, by decide⟩,⟨1398806, by decide⟩]) unmarked_context_11_101896_1398807 node_context_11_101896_1398807
  intro a
  fin_cases a
  · exact context_12_407584_1108174
  · exact context_12_407585_1398733
  · exact context_12_407586_1398773
  · exact context_12_407587_1398806

theorem selected_cut_49445 : selected 10 ⟨1398913, by decide⟩
    (prefixPartial 11 101897) = some ⟨11, 2, 0, 1398913, 101897, 3589, 262144⟩ := by
  decide +kernel

theorem context_11_101897_1398913 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101897 ⟨1398913, by decide⟩ :=
  accepted_of_selected 11 101897 ⟨1398913, by decide⟩ ⟨11, 2, 0, 1398913, 101897, 3589, 262144⟩
    (by decide) selected_cut_49445

theorem selected_cut_49446 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 101898) = some ⟨11, 1, 0, 900587, 101898, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101898_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101898 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 101898 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 101898, 1, 262144⟩
    (by decide) selected_cut_49446

theorem selected_cut_49447 : selected 10 ⟨1398987, by decide⟩
    (prefixPartial 11 101899) = some ⟨11, 2, 0, 1398987, 101899, 3417, 262144⟩ := by
  decide +kernel

theorem context_11_101899_1398987 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101899 ⟨1398987, by decide⟩ :=
  accepted_of_selected 11 101899 ⟨1398987, by decide⟩ ⟨11, 2, 0, 1398987, 101899, 3417, 262144⟩
    (by decide) selected_cut_49447

theorem unmarked_context_10_25474_1398988 : frontier 11 ⟨1398988, by decide⟩
    (prefixCache 10 25474) (prefixPartial 10 25474) = false := by
  decide +kernel

theorem node_context_10_25474_1398988 : EJMOriginalGlobalDAGData.nodes 11 ⟨1398988, by decide⟩ =
    .split (coordinate 10) (![⟨1398807, by decide⟩,⟨1398913, by decide⟩,⟨900587, by decide⟩,⟨1398987, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25474_1398988 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25474 ⟨1398988, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25474
    ⟨1398988, by decide⟩ (by decide) (![⟨1398807, by decide⟩,⟨1398913, by decide⟩,⟨900587, by decide⟩,⟨1398987, by decide⟩]) unmarked_context_10_25474_1398988 node_context_10_25474_1398988
  intro a
  fin_cases a
  · exact context_11_101896_1398807
  · exact context_11_101897_1398913
  · exact context_11_101898_900587
  · exact context_11_101899_1398987

theorem selected_cut_49448 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407600) = some ⟨12, 1, 0, 1108174, 407600, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407600_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407600 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407600 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407600, 1, 65536⟩
    (by decide) selected_cut_49448

theorem selected_cut_49449 : selected 9 ⟨1399030, by decide⟩
    (prefixPartial 12 407601) = some ⟨12, 2, 0, 1399030, 407601, 1729, 65536⟩ := by
  decide +kernel

theorem context_12_407601_1399030 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407601 ⟨1399030, by decide⟩ :=
  accepted_of_selected 12 407601 ⟨1399030, by decide⟩ ⟨12, 2, 0, 1399030, 407601, 1729, 65536⟩
    (by decide) selected_cut_49449

theorem selected_cut_49450 : selected 9 ⟨1399077, by decide⟩
    (prefixPartial 12 407602) = some ⟨12, 2, 0, 1399077, 407602, 1637, 65536⟩ := by
  decide +kernel

theorem context_12_407602_1399077 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407602 ⟨1399077, by decide⟩ :=
  accepted_of_selected 12 407602 ⟨1399077, by decide⟩ ⟨12, 2, 0, 1399077, 407602, 1637, 65536⟩
    (by decide) selected_cut_49450

theorem selected_cut_49451 : selected 9 ⟨1399110, by decide⟩
    (prefixPartial 12 407603) = some ⟨12, 2, 0, 1399110, 407603, 1465, 65536⟩ := by
  decide +kernel

theorem context_12_407603_1399110 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407603 ⟨1399110, by decide⟩ :=
  accepted_of_selected 12 407603 ⟨1399110, by decide⟩ ⟨12, 2, 0, 1399110, 407603, 1465, 65536⟩
    (by decide) selected_cut_49451

theorem unmarked_context_11_101900_1399111 : frontier 10 ⟨1399111, by decide⟩
    (prefixCache 11 101900) (prefixPartial 11 101900) = false := by
  decide +kernel

theorem node_context_11_101900_1399111 : EJMOriginalGlobalDAGData.nodes 10 ⟨1399111, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1399030, by decide⟩,⟨1399077, by decide⟩,⟨1399110, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101900_1399111 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101900 ⟨1399111, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101900
    ⟨1399111, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1399030, by decide⟩,⟨1399077, by decide⟩,⟨1399110, by decide⟩]) unmarked_context_11_101900_1399111 node_context_11_101900_1399111
  intro a
  fin_cases a
  · exact context_12_407600_1108174
  · exact context_12_407601_1399030
  · exact context_12_407602_1399077
  · exact context_12_407603_1399110

theorem selected_cut_49452 : selected 10 ⟨1399210, by decide⟩
    (prefixPartial 11 101901) = some ⟨11, 2, 0, 1399210, 101901, 3521, 262144⟩ := by
  decide +kernel

theorem context_11_101901_1399210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101901 ⟨1399210, by decide⟩ :=
  accepted_of_selected 11 101901 ⟨1399210, by decide⟩ ⟨11, 2, 0, 1399210, 101901, 3521, 262144⟩
    (by decide) selected_cut_49452

theorem selected_cut_49453 : selected 10 ⟨1399277, by decide⟩
    (prefixPartial 11 101902) = some ⟨11, 2, 0, 1399277, 101902, 2969, 262144⟩ := by
  decide +kernel

theorem context_11_101902_1399277 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101902 ⟨1399277, by decide⟩ :=
  accepted_of_selected 11 101902 ⟨1399277, by decide⟩ ⟨11, 2, 0, 1399277, 101902, 2969, 262144⟩
    (by decide) selected_cut_49453

theorem selected_cut_49454 : selected 10 ⟨1399312, by decide⟩
    (prefixPartial 11 101903) = some ⟨11, 2, 0, 1399312, 101903, 1437, 262144⟩ := by
  decide +kernel

theorem context_11_101903_1399312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101903 ⟨1399312, by decide⟩ :=
  accepted_of_selected 11 101903 ⟨1399312, by decide⟩ ⟨11, 2, 0, 1399312, 101903, 1437, 262144⟩
    (by decide) selected_cut_49454

theorem unmarked_context_10_25475_1399313 : frontier 11 ⟨1399313, by decide⟩
    (prefixCache 10 25475) (prefixPartial 10 25475) = false := by
  decide +kernel

theorem node_context_10_25475_1399313 : EJMOriginalGlobalDAGData.nodes 11 ⟨1399313, by decide⟩ =
    .split (coordinate 10) (![⟨1399111, by decide⟩,⟨1399210, by decide⟩,⟨1399277, by decide⟩,⟨1399312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25475_1399313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25475 ⟨1399313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25475
    ⟨1399313, by decide⟩ (by decide) (![⟨1399111, by decide⟩,⟨1399210, by decide⟩,⟨1399277, by decide⟩,⟨1399312, by decide⟩]) unmarked_context_10_25475_1399313 node_context_10_25475_1399313
  intro a
  fin_cases a
  · exact context_11_101900_1399111
  · exact context_11_101901_1399210
  · exact context_11_101902_1399277
  · exact context_11_101903_1399312

theorem unmarked_context_9_6368_1399314 : frontier 12 ⟨1399314, by decide⟩
    (prefixCache 9 6368) (prefixPartial 9 6368) = false := by
  decide +kernel

theorem node_context_9_6368_1399314 : EJMOriginalGlobalDAGData.nodes 12 ⟨1399314, by decide⟩ =
    .split (coordinate 9) (![⟨1398293, by decide⟩,⟨1398694, by decide⟩,⟨1398988, by decide⟩,⟨1399313, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6368_1399314 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6368 ⟨1399314, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6368
    ⟨1399314, by decide⟩ (by decide) (![⟨1398293, by decide⟩,⟨1398694, by decide⟩,⟨1398988, by decide⟩,⟨1399313, by decide⟩]) unmarked_context_9_6368_1399314 node_context_9_6368_1399314
  intro a
  fin_cases a
  · exact context_10_25472_1398293
  · exact context_10_25473_1398694
  · exact context_10_25474_1398988
  · exact context_10_25475_1399313

theorem selected_cut_49455 : selected 10 ⟨1399349, by decide⟩
    (prefixPartial 11 101904) = some ⟨11, 2, 0, 1399349, 101904, 1377, 262144⟩ := by
  decide +kernel

theorem context_11_101904_1399349 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101904 ⟨1399349, by decide⟩ :=
  accepted_of_selected 11 101904 ⟨1399349, by decide⟩ ⟨11, 2, 0, 1399349, 101904, 1377, 262144⟩
    (by decide) selected_cut_49455

theorem selected_cut_49456 : selected 9 ⟨1399378, by decide⟩
    (prefixPartial 12 407620) = some ⟨12, 2, 0, 1399378, 407620, 1265, 65536⟩ := by
  decide +kernel

theorem context_12_407620_1399378 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407620 ⟨1399378, by decide⟩ :=
  accepted_of_selected 12 407620 ⟨1399378, by decide⟩ ⟨12, 2, 0, 1399378, 407620, 1265, 65536⟩
    (by decide) selected_cut_49456

theorem selected_cut_49457 : selected 9 ⟨642341, by decide⟩
    (prefixPartial 12 407621) = some ⟨12, 1, 0, 642341, 407621, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407621_642341 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407621 ⟨642341, by decide⟩ :=
  accepted_of_selected 12 407621 ⟨642341, by decide⟩ ⟨12, 1, 0, 642341, 407621, 1, 65536⟩
    (by decide) selected_cut_49457

theorem selected_cut_49458 : selected 9 ⟨1399420, by decide⟩
    (prefixPartial 12 407622) = some ⟨12, 2, 0, 1399420, 407622, 1545, 65536⟩ := by
  decide +kernel

theorem context_12_407622_1399420 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407622 ⟨1399420, by decide⟩ :=
  accepted_of_selected 12 407622 ⟨1399420, by decide⟩ ⟨12, 2, 0, 1399420, 407622, 1545, 65536⟩
    (by decide) selected_cut_49458

theorem selected_cut_49459 : selected 9 ⟨1399450, by decide⟩
    (prefixPartial 12 407623) = some ⟨12, 2, 0, 1399450, 407623, 1333, 65536⟩ := by
  decide +kernel

theorem context_12_407623_1399450 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407623 ⟨1399450, by decide⟩ :=
  accepted_of_selected 12 407623 ⟨1399450, by decide⟩ ⟨12, 2, 0, 1399450, 407623, 1333, 65536⟩
    (by decide) selected_cut_49459

theorem unmarked_context_11_101905_1399451 : frontier 10 ⟨1399451, by decide⟩
    (prefixCache 11 101905) (prefixPartial 11 101905) = false := by
  decide +kernel

theorem node_context_11_101905_1399451 : EJMOriginalGlobalDAGData.nodes 10 ⟨1399451, by decide⟩ =
    .split (coordinate 11) (![⟨1399378, by decide⟩,⟨642341, by decide⟩,⟨1399420, by decide⟩,⟨1399450, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101905_1399451 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101905 ⟨1399451, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101905
    ⟨1399451, by decide⟩ (by decide) (![⟨1399378, by decide⟩,⟨642341, by decide⟩,⟨1399420, by decide⟩,⟨1399450, by decide⟩]) unmarked_context_11_101905_1399451 node_context_11_101905_1399451
  intro a
  fin_cases a
  · exact context_12_407620_1399378
  · exact context_12_407621_642341
  · exact context_12_407622_1399420
  · exact context_12_407623_1399450

theorem selected_cut_49460 : selected 10 ⟨1399491, by decide⟩
    (prefixPartial 11 101906) = some ⟨11, 2, 0, 1399491, 101906, 2277, 262144⟩ := by
  decide +kernel

theorem context_11_101906_1399491 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101906 ⟨1399491, by decide⟩ :=
  accepted_of_selected 11 101906 ⟨1399491, by decide⟩ ⟨11, 2, 0, 1399491, 101906, 2277, 262144⟩
    (by decide) selected_cut_49460

theorem selected_cut_49461 : selected 10 ⟨1399547, by decide⟩
    (prefixPartial 11 101907) = some ⟨11, 2, 0, 1399547, 101907, 2565, 262144⟩ := by
  decide +kernel

theorem context_11_101907_1399547 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101907 ⟨1399547, by decide⟩ :=
  accepted_of_selected 11 101907 ⟨1399547, by decide⟩ ⟨11, 2, 0, 1399547, 101907, 2565, 262144⟩
    (by decide) selected_cut_49461

theorem unmarked_context_10_25476_1399548 : frontier 11 ⟨1399548, by decide⟩
    (prefixCache 10 25476) (prefixPartial 10 25476) = false := by
  decide +kernel

theorem node_context_10_25476_1399548 : EJMOriginalGlobalDAGData.nodes 11 ⟨1399548, by decide⟩ =
    .split (coordinate 10) (![⟨1399349, by decide⟩,⟨1399451, by decide⟩,⟨1399491, by decide⟩,⟨1399547, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25476_1399548 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25476 ⟨1399548, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25476
    ⟨1399548, by decide⟩ (by decide) (![⟨1399349, by decide⟩,⟨1399451, by decide⟩,⟨1399491, by decide⟩,⟨1399547, by decide⟩]) unmarked_context_10_25476_1399548 node_context_10_25476_1399548
  intro a
  fin_cases a
  · exact context_11_101904_1399349
  · exact context_11_101905_1399451
  · exact context_11_101906_1399491
  · exact context_11_101907_1399547

theorem selected_cut_49462 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25477) = some ⟨10, 1, 0, 893098, 25477, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25477_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25477 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25477 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25477, 1, 1048576⟩
    (by decide) selected_cut_49462

theorem selected_cut_49463 : selected 10 ⟨1399615, by decide⟩
    (prefixPartial 11 101912) = some ⟨11, 2, 0, 1399615, 101912, 2613, 262144⟩ := by
  decide +kernel

theorem context_11_101912_1399615 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101912 ⟨1399615, by decide⟩ :=
  accepted_of_selected 11 101912 ⟨1399615, by decide⟩ ⟨11, 2, 0, 1399615, 101912, 2613, 262144⟩
    (by decide) selected_cut_49463

theorem selected_cut_49464 : selected 10 ⟨1399714, by decide⟩
    (prefixPartial 11 101913) = some ⟨11, 2, 0, 1399714, 101913, 3577, 262144⟩ := by
  decide +kernel

theorem context_11_101913_1399714 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101913 ⟨1399714, by decide⟩ :=
  accepted_of_selected 11 101913 ⟨1399714, by decide⟩ ⟨11, 2, 0, 1399714, 101913, 3577, 262144⟩
    (by decide) selected_cut_49464

theorem selected_cut_49465 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 101914) = some ⟨11, 1, 0, 900587, 101914, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101914_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101914 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 101914 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 101914, 1, 262144⟩
    (by decide) selected_cut_49465

theorem selected_cut_49466 : selected 10 ⟨1399765, by decide⟩
    (prefixPartial 11 101915) = some ⟨11, 2, 0, 1399765, 101915, 3065, 262144⟩ := by
  decide +kernel

theorem context_11_101915_1399765 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101915 ⟨1399765, by decide⟩ :=
  accepted_of_selected 11 101915 ⟨1399765, by decide⟩ ⟨11, 2, 0, 1399765, 101915, 3065, 262144⟩
    (by decide) selected_cut_49466

theorem unmarked_context_10_25478_1399766 : frontier 11 ⟨1399766, by decide⟩
    (prefixCache 10 25478) (prefixPartial 10 25478) = false := by
  decide +kernel

theorem node_context_10_25478_1399766 : EJMOriginalGlobalDAGData.nodes 11 ⟨1399766, by decide⟩ =
    .split (coordinate 10) (![⟨1399615, by decide⟩,⟨1399714, by decide⟩,⟨900587, by decide⟩,⟨1399765, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25478_1399766 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25478 ⟨1399766, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25478
    ⟨1399766, by decide⟩ (by decide) (![⟨1399615, by decide⟩,⟨1399714, by decide⟩,⟨900587, by decide⟩,⟨1399765, by decide⟩]) unmarked_context_10_25478_1399766 node_context_10_25478_1399766
  intro a
  fin_cases a
  · exact context_11_101912_1399615
  · exact context_11_101913_1399714
  · exact context_11_101914_900587
  · exact context_11_101915_1399765

theorem selected_cut_49467 : selected 10 ⟨1399810, by decide⟩
    (prefixPartial 11 101916) = some ⟨11, 2, 0, 1399810, 101916, 2141, 262144⟩ := by
  decide +kernel

theorem context_11_101916_1399810 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101916 ⟨1399810, by decide⟩ :=
  accepted_of_selected 11 101916 ⟨1399810, by decide⟩ ⟨11, 2, 0, 1399810, 101916, 2141, 262144⟩
    (by decide) selected_cut_49467

theorem selected_cut_49468 : selected 10 ⟨1399876, by decide⟩
    (prefixPartial 11 101917) = some ⟨11, 2, 0, 1399876, 101917, 2937, 262144⟩ := by
  decide +kernel

theorem context_11_101917_1399876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101917 ⟨1399876, by decide⟩ :=
  accepted_of_selected 11 101917 ⟨1399876, by decide⟩ ⟨11, 2, 0, 1399876, 101917, 2937, 262144⟩
    (by decide) selected_cut_49468

theorem selected_cut_49469 : selected 10 ⟨1399903, by decide⟩
    (prefixPartial 11 101918) = some ⟨11, 2, 0, 1399903, 101918, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_101918_1399903 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101918 ⟨1399903, by decide⟩ :=
  accepted_of_selected 11 101918 ⟨1399903, by decide⟩ ⟨11, 2, 0, 1399903, 101918, 1589, 262144⟩
    (by decide) selected_cut_49469

theorem selected_cut_49470 : selected 10 ⟨1399917, by decide⟩
    (prefixPartial 11 101919) = some ⟨11, 2, 0, 1399917, 101919, 757, 262144⟩ := by
  decide +kernel

theorem context_11_101919_1399917 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101919 ⟨1399917, by decide⟩ :=
  accepted_of_selected 11 101919 ⟨1399917, by decide⟩ ⟨11, 2, 0, 1399917, 101919, 757, 262144⟩
    (by decide) selected_cut_49470

theorem unmarked_context_10_25479_1399918 : frontier 11 ⟨1399918, by decide⟩
    (prefixCache 10 25479) (prefixPartial 10 25479) = false := by
  decide +kernel

theorem node_context_10_25479_1399918 : EJMOriginalGlobalDAGData.nodes 11 ⟨1399918, by decide⟩ =
    .split (coordinate 10) (![⟨1399810, by decide⟩,⟨1399876, by decide⟩,⟨1399903, by decide⟩,⟨1399917, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25479_1399918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25479 ⟨1399918, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25479
    ⟨1399918, by decide⟩ (by decide) (![⟨1399810, by decide⟩,⟨1399876, by decide⟩,⟨1399903, by decide⟩,⟨1399917, by decide⟩]) unmarked_context_10_25479_1399918 node_context_10_25479_1399918
  intro a
  fin_cases a
  · exact context_11_101916_1399810
  · exact context_11_101917_1399876
  · exact context_11_101918_1399903
  · exact context_11_101919_1399917

theorem unmarked_context_9_6369_1399919 : frontier 12 ⟨1399919, by decide⟩
    (prefixCache 9 6369) (prefixPartial 9 6369) = false := by
  decide +kernel

theorem node_context_9_6369_1399919 : EJMOriginalGlobalDAGData.nodes 12 ⟨1399919, by decide⟩ =
    .split (coordinate 9) (![⟨1399548, by decide⟩,⟨893098, by decide⟩,⟨1399766, by decide⟩,⟨1399918, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6369_1399919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6369 ⟨1399919, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6369
    ⟨1399919, by decide⟩ (by decide) (![⟨1399548, by decide⟩,⟨893098, by decide⟩,⟨1399766, by decide⟩,⟨1399918, by decide⟩]) unmarked_context_9_6369_1399919 node_context_9_6369_1399919
  intro a
  fin_cases a
  · exact context_10_25476_1399548
  · exact context_10_25477_893098
  · exact context_10_25478_1399766
  · exact context_10_25479_1399918

theorem selected_cut_49471 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 101920) = some ⟨11, 1, 0, 1375697, 101920, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101920_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101920 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 101920 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 101920, 1, 262144⟩
    (by decide) selected_cut_49471

theorem selected_cut_49472 : selected 10 ⟨1399958, by decide⟩
    (prefixPartial 11 101921) = some ⟨11, 2, 0, 1399958, 101921, 1709, 262144⟩ := by
  decide +kernel

theorem context_11_101921_1399958 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101921 ⟨1399958, by decide⟩ :=
  accepted_of_selected 11 101921 ⟨1399958, by decide⟩ ⟨11, 2, 0, 1399958, 101921, 1709, 262144⟩
    (by decide) selected_cut_49472

theorem selected_cut_49473 : selected 10 ⟨1400006, by decide⟩
    (prefixPartial 11 101922) = some ⟨11, 2, 0, 1400006, 101922, 2309, 262144⟩ := by
  decide +kernel

theorem context_11_101922_1400006 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101922 ⟨1400006, by decide⟩ :=
  accepted_of_selected 11 101922 ⟨1400006, by decide⟩ ⟨11, 2, 0, 1400006, 101922, 2309, 262144⟩
    (by decide) selected_cut_49473

theorem selected_cut_49474 : selected 10 ⟨1400036, by decide⟩
    (prefixPartial 11 101923) = some ⟨11, 2, 0, 1400036, 101923, 1585, 262144⟩ := by
  decide +kernel

theorem context_11_101923_1400036 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101923 ⟨1400036, by decide⟩ :=
  accepted_of_selected 11 101923 ⟨1400036, by decide⟩ ⟨11, 2, 0, 1400036, 101923, 1585, 262144⟩
    (by decide) selected_cut_49474

theorem unmarked_context_10_25480_1400037 : frontier 11 ⟨1400037, by decide⟩
    (prefixCache 10 25480) (prefixPartial 10 25480) = false := by
  decide +kernel

theorem node_context_10_25480_1400037 : EJMOriginalGlobalDAGData.nodes 11 ⟨1400037, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1399958, by decide⟩,⟨1400006, by decide⟩,⟨1400036, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25480_1400037 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25480 ⟨1400037, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25480
    ⟨1400037, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1399958, by decide⟩,⟨1400006, by decide⟩,⟨1400036, by decide⟩]) unmarked_context_10_25480_1400037 node_context_10_25480_1400037
  intro a
  fin_cases a
  · exact context_11_101920_1375697
  · exact context_11_101921_1399958
  · exact context_11_101922_1400006
  · exact context_11_101923_1400036

theorem selected_cut_49475 : selected 10 ⟨1400084, by decide⟩
    (prefixPartial 11 101924) = some ⟨11, 2, 0, 1400084, 101924, 1741, 262144⟩ := by
  decide +kernel

theorem context_11_101924_1400084 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101924 ⟨1400084, by decide⟩ :=
  accepted_of_selected 11 101924 ⟨1400084, by decide⟩ ⟨11, 2, 0, 1400084, 101924, 1741, 262144⟩
    (by decide) selected_cut_49475

theorem selected_cut_49476 : selected 10 ⟨1378525, by decide⟩
    (prefixPartial 11 101925) = some ⟨11, 1, 0, 1378525, 101925, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101925_1378525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101925 ⟨1378525, by decide⟩ :=
  accepted_of_selected 11 101925 ⟨1378525, by decide⟩ ⟨11, 1, 0, 1378525, 101925, 1, 262144⟩
    (by decide) selected_cut_49476

theorem selected_cut_49477 : selected 10 ⟨1400134, by decide⟩
    (prefixPartial 11 101926) = some ⟨11, 2, 0, 1400134, 101926, 2121, 262144⟩ := by
  decide +kernel

theorem context_11_101926_1400134 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101926 ⟨1400134, by decide⟩ :=
  accepted_of_selected 11 101926 ⟨1400134, by decide⟩ ⟨11, 2, 0, 1400134, 101926, 2121, 262144⟩
    (by decide) selected_cut_49477

theorem selected_cut_49478 : selected 10 ⟨1400180, by decide⟩
    (prefixPartial 11 101927) = some ⟨11, 2, 0, 1400180, 101927, 2573, 262144⟩ := by
  decide +kernel

theorem context_11_101927_1400180 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101927 ⟨1400180, by decide⟩ :=
  accepted_of_selected 11 101927 ⟨1400180, by decide⟩ ⟨11, 2, 0, 1400180, 101927, 2573, 262144⟩
    (by decide) selected_cut_49478

theorem unmarked_context_10_25481_1400181 : frontier 11 ⟨1400181, by decide⟩
    (prefixCache 10 25481) (prefixPartial 10 25481) = false := by
  decide +kernel

theorem node_context_10_25481_1400181 : EJMOriginalGlobalDAGData.nodes 11 ⟨1400181, by decide⟩ =
    .split (coordinate 10) (![⟨1400084, by decide⟩,⟨1378525, by decide⟩,⟨1400134, by decide⟩,⟨1400180, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25481_1400181 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25481 ⟨1400181, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25481
    ⟨1400181, by decide⟩ (by decide) (![⟨1400084, by decide⟩,⟨1378525, by decide⟩,⟨1400134, by decide⟩,⟨1400180, by decide⟩]) unmarked_context_10_25481_1400181 node_context_10_25481_1400181
  intro a
  fin_cases a
  · exact context_11_101924_1400084
  · exact context_11_101925_1378525
  · exact context_11_101926_1400134
  · exact context_11_101927_1400180

theorem selected_cut_49479 : selected 11 ⟨1400210, by decide⟩
    (prefixPartial 10 25482) = some ⟨10, 2, 0, 1400210, 25482, 1133, 1048576⟩ := by
  decide +kernel

theorem context_10_25482_1400210 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25482 ⟨1400210, by decide⟩ :=
  accepted_of_selected 10 25482 ⟨1400210, by decide⟩ ⟨10, 2, 0, 1400210, 25482, 1133, 1048576⟩
    (by decide) selected_cut_49479

theorem selected_cut_49480 : selected 10 ⟨1400238, by decide⟩
    (prefixPartial 11 101932) = some ⟨11, 2, 0, 1400238, 101932, 1077, 262144⟩ := by
  decide +kernel

theorem context_11_101932_1400238 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101932 ⟨1400238, by decide⟩ :=
  accepted_of_selected 11 101932 ⟨1400238, by decide⟩ ⟨11, 2, 0, 1400238, 101932, 1077, 262144⟩
    (by decide) selected_cut_49480

theorem selected_cut_49481 : selected 10 ⟨1400279, by decide⟩
    (prefixPartial 11 101933) = some ⟨11, 2, 0, 1400279, 101933, 1869, 262144⟩ := by
  decide +kernel

theorem context_11_101933_1400279 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101933 ⟨1400279, by decide⟩ :=
  accepted_of_selected 11 101933 ⟨1400279, by decide⟩ ⟨11, 2, 0, 1400279, 101933, 1869, 262144⟩
    (by decide) selected_cut_49481

theorem selected_cut_49482 : selected 10 ⟨1400311, by decide⟩
    (prefixPartial 11 101934) = some ⟨11, 2, 0, 1400311, 101934, 1169, 262144⟩ := by
  decide +kernel

theorem context_11_101934_1400311 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101934 ⟨1400311, by decide⟩ :=
  accepted_of_selected 11 101934 ⟨1400311, by decide⟩ ⟨11, 2, 0, 1400311, 101934, 1169, 262144⟩
    (by decide) selected_cut_49482

theorem selected_cut_49483 : selected 10 ⟨1376021, by decide⟩
    (prefixPartial 11 101935) = some ⟨11, 1, 0, 1376021, 101935, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101935_1376021 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101935 ⟨1376021, by decide⟩ :=
  accepted_of_selected 11 101935 ⟨1376021, by decide⟩ ⟨11, 1, 0, 1376021, 101935, 1, 262144⟩
    (by decide) selected_cut_49483

theorem unmarked_context_10_25483_1400312 : frontier 11 ⟨1400312, by decide⟩
    (prefixCache 10 25483) (prefixPartial 10 25483) = false := by
  decide +kernel

theorem node_context_10_25483_1400312 : EJMOriginalGlobalDAGData.nodes 11 ⟨1400312, by decide⟩ =
    .split (coordinate 10) (![⟨1400238, by decide⟩,⟨1400279, by decide⟩,⟨1400311, by decide⟩,⟨1376021, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25483_1400312 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25483 ⟨1400312, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25483
    ⟨1400312, by decide⟩ (by decide) (![⟨1400238, by decide⟩,⟨1400279, by decide⟩,⟨1400311, by decide⟩,⟨1376021, by decide⟩]) unmarked_context_10_25483_1400312 node_context_10_25483_1400312
  intro a
  fin_cases a
  · exact context_11_101932_1400238
  · exact context_11_101933_1400279
  · exact context_11_101934_1400311
  · exact context_11_101935_1376021

theorem unmarked_context_9_6370_1400313 : frontier 12 ⟨1400313, by decide⟩
    (prefixCache 9 6370) (prefixPartial 9 6370) = false := by
  decide +kernel

theorem node_context_9_6370_1400313 : EJMOriginalGlobalDAGData.nodes 12 ⟨1400313, by decide⟩ =
    .split (coordinate 9) (![⟨1400037, by decide⟩,⟨1400181, by decide⟩,⟨1400210, by decide⟩,⟨1400312, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6370_1400313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6370 ⟨1400313, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6370
    ⟨1400313, by decide⟩ (by decide) (![⟨1400037, by decide⟩,⟨1400181, by decide⟩,⟨1400210, by decide⟩,⟨1400312, by decide⟩]) unmarked_context_9_6370_1400313 node_context_9_6370_1400313
  intro a
  fin_cases a
  · exact context_10_25480_1400037
  · exact context_10_25481_1400181
  · exact context_10_25482_1400210
  · exact context_10_25483_1400312

theorem selected_cut_49484 : selected 11 ⟨1400362, by decide⟩
    (prefixPartial 10 25484) = some ⟨10, 2, 0, 1400362, 25484, 2361, 1048576⟩ := by
  decide +kernel

theorem context_10_25484_1400362 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25484 ⟨1400362, by decide⟩ :=
  accepted_of_selected 10 25484 ⟨1400362, by decide⟩ ⟨10, 2, 0, 1400362, 25484, 2361, 1048576⟩
    (by decide) selected_cut_49484

theorem selected_cut_49485 : selected 11 ⟨1400404, by decide⟩
    (prefixPartial 10 25485) = some ⟨10, 2, 0, 1400404, 25485, 2021, 1048576⟩ := by
  decide +kernel

theorem context_10_25485_1400404 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25485 ⟨1400404, by decide⟩ :=
  accepted_of_selected 10 25485 ⟨1400404, by decide⟩ ⟨10, 2, 0, 1400404, 25485, 2021, 1048576⟩
    (by decide) selected_cut_49485

theorem selected_cut_49486 : selected 11 ⟨1400432, by decide⟩
    (prefixPartial 10 25486) = some ⟨10, 2, 0, 1400432, 25486, 869, 1048576⟩ := by
  decide +kernel

theorem context_10_25486_1400432 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25486 ⟨1400432, by decide⟩ :=
  accepted_of_selected 10 25486 ⟨1400432, by decide⟩ ⟨10, 2, 0, 1400432, 25486, 869, 1048576⟩
    (by decide) selected_cut_49486

theorem selected_cut_49487 : selected 11 ⟨1400441, by decide⟩
    (prefixPartial 10 25487) = some ⟨10, 2, 0, 1400441, 25487, 73, 1048576⟩ := by
  decide +kernel

theorem context_10_25487_1400441 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25487 ⟨1400441, by decide⟩ :=
  accepted_of_selected 10 25487 ⟨1400441, by decide⟩ ⟨10, 2, 0, 1400441, 25487, 73, 1048576⟩
    (by decide) selected_cut_49487

theorem unmarked_context_9_6371_1400442 : frontier 12 ⟨1400442, by decide⟩
    (prefixCache 9 6371) (prefixPartial 9 6371) = false := by
  decide +kernel

theorem node_context_9_6371_1400442 : EJMOriginalGlobalDAGData.nodes 12 ⟨1400442, by decide⟩ =
    .split (coordinate 9) (![⟨1400362, by decide⟩,⟨1400404, by decide⟩,⟨1400432, by decide⟩,⟨1400441, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6371_1400442 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6371 ⟨1400442, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6371
    ⟨1400442, by decide⟩ (by decide) (![⟨1400362, by decide⟩,⟨1400404, by decide⟩,⟨1400432, by decide⟩,⟨1400441, by decide⟩]) unmarked_context_9_6371_1400442 node_context_9_6371_1400442
  intro a
  fin_cases a
  · exact context_10_25484_1400362
  · exact context_10_25485_1400404
  · exact context_10_25486_1400432
  · exact context_10_25487_1400441

theorem unmarked_context_8_1592_1400443 : frontier 13 ⟨1400443, by decide⟩
    (prefixCache 8 1592) (prefixPartial 8 1592) = false := by
  decide +kernel

theorem node_context_8_1592_1400443 : EJMOriginalGlobalDAGData.nodes 13 ⟨1400443, by decide⟩ =
    .split (coordinate 8) (![⟨1399314, by decide⟩,⟨1399919, by decide⟩,⟨1400313, by decide⟩,⟨1400442, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_8_1592_1400443 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 8 1592 ⟨1400443, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 8 1592
    ⟨1400443, by decide⟩ (by decide) (![⟨1399314, by decide⟩,⟨1399919, by decide⟩,⟨1400313, by decide⟩,⟨1400442, by decide⟩]) unmarked_context_8_1592_1400443 node_context_8_1592_1400443
  intro a
  fin_cases a
  · exact context_9_6368_1399314
  · exact context_9_6369_1399919
  · exact context_9_6370_1400313
  · exact context_9_6371_1400442

theorem selected_cut_49488 : selected 11 ⟨1400531, by decide⟩
    (prefixPartial 10 25488) = some ⟨10, 2, 0, 1400531, 25488, 3993, 1048576⟩ := by
  decide +kernel

theorem context_10_25488_1400531 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25488 ⟨1400531, by decide⟩ :=
  accepted_of_selected 10 25488 ⟨1400531, by decide⟩ ⟨10, 2, 0, 1400531, 25488, 3993, 1048576⟩
    (by decide) selected_cut_49488

theorem selected_cut_49489 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407824) = some ⟨12, 1, 0, 1108174, 407824, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407824_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407824 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407824 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407824, 1, 65536⟩
    (by decide) selected_cut_49489

theorem selected_cut_49490 : selected 9 ⟨1400578, by decide⟩
    (prefixPartial 12 407825) = some ⟨12, 2, 0, 1400578, 407825, 2113, 65536⟩ := by
  decide +kernel

theorem context_12_407825_1400578 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407825 ⟨1400578, by decide⟩ :=
  accepted_of_selected 12 407825 ⟨1400578, by decide⟩ ⟨12, 2, 0, 1400578, 407825, 2113, 65536⟩
    (by decide) selected_cut_49490

theorem selected_cut_49491 : selected 9 ⟨1400621, by decide⟩
    (prefixPartial 12 407826) = some ⟨12, 2, 0, 1400621, 407826, 2065, 65536⟩ := by
  decide +kernel

theorem context_12_407826_1400621 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407826 ⟨1400621, by decide⟩ :=
  accepted_of_selected 12 407826 ⟨1400621, by decide⟩ ⟨12, 2, 0, 1400621, 407826, 2065, 65536⟩
    (by decide) selected_cut_49491

theorem selected_cut_49492 : selected 9 ⟨1400668, by decide⟩
    (prefixPartial 12 407827) = some ⟨12, 2, 0, 1400668, 407827, 2049, 65536⟩ := by
  decide +kernel

theorem context_12_407827_1400668 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407827 ⟨1400668, by decide⟩ :=
  accepted_of_selected 12 407827 ⟨1400668, by decide⟩ ⟨12, 2, 0, 1400668, 407827, 2049, 65536⟩
    (by decide) selected_cut_49492

theorem unmarked_context_11_101956_1400669 : frontier 10 ⟨1400669, by decide⟩
    (prefixCache 11 101956) (prefixPartial 11 101956) = false := by
  decide +kernel

theorem node_context_11_101956_1400669 : EJMOriginalGlobalDAGData.nodes 10 ⟨1400669, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1400578, by decide⟩,⟨1400621, by decide⟩,⟨1400668, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101956_1400669 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101956 ⟨1400669, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101956
    ⟨1400669, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1400578, by decide⟩,⟨1400621, by decide⟩,⟨1400668, by decide⟩]) unmarked_context_11_101956_1400669 node_context_11_101956_1400669
  intro a
  fin_cases a
  · exact context_12_407824_1108174
  · exact context_12_407825_1400578
  · exact context_12_407826_1400621
  · exact context_12_407827_1400668

theorem selected_cut_49493 : selected 10 ⟨1400670, by decide⟩
    (prefixPartial 11 101957) = some ⟨11, 2, 0, 1400670, 101957, 5, 262144⟩ := by
  decide +kernel

theorem context_11_101957_1400670 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101957 ⟨1400670, by decide⟩ :=
  accepted_of_selected 11 101957 ⟨1400670, by decide⟩ ⟨11, 2, 0, 1400670, 101957, 5, 262144⟩
    (by decide) selected_cut_49493

theorem selected_cut_49494 : selected 10 ⟨1400755, by decide⟩
    (prefixPartial 11 101958) = some ⟨11, 2, 0, 1400755, 101958, 3445, 262144⟩ := by
  decide +kernel

theorem context_11_101958_1400755 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101958 ⟨1400755, by decide⟩ :=
  accepted_of_selected 11 101958 ⟨1400755, by decide⟩ ⟨11, 2, 0, 1400755, 101958, 3445, 262144⟩
    (by decide) selected_cut_49494

theorem selected_cut_49495 : selected 10 ⟨1400826, by decide⟩
    (prefixPartial 11 101959) = some ⟨11, 2, 0, 1400826, 101959, 3745, 262144⟩ := by
  decide +kernel

theorem context_11_101959_1400826 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101959 ⟨1400826, by decide⟩ :=
  accepted_of_selected 11 101959 ⟨1400826, by decide⟩ ⟨11, 2, 0, 1400826, 101959, 3745, 262144⟩
    (by decide) selected_cut_49495

theorem unmarked_context_10_25489_1400827 : frontier 11 ⟨1400827, by decide⟩
    (prefixCache 10 25489) (prefixPartial 10 25489) = false := by
  decide +kernel

theorem node_context_10_25489_1400827 : EJMOriginalGlobalDAGData.nodes 11 ⟨1400827, by decide⟩ =
    .split (coordinate 10) (![⟨1400669, by decide⟩,⟨1400670, by decide⟩,⟨1400755, by decide⟩,⟨1400826, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25489_1400827 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25489 ⟨1400827, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25489
    ⟨1400827, by decide⟩ (by decide) (![⟨1400669, by decide⟩,⟨1400670, by decide⟩,⟨1400755, by decide⟩,⟨1400826, by decide⟩]) unmarked_context_10_25489_1400827 node_context_10_25489_1400827
  intro a
  fin_cases a
  · exact context_11_101956_1400669
  · exact context_11_101957_1400670
  · exact context_11_101958_1400755
  · exact context_11_101959_1400826

theorem selected_cut_49496 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407840) = some ⟨12, 1, 0, 1108174, 407840, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407840_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407840 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407840 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407840, 1, 65536⟩
    (by decide) selected_cut_49496

theorem selected_cut_49497 : selected 9 ⟨1400863, by decide⟩
    (prefixPartial 12 407841) = some ⟨12, 2, 0, 1400863, 407841, 1841, 65536⟩ := by
  decide +kernel

theorem context_12_407841_1400863 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407841 ⟨1400863, by decide⟩ :=
  accepted_of_selected 12 407841 ⟨1400863, by decide⟩ ⟨12, 2, 0, 1400863, 407841, 1841, 65536⟩
    (by decide) selected_cut_49497

theorem selected_cut_49498 : selected 9 ⟨1400896, by decide⟩
    (prefixPartial 12 407842) = some ⟨12, 2, 0, 1400896, 407842, 1793, 65536⟩ := by
  decide +kernel

theorem context_12_407842_1400896 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407842 ⟨1400896, by decide⟩ :=
  accepted_of_selected 12 407842 ⟨1400896, by decide⟩ ⟨12, 2, 0, 1400896, 407842, 1793, 65536⟩
    (by decide) selected_cut_49498

theorem selected_cut_49499 : selected 9 ⟨1400919, by decide⟩
    (prefixPartial 12 407843) = some ⟨12, 2, 0, 1400919, 407843, 1625, 65536⟩ := by
  decide +kernel

theorem context_12_407843_1400919 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407843 ⟨1400919, by decide⟩ :=
  accepted_of_selected 12 407843 ⟨1400919, by decide⟩ ⟨12, 2, 0, 1400919, 407843, 1625, 65536⟩
    (by decide) selected_cut_49499

theorem unmarked_context_11_101960_1400920 : frontier 10 ⟨1400920, by decide⟩
    (prefixCache 11 101960) (prefixPartial 11 101960) = false := by
  decide +kernel

theorem node_context_11_101960_1400920 : EJMOriginalGlobalDAGData.nodes 10 ⟨1400920, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1400863, by decide⟩,⟨1400896, by decide⟩,⟨1400919, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101960_1400920 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101960 ⟨1400920, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101960
    ⟨1400920, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1400863, by decide⟩,⟨1400896, by decide⟩,⟨1400919, by decide⟩]) unmarked_context_11_101960_1400920 node_context_11_101960_1400920
  intro a
  fin_cases a
  · exact context_12_407840_1108174
  · exact context_12_407841_1400863
  · exact context_12_407842_1400896
  · exact context_12_407843_1400919

theorem selected_cut_49500 : selected 10 ⟨1400982, by decide⟩
    (prefixPartial 11 101961) = some ⟨11, 2, 0, 1400982, 101961, 3349, 262144⟩ := by
  decide +kernel

theorem context_11_101961_1400982 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101961 ⟨1400982, by decide⟩ :=
  accepted_of_selected 11 101961 ⟨1400982, by decide⟩ ⟨11, 2, 0, 1400982, 101961, 3349, 262144⟩
    (by decide) selected_cut_49500

theorem selected_cut_49501 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 101962) = some ⟨11, 1, 0, 900587, 101962, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101962_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101962 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 101962 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 101962, 1, 262144⟩
    (by decide) selected_cut_49501

theorem selected_cut_49502 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407852) = some ⟨12, 1, 0, 1108174, 407852, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407852_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407852 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407852 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407852, 1, 65536⟩
    (by decide) selected_cut_49502

theorem selected_cut_49503 : selected 9 ⟨1401014, by decide⟩
    (prefixPartial 12 407853) = some ⟨12, 2, 0, 1401014, 407853, 1541, 65536⟩ := by
  decide +kernel

theorem context_12_407853_1401014 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407853 ⟨1401014, by decide⟩ :=
  accepted_of_selected 12 407853 ⟨1401014, by decide⟩ ⟨12, 2, 0, 1401014, 407853, 1541, 65536⟩
    (by decide) selected_cut_49503

theorem selected_cut_49504 : selected 9 ⟨1401042, by decide⟩
    (prefixPartial 12 407854) = some ⟨12, 2, 0, 1401042, 407854, 1673, 65536⟩ := by
  decide +kernel

theorem context_12_407854_1401042 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407854 ⟨1401042, by decide⟩ :=
  accepted_of_selected 12 407854 ⟨1401042, by decide⟩ ⟨12, 2, 0, 1401042, 407854, 1673, 65536⟩
    (by decide) selected_cut_49504

theorem selected_cut_49505 : selected 9 ⟨1401065, by decide⟩
    (prefixPartial 12 407855) = some ⟨12, 2, 0, 1401065, 407855, 1453, 65536⟩ := by
  decide +kernel

theorem context_12_407855_1401065 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407855 ⟨1401065, by decide⟩ :=
  accepted_of_selected 12 407855 ⟨1401065, by decide⟩ ⟨12, 2, 0, 1401065, 407855, 1453, 65536⟩
    (by decide) selected_cut_49505

theorem unmarked_context_11_101963_1401066 : frontier 10 ⟨1401066, by decide⟩
    (prefixCache 11 101963) (prefixPartial 11 101963) = false := by
  decide +kernel

theorem node_context_11_101963_1401066 : EJMOriginalGlobalDAGData.nodes 10 ⟨1401066, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1401014, by decide⟩,⟨1401042, by decide⟩,⟨1401065, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101963_1401066 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101963 ⟨1401066, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101963
    ⟨1401066, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1401014, by decide⟩,⟨1401042, by decide⟩,⟨1401065, by decide⟩]) unmarked_context_11_101963_1401066 node_context_11_101963_1401066
  intro a
  fin_cases a
  · exact context_12_407852_1108174
  · exact context_12_407853_1401014
  · exact context_12_407854_1401042
  · exact context_12_407855_1401065

theorem unmarked_context_10_25490_1401067 : frontier 11 ⟨1401067, by decide⟩
    (prefixCache 10 25490) (prefixPartial 10 25490) = false := by
  decide +kernel

theorem node_context_10_25490_1401067 : EJMOriginalGlobalDAGData.nodes 11 ⟨1401067, by decide⟩ =
    .split (coordinate 10) (![⟨1400920, by decide⟩,⟨1400982, by decide⟩,⟨900587, by decide⟩,⟨1401066, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25490_1401067 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25490 ⟨1401067, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25490
    ⟨1401067, by decide⟩ (by decide) (![⟨1400920, by decide⟩,⟨1400982, by decide⟩,⟨900587, by decide⟩,⟨1401066, by decide⟩]) unmarked_context_10_25490_1401067 node_context_10_25490_1401067
  intro a
  fin_cases a
  · exact context_11_101960_1400920
  · exact context_11_101961_1400982
  · exact context_11_101962_900587
  · exact context_11_101963_1401066

theorem selected_cut_49506 : selected 9 ⟨1108174, by decide⟩
    (prefixPartial 12 407856) = some ⟨12, 1, 0, 1108174, 407856, 1, 65536⟩ := by
  decide +kernel

theorem context_12_407856_1108174 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407856 ⟨1108174, by decide⟩ :=
  accepted_of_selected 12 407856 ⟨1108174, by decide⟩ ⟨12, 1, 0, 1108174, 407856, 1, 65536⟩
    (by decide) selected_cut_49506

theorem selected_cut_49507 : selected 9 ⟨1401112, by decide⟩
    (prefixPartial 12 407857) = some ⟨12, 2, 0, 1401112, 407857, 1741, 65536⟩ := by
  decide +kernel

theorem context_12_407857_1401112 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407857 ⟨1401112, by decide⟩ :=
  accepted_of_selected 12 407857 ⟨1401112, by decide⟩ ⟨12, 2, 0, 1401112, 407857, 1741, 65536⟩
    (by decide) selected_cut_49507

theorem selected_cut_49508 : selected 9 ⟨1401142, by decide⟩
    (prefixPartial 12 407858) = some ⟨12, 2, 0, 1401142, 407858, 1621, 65536⟩ := by
  decide +kernel

theorem context_12_407858_1401142 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407858 ⟨1401142, by decide⟩ :=
  accepted_of_selected 12 407858 ⟨1401142, by decide⟩ ⟨12, 2, 0, 1401142, 407858, 1621, 65536⟩
    (by decide) selected_cut_49508

theorem selected_cut_49509 : selected 9 ⟨1401175, by decide⟩
    (prefixPartial 12 407859) = some ⟨12, 2, 0, 1401175, 407859, 1601, 65536⟩ := by
  decide +kernel

theorem context_12_407859_1401175 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 12 407859 ⟨1401175, by decide⟩ :=
  accepted_of_selected 12 407859 ⟨1401175, by decide⟩ ⟨12, 2, 0, 1401175, 407859, 1601, 65536⟩
    (by decide) selected_cut_49509

theorem unmarked_context_11_101964_1401176 : frontier 10 ⟨1401176, by decide⟩
    (prefixCache 11 101964) (prefixPartial 11 101964) = false := by
  decide +kernel

theorem node_context_11_101964_1401176 : EJMOriginalGlobalDAGData.nodes 10 ⟨1401176, by decide⟩ =
    .split (coordinate 11) (![⟨1108174, by decide⟩,⟨1401112, by decide⟩,⟨1401142, by decide⟩,⟨1401175, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_11_101964_1401176 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101964 ⟨1401176, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 11 101964
    ⟨1401176, by decide⟩ (by decide) (![⟨1108174, by decide⟩,⟨1401112, by decide⟩,⟨1401142, by decide⟩,⟨1401175, by decide⟩]) unmarked_context_11_101964_1401176 node_context_11_101964_1401176
  intro a
  fin_cases a
  · exact context_12_407856_1108174
  · exact context_12_407857_1401112
  · exact context_12_407858_1401142
  · exact context_12_407859_1401175

theorem selected_cut_49510 : selected 10 ⟨1401239, by decide⟩
    (prefixPartial 11 101965) = some ⟨11, 2, 0, 1401239, 101965, 3097, 262144⟩ := by
  decide +kernel

theorem context_11_101965_1401239 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101965 ⟨1401239, by decide⟩ :=
  accepted_of_selected 11 101965 ⟨1401239, by decide⟩ ⟨11, 2, 0, 1401239, 101965, 3097, 262144⟩
    (by decide) selected_cut_49510

theorem selected_cut_49511 : selected 10 ⟨1401313, by decide⟩
    (prefixPartial 11 101966) = some ⟨11, 2, 0, 1401313, 101966, 3745, 262144⟩ := by
  decide +kernel

theorem context_11_101966_1401313 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101966 ⟨1401313, by decide⟩ :=
  accepted_of_selected 11 101966 ⟨1401313, by decide⟩ ⟨11, 2, 0, 1401313, 101966, 3745, 262144⟩
    (by decide) selected_cut_49511

theorem selected_cut_49512 : selected 10 ⟨1401345, by decide⟩
    (prefixPartial 11 101967) = some ⟨11, 2, 0, 1401345, 101967, 1361, 262144⟩ := by
  decide +kernel

theorem context_11_101967_1401345 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101967 ⟨1401345, by decide⟩ :=
  accepted_of_selected 11 101967 ⟨1401345, by decide⟩ ⟨11, 2, 0, 1401345, 101967, 1361, 262144⟩
    (by decide) selected_cut_49512

theorem unmarked_context_10_25491_1401346 : frontier 11 ⟨1401346, by decide⟩
    (prefixCache 10 25491) (prefixPartial 10 25491) = false := by
  decide +kernel

theorem node_context_10_25491_1401346 : EJMOriginalGlobalDAGData.nodes 11 ⟨1401346, by decide⟩ =
    .split (coordinate 10) (![⟨1401176, by decide⟩,⟨1401239, by decide⟩,⟨1401313, by decide⟩,⟨1401345, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25491_1401346 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25491 ⟨1401346, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25491
    ⟨1401346, by decide⟩ (by decide) (![⟨1401176, by decide⟩,⟨1401239, by decide⟩,⟨1401313, by decide⟩,⟨1401345, by decide⟩]) unmarked_context_10_25491_1401346 node_context_10_25491_1401346
  intro a
  fin_cases a
  · exact context_11_101964_1401176
  · exact context_11_101965_1401239
  · exact context_11_101966_1401313
  · exact context_11_101967_1401345

theorem unmarked_context_9_6372_1401347 : frontier 12 ⟨1401347, by decide⟩
    (prefixCache 9 6372) (prefixPartial 9 6372) = false := by
  decide +kernel

theorem node_context_9_6372_1401347 : EJMOriginalGlobalDAGData.nodes 12 ⟨1401347, by decide⟩ =
    .split (coordinate 9) (![⟨1400531, by decide⟩,⟨1400827, by decide⟩,⟨1401067, by decide⟩,⟨1401346, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6372_1401347 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6372 ⟨1401347, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6372
    ⟨1401347, by decide⟩ (by decide) (![⟨1400531, by decide⟩,⟨1400827, by decide⟩,⟨1401067, by decide⟩,⟨1401346, by decide⟩]) unmarked_context_9_6372_1401347 node_context_9_6372_1401347
  intro a
  fin_cases a
  · exact context_10_25488_1400531
  · exact context_10_25489_1400827
  · exact context_10_25490_1401067
  · exact context_10_25491_1401346

theorem selected_cut_49513 : selected 10 ⟨1401379, by decide⟩
    (prefixPartial 11 101968) = some ⟨11, 2, 0, 1401379, 101968, 1497, 262144⟩ := by
  decide +kernel

theorem context_11_101968_1401379 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101968 ⟨1401379, by decide⟩ :=
  accepted_of_selected 11 101968 ⟨1401379, by decide⟩ ⟨11, 2, 0, 1401379, 101968, 1497, 262144⟩
    (by decide) selected_cut_49513

theorem selected_cut_49514 : selected 10 ⟨1401467, by decide⟩
    (prefixPartial 11 101969) = some ⟨11, 2, 0, 1401467, 101969, 3925, 262144⟩ := by
  decide +kernel

theorem context_11_101969_1401467 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101969 ⟨1401467, by decide⟩ :=
  accepted_of_selected 11 101969 ⟨1401467, by decide⟩ ⟨11, 2, 0, 1401467, 101969, 3925, 262144⟩
    (by decide) selected_cut_49514

theorem selected_cut_49515 : selected 10 ⟨1401501, by decide⟩
    (prefixPartial 11 101970) = some ⟨11, 2, 0, 1401501, 101970, 2173, 262144⟩ := by
  decide +kernel

theorem context_11_101970_1401501 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101970 ⟨1401501, by decide⟩ :=
  accepted_of_selected 11 101970 ⟨1401501, by decide⟩ ⟨11, 2, 0, 1401501, 101970, 2173, 262144⟩
    (by decide) selected_cut_49515

theorem selected_cut_49516 : selected 10 ⟨1401562, by decide⟩
    (prefixPartial 11 101971) = some ⟨11, 2, 0, 1401562, 101971, 2577, 262144⟩ := by
  decide +kernel

theorem context_11_101971_1401562 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101971 ⟨1401562, by decide⟩ :=
  accepted_of_selected 11 101971 ⟨1401562, by decide⟩ ⟨11, 2, 0, 1401562, 101971, 2577, 262144⟩
    (by decide) selected_cut_49516

theorem unmarked_context_10_25492_1401563 : frontier 11 ⟨1401563, by decide⟩
    (prefixCache 10 25492) (prefixPartial 10 25492) = false := by
  decide +kernel

theorem node_context_10_25492_1401563 : EJMOriginalGlobalDAGData.nodes 11 ⟨1401563, by decide⟩ =
    .split (coordinate 10) (![⟨1401379, by decide⟩,⟨1401467, by decide⟩,⟨1401501, by decide⟩,⟨1401562, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25492_1401563 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25492 ⟨1401563, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25492
    ⟨1401563, by decide⟩ (by decide) (![⟨1401379, by decide⟩,⟨1401467, by decide⟩,⟨1401501, by decide⟩,⟨1401562, by decide⟩]) unmarked_context_10_25492_1401563 node_context_10_25492_1401563
  intro a
  fin_cases a
  · exact context_11_101968_1401379
  · exact context_11_101969_1401467
  · exact context_11_101970_1401501
  · exact context_11_101971_1401562

theorem selected_cut_49517 : selected 11 ⟨893098, by decide⟩
    (prefixPartial 10 25493) = some ⟨10, 1, 0, 893098, 25493, 1, 1048576⟩ := by
  decide +kernel

theorem context_10_25493_893098 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25493 ⟨893098, by decide⟩ :=
  accepted_of_selected 10 25493 ⟨893098, by decide⟩ ⟨10, 1, 0, 893098, 25493, 1, 1048576⟩
    (by decide) selected_cut_49517

theorem selected_cut_49518 : selected 10 ⟨1401624, by decide⟩
    (prefixPartial 11 101976) = some ⟨11, 2, 0, 1401624, 101976, 2569, 262144⟩ := by
  decide +kernel

theorem context_11_101976_1401624 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101976 ⟨1401624, by decide⟩ :=
  accepted_of_selected 11 101976 ⟨1401624, by decide⟩ ⟨11, 2, 0, 1401624, 101976, 2569, 262144⟩
    (by decide) selected_cut_49518

theorem selected_cut_49519 : selected 10 ⟨1401690, by decide⟩
    (prefixPartial 11 101977) = some ⟨11, 2, 0, 1401690, 101977, 3233, 262144⟩ := by
  decide +kernel

theorem context_11_101977_1401690 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101977 ⟨1401690, by decide⟩ :=
  accepted_of_selected 11 101977 ⟨1401690, by decide⟩ ⟨11, 2, 0, 1401690, 101977, 3233, 262144⟩
    (by decide) selected_cut_49519

theorem selected_cut_49520 : selected 10 ⟨900587, by decide⟩
    (prefixPartial 11 101978) = some ⟨11, 1, 0, 900587, 101978, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101978_900587 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101978 ⟨900587, by decide⟩ :=
  accepted_of_selected 11 101978 ⟨900587, by decide⟩ ⟨11, 1, 0, 900587, 101978, 1, 262144⟩
    (by decide) selected_cut_49520

theorem selected_cut_49521 : selected 10 ⟨1401721, by decide⟩
    (prefixPartial 11 101979) = some ⟨11, 2, 0, 1401721, 101979, 2057, 262144⟩ := by
  decide +kernel

theorem context_11_101979_1401721 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101979 ⟨1401721, by decide⟩ :=
  accepted_of_selected 11 101979 ⟨1401721, by decide⟩ ⟨11, 2, 0, 1401721, 101979, 2057, 262144⟩
    (by decide) selected_cut_49521

theorem unmarked_context_10_25494_1401722 : frontier 11 ⟨1401722, by decide⟩
    (prefixCache 10 25494) (prefixPartial 10 25494) = false := by
  decide +kernel

theorem node_context_10_25494_1401722 : EJMOriginalGlobalDAGData.nodes 11 ⟨1401722, by decide⟩ =
    .split (coordinate 10) (![⟨1401624, by decide⟩,⟨1401690, by decide⟩,⟨900587, by decide⟩,⟨1401721, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25494_1401722 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25494 ⟨1401722, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25494
    ⟨1401722, by decide⟩ (by decide) (![⟨1401624, by decide⟩,⟨1401690, by decide⟩,⟨900587, by decide⟩,⟨1401721, by decide⟩]) unmarked_context_10_25494_1401722 node_context_10_25494_1401722
  intro a
  fin_cases a
  · exact context_11_101976_1401624
  · exact context_11_101977_1401690
  · exact context_11_101978_900587
  · exact context_11_101979_1401721

theorem selected_cut_49522 : selected 10 ⟨1401780, by decide⟩
    (prefixPartial 11 101980) = some ⟨11, 2, 0, 1401780, 101980, 2333, 262144⟩ := by
  decide +kernel

theorem context_11_101980_1401780 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101980 ⟨1401780, by decide⟩ :=
  accepted_of_selected 11 101980 ⟨1401780, by decide⟩ ⟨11, 2, 0, 1401780, 101980, 2333, 262144⟩
    (by decide) selected_cut_49522

theorem selected_cut_49523 : selected 10 ⟨1401836, by decide⟩
    (prefixPartial 11 101981) = some ⟨11, 2, 0, 1401836, 101981, 2857, 262144⟩ := by
  decide +kernel

theorem context_11_101981_1401836 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101981 ⟨1401836, by decide⟩ :=
  accepted_of_selected 11 101981 ⟨1401836, by decide⟩ ⟨11, 2, 0, 1401836, 101981, 2857, 262144⟩
    (by decide) selected_cut_49523

theorem selected_cut_49524 : selected 10 ⟨1401865, by decide⟩
    (prefixPartial 11 101982) = some ⟨11, 2, 0, 1401865, 101982, 1589, 262144⟩ := by
  decide +kernel

theorem context_11_101982_1401865 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101982 ⟨1401865, by decide⟩ :=
  accepted_of_selected 11 101982 ⟨1401865, by decide⟩ ⟨11, 2, 0, 1401865, 101982, 1589, 262144⟩
    (by decide) selected_cut_49524

theorem selected_cut_49525 : selected 10 ⟨1401875, by decide⟩
    (prefixPartial 11 101983) = some ⟨11, 2, 0, 1401875, 101983, 753, 262144⟩ := by
  decide +kernel

theorem context_11_101983_1401875 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101983 ⟨1401875, by decide⟩ :=
  accepted_of_selected 11 101983 ⟨1401875, by decide⟩ ⟨11, 2, 0, 1401875, 101983, 753, 262144⟩
    (by decide) selected_cut_49525

theorem unmarked_context_10_25495_1401876 : frontier 11 ⟨1401876, by decide⟩
    (prefixCache 10 25495) (prefixPartial 10 25495) = false := by
  decide +kernel

theorem node_context_10_25495_1401876 : EJMOriginalGlobalDAGData.nodes 11 ⟨1401876, by decide⟩ =
    .split (coordinate 10) (![⟨1401780, by decide⟩,⟨1401836, by decide⟩,⟨1401865, by decide⟩,⟨1401875, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25495_1401876 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25495 ⟨1401876, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25495
    ⟨1401876, by decide⟩ (by decide) (![⟨1401780, by decide⟩,⟨1401836, by decide⟩,⟨1401865, by decide⟩,⟨1401875, by decide⟩]) unmarked_context_10_25495_1401876 node_context_10_25495_1401876
  intro a
  fin_cases a
  · exact context_11_101980_1401780
  · exact context_11_101981_1401836
  · exact context_11_101982_1401865
  · exact context_11_101983_1401875

theorem unmarked_context_9_6373_1401877 : frontier 12 ⟨1401877, by decide⟩
    (prefixCache 9 6373) (prefixPartial 9 6373) = false := by
  decide +kernel

theorem node_context_9_6373_1401877 : EJMOriginalGlobalDAGData.nodes 12 ⟨1401877, by decide⟩ =
    .split (coordinate 9) (![⟨1401563, by decide⟩,⟨893098, by decide⟩,⟨1401722, by decide⟩,⟨1401876, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6373_1401877 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6373 ⟨1401877, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6373
    ⟨1401877, by decide⟩ (by decide) (![⟨1401563, by decide⟩,⟨893098, by decide⟩,⟨1401722, by decide⟩,⟨1401876, by decide⟩]) unmarked_context_9_6373_1401877 node_context_9_6373_1401877
  intro a
  fin_cases a
  · exact context_10_25492_1401563
  · exact context_10_25493_893098
  · exact context_10_25494_1401722
  · exact context_10_25495_1401876

theorem selected_cut_49526 : selected 10 ⟨1375697, by decide⟩
    (prefixPartial 11 101984) = some ⟨11, 1, 0, 1375697, 101984, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101984_1375697 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101984 ⟨1375697, by decide⟩ :=
  accepted_of_selected 11 101984 ⟨1375697, by decide⟩ ⟨11, 1, 0, 1375697, 101984, 1, 262144⟩
    (by decide) selected_cut_49526

theorem selected_cut_49527 : selected 10 ⟨1401918, by decide⟩
    (prefixPartial 11 101985) = some ⟨11, 2, 0, 1401918, 101985, 1753, 262144⟩ := by
  decide +kernel

theorem context_11_101985_1401918 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101985 ⟨1401918, by decide⟩ :=
  accepted_of_selected 11 101985 ⟨1401918, by decide⟩ ⟨11, 2, 0, 1401918, 101985, 1753, 262144⟩
    (by decide) selected_cut_49527

theorem selected_cut_49528 : selected 10 ⟨1401961, by decide⟩
    (prefixPartial 11 101986) = some ⟨11, 2, 0, 1401961, 101986, 2285, 262144⟩ := by
  decide +kernel

theorem context_11_101986_1401961 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101986 ⟨1401961, by decide⟩ :=
  accepted_of_selected 11 101986 ⟨1401961, by decide⟩ ⟨11, 2, 0, 1401961, 101986, 2285, 262144⟩
    (by decide) selected_cut_49528

theorem selected_cut_49529 : selected 10 ⟨1402012, by decide⟩
    (prefixPartial 11 101987) = some ⟨11, 2, 0, 1402012, 101987, 2433, 262144⟩ := by
  decide +kernel

theorem context_11_101987_1402012 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101987 ⟨1402012, by decide⟩ :=
  accepted_of_selected 11 101987 ⟨1402012, by decide⟩ ⟨11, 2, 0, 1402012, 101987, 2433, 262144⟩
    (by decide) selected_cut_49529

theorem unmarked_context_10_25496_1402013 : frontier 11 ⟨1402013, by decide⟩
    (prefixCache 10 25496) (prefixPartial 10 25496) = false := by
  decide +kernel

theorem node_context_10_25496_1402013 : EJMOriginalGlobalDAGData.nodes 11 ⟨1402013, by decide⟩ =
    .split (coordinate 10) (![⟨1375697, by decide⟩,⟨1401918, by decide⟩,⟨1401961, by decide⟩,⟨1402012, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25496_1402013 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25496 ⟨1402013, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25496
    ⟨1402013, by decide⟩ (by decide) (![⟨1375697, by decide⟩,⟨1401918, by decide⟩,⟨1401961, by decide⟩,⟨1402012, by decide⟩]) unmarked_context_10_25496_1402013 node_context_10_25496_1402013
  intro a
  fin_cases a
  · exact context_11_101984_1375697
  · exact context_11_101985_1401918
  · exact context_11_101986_1401961
  · exact context_11_101987_1402012

theorem selected_cut_49530 : selected 10 ⟨1402052, by decide⟩
    (prefixPartial 11 101988) = some ⟨11, 2, 0, 1402052, 101988, 1609, 262144⟩ := by
  decide +kernel

theorem context_11_101988_1402052 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101988 ⟨1402052, by decide⟩ :=
  accepted_of_selected 11 101988 ⟨1402052, by decide⟩ ⟨11, 2, 0, 1402052, 101988, 1609, 262144⟩
    (by decide) selected_cut_49530

theorem selected_cut_49531 : selected 10 ⟨1378525, by decide⟩
    (prefixPartial 11 101989) = some ⟨11, 1, 0, 1378525, 101989, 1, 262144⟩ := by
  decide +kernel

theorem context_11_101989_1378525 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101989 ⟨1378525, by decide⟩ :=
  accepted_of_selected 11 101989 ⟨1378525, by decide⟩ ⟨11, 1, 0, 1378525, 101989, 1, 262144⟩
    (by decide) selected_cut_49531

theorem selected_cut_49532 : selected 10 ⟨1402090, by decide⟩
    (prefixPartial 11 101990) = some ⟨11, 2, 0, 1402090, 101990, 1809, 262144⟩ := by
  decide +kernel

theorem context_11_101990_1402090 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101990 ⟨1402090, by decide⟩ :=
  accepted_of_selected 11 101990 ⟨1402090, by decide⟩ ⟨11, 2, 0, 1402090, 101990, 1809, 262144⟩
    (by decide) selected_cut_49532

theorem selected_cut_49533 : selected 10 ⟨1402123, by decide⟩
    (prefixPartial 11 101991) = some ⟨11, 2, 0, 1402123, 101991, 1685, 262144⟩ := by
  decide +kernel

theorem context_11_101991_1402123 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 11 101991 ⟨1402123, by decide⟩ :=
  accepted_of_selected 11 101991 ⟨1402123, by decide⟩ ⟨11, 2, 0, 1402123, 101991, 1685, 262144⟩
    (by decide) selected_cut_49533

theorem unmarked_context_10_25497_1402124 : frontier 11 ⟨1402124, by decide⟩
    (prefixCache 10 25497) (prefixPartial 10 25497) = false := by
  decide +kernel

theorem node_context_10_25497_1402124 : EJMOriginalGlobalDAGData.nodes 11 ⟨1402124, by decide⟩ =
    .split (coordinate 10) (![⟨1402052, by decide⟩,⟨1378525, by decide⟩,⟨1402090, by decide⟩,⟨1402123, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_10_25497_1402124 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25497 ⟨1402124, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 10 25497
    ⟨1402124, by decide⟩ (by decide) (![⟨1402052, by decide⟩,⟨1378525, by decide⟩,⟨1402090, by decide⟩,⟨1402123, by decide⟩]) unmarked_context_10_25497_1402124 node_context_10_25497_1402124
  intro a
  fin_cases a
  · exact context_11_101988_1402052
  · exact context_11_101989_1378525
  · exact context_11_101990_1402090
  · exact context_11_101991_1402123

theorem selected_cut_49534 : selected 11 ⟨1402148, by decide⟩
    (prefixPartial 10 25498) = some ⟨10, 2, 0, 1402148, 25498, 625, 1048576⟩ := by
  decide +kernel

theorem context_10_25498_1402148 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25498 ⟨1402148, by decide⟩ :=
  accepted_of_selected 10 25498 ⟨1402148, by decide⟩ ⟨10, 2, 0, 1402148, 25498, 625, 1048576⟩
    (by decide) selected_cut_49534

theorem selected_cut_49535 : selected 11 ⟨1402222, by decide⟩
    (prefixPartial 10 25499) = some ⟨10, 2, 0, 1402222, 25499, 3341, 1048576⟩ := by
  decide +kernel

theorem context_10_25499_1402222 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25499 ⟨1402222, by decide⟩ :=
  accepted_of_selected 10 25499 ⟨1402222, by decide⟩ ⟨10, 2, 0, 1402222, 25499, 3341, 1048576⟩
    (by decide) selected_cut_49535

theorem unmarked_context_9_6374_1402223 : frontier 12 ⟨1402223, by decide⟩
    (prefixCache 9 6374) (prefixPartial 9 6374) = false := by
  decide +kernel

theorem node_context_9_6374_1402223 : EJMOriginalGlobalDAGData.nodes 12 ⟨1402223, by decide⟩ =
    .split (coordinate 9) (![⟨1402013, by decide⟩,⟨1402124, by decide⟩,⟨1402148, by decide⟩,⟨1402222, by decide⟩]) := by
  apply FiniteCachedSymmetryDAGReplay.checked_split_node
  decide +kernel

theorem context_9_6374_1402223 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 9 6374 ⟨1402223, by decide⟩ := by
  apply TransientEJMOriginalAdaptiveFrontierBridge.assemble frontier 9 6374
    ⟨1402223, by decide⟩ (by decide) (![⟨1402013, by decide⟩,⟨1402124, by decide⟩,⟨1402148, by decide⟩,⟨1402222, by decide⟩]) unmarked_context_9_6374_1402223 node_context_9_6374_1402223
  intro a
  fin_cases a
  · exact context_10_25496_1402013
  · exact context_10_25497_1402124
  · exact context_10_25498_1402148
  · exact context_10_25499_1402222

theorem selected_cut_49536 : selected 11 ⟨1402288, by decide⟩
    (prefixPartial 10 25500) = some ⟨10, 2, 0, 1402288, 25500, 2881, 1048576⟩ := by
  decide +kernel

theorem context_10_25500_1402288 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25500 ⟨1402288, by decide⟩ :=
  accepted_of_selected 10 25500 ⟨1402288, by decide⟩ ⟨10, 2, 0, 1402288, 25500, 2881, 1048576⟩
    (by decide) selected_cut_49536

theorem selected_cut_49537 : selected 11 ⟨1402333, by decide⟩
    (prefixPartial 10 25501) = some ⟨10, 2, 0, 1402333, 25501, 1801, 1048576⟩ := by
  decide +kernel

theorem context_10_25501_1402333 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25501 ⟨1402333, by decide⟩ :=
  accepted_of_selected 10 25501 ⟨1402333, by decide⟩ ⟨10, 2, 0, 1402333, 25501, 1801, 1048576⟩
    (by decide) selected_cut_49537

theorem selected_cut_49538 : selected 11 ⟨1402365, by decide⟩
    (prefixPartial 10 25502) = some ⟨10, 2, 0, 1402365, 25502, 993, 1048576⟩ := by
  decide +kernel

theorem context_10_25502_1402365 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25502 ⟨1402365, by decide⟩ :=
  accepted_of_selected 10 25502 ⟨1402365, by decide⟩ ⟨10, 2, 0, 1402365, 25502, 993, 1048576⟩
    (by decide) selected_cut_49538

theorem selected_cut_49539 : selected 11 ⟨1402374, by decide⟩
    (prefixPartial 10 25503) = some ⟨10, 2, 0, 1402374, 25503, 73, 1048576⟩ := by
  decide +kernel

theorem context_10_25503_1402374 : TransientEJMOriginalAdaptiveFrontierBridge.Accepted
    frontier 10 25503 ⟨1402374, by decide⟩ :=
  accepted_of_selected 10 25503 ⟨1402374, by decide⟩ ⟨10, 2, 0, 1402374, 25503, 73, 1048576⟩
    (by decide) selected_cut_49539

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
